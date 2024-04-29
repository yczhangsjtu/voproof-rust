from sympy import Symbol, latex, sympify, Integer, Expr,\
    simplify, Max, Add, Mul, Pow, srepr
from .rust_sympy import rust_code, rust_code_to_field, force_lowercase


sym_i = Symbol("i")


def keep_alpha_number(s):
  return "".join([c for c in s if c.isalnum()])


def rust(expr, to_field=False):
  if isinstance(expr, str):
    return expr
  if hasattr(expr, "dumpr"):
    return expr.dumpr()
  if isinstance(expr, Expr):
    return rust_code(expr) if not to_field else rust_code_to_field(expr)
  return str(expr)


def to_field(expr):
  if isinstance(expr, Integer) or isinstance(expr, int):
    if expr == 0:
      return rust(rust_zero())
    if expr == 1:
      return rust(rust_one())
    if expr == -1:
      return "-%s" % rust(rust_one())
    if expr > 0:
      return rust(rust_to_field(expr))
    return "-%s" % rust(rust_to_field(-expr))
  return rust(expr)


class RustArg(object):
  def __init__(self, name, is_ref=False, is_mutable=False):
    self.name = name
    self.is_ref = is_ref
    self.is_mutable = is_mutable

  def dumpr(self):
    if not self.is_ref:
      return dumpr(self.name)
    if self.is_mutable:
      return "&mut %s" % dumpr(self.name)
    return "&%s" % dumpr(self.name)


def ref(name):
  return RustArg(name, is_ref=True)


def mut(name):
  return RustArg(name, is_ref=True, is_mutable=True)


class RustList(object):
  def __init__(self):
    self.items = []
    self.expand_lines = False

  def append(self, item):
    if isinstance(item, list):
      self.items += item
    else:
      self.items.append(item)
    return self

  def __len__(self):
    return len(self.items)

  def __getitem__(self, index):
    return self.items[index]

  def dumpr(self):
    if self.expand_lines and len(self.items) > 0:
      return "\n          " + ",\n          ".join([rust(item) for item in self.items])
    else:
      return ", ".join([rust(item) for item in self.items])


class FunctionCall(RustList):
  def __init__(self, func_name):
    super(FunctionCall, self).__init__()
    self.func_name = func_name
    self.expand_lines = True

  def dumpr(self):
    return "%s(%s)" % (self.func_name, super(FunctionCall, self).dumpr())


class RustMacro(FunctionCall):
  def __init__(self, macro_name, *args):
    super(RustMacro, self).__init__("%s!" % macro_name)
    self.macro_name = macro_name
    if (isinstance(args, list) or isinstance(args, tuple)) and len(args) > 0:
      for arg in args:
        self.append(arg)


class Tuple(RustList):
  def __init__(self):
    super(Tuple, self).__init__()

  def dumpr(self):
    return "(%s)" % super(Tuple, self).dumpr()


class RustBuilder(object):
  def __init__(self, *args):
    self.items = list(args)
    self.stack = []

  def append(self, right):
    if isinstance(right, list):
      self.items += right
    elif isinstance(right, RustBuilder):
      self.items += right.items
    else:
      self.items.append(right)
    return self

  def append_to_last(self, right):
    if hasattr(self.items[-1], 'append'):
      self.items[-1].append(right)
    return self
    raise Exception("Cannot append to last element of type %s"
                    % type(self.items[-1]))

  def let(self, right=None):
    self.append("let")
    if right is not None:
      self.space(right)
    return self

  def letmut(self, right=None):
    self.append("let mut")
    if right is not None:
      self.space(right)
    return self

  def func(self, right):
    if isinstance(right, str):
      return self.append(FunctionCall(right))
    elif isinstance(right, FunctionCall):
      return self.append(right)
    raise Exception("Cannot call type %s" % type(right))

  def invoke_method(self, right):
    self.append(".")
    if isinstance(right, str):
      return self.append(FunctionCall(right))
    elif isinstance(right, FunctionCall):
      return self.append(right)
    raise Exception("Cannot call type %s" % type(right))

  def attribute(self, right):
    self.append(".")
    if right is not None:
      self.append(right)
    return self

  def assign_func(self, right):
    return self.assign().func(right)

  def space(self, right=None):
    self.append(" ")
    if right is not None:
      self.append(right)
    return self

  def space_around(self):
    self.append(" ")
    self.append(right)
    self.append(" ")
    return self

  def comma(self, right=None):
    self.append(",")
    if right is not None:
      self.append(right)
    return self

  def plus(self, right=None):
    self.append("+")
    if right is not None:
      self.append(right)
    return self

  def plus_assign(self, right=None):
    self.append("+=")
    if right is not None:
      self.append(right)
    return self

  def minus(self, right=None, align=False):
    self.append("-")
    if right is not None:
      self.append(right)
    return self

  def mul(self, right=None):
    self.append("*")
    if right is not None:
      self.append(right)
    return self

  def slash(self, right=None):
    self.append("/")
    if right is not None:
      self.append(right)
    return self

  def paren(self, right=None):
    self.append("\\left(")
    if right is not None:
      self.append(right)
    self.append("\\right)")
    return self

  def start_env(self, name, marker):
    self.append(marker)
    self.stack.append(name)
    return self

  def end_env(self, name, marker):
    if not self.stack[-1] == name:
      raise Exception("Cannot end %s. Last time is %s" %
                      (name, self.stack[-1]))
    self.stack.pop()
    self.append(marker)
    return self

  def start_paren(self):
    return self.start_env("paren", "(")

  def end_paren(self):
    return self.end_env("paren", ")")

  def assign(self, right=None):
    self.append("=")
    if right is not None:
      self.append(right)
    return self

  def eol(self):
    return self.append("\n" + " " * 12)

  def end(self):
    return self.append(";\n" + " " * 8)

  def dumpr(self):
    if len(self.stack) > 0:
      raise Exception("Stack is not empty")
    return "".join([rust(arg) for arg in self.items])


def rust_builder_macro(macro_name, *args):
  return RustBuilder().append(RustMacro(macro_name, *args))


class _ArgName(object):
  def __init__(self, argname):
    self.argname = argname


class _ArgProcess(object):
  def __init__(self, func, *argnames):
    self.argnames = argnames
    self.func = func


rust_macro_list = [
    ("one", None, (), ()),
    ("zero", None, (), ()),
    ("commit_scalar", None, ("c"), ("vk", _ArgName("c"))),
    ("expression_vector_to_vector", "expression_vector_to_vector_i", ("v", "expr"),
     (_ArgName("v"), sym_i, _ArgName("expr"))),
    ("assert_eq", None, ("a", "b"), ()),
    ("vector_index", None, ("v", "i"), ()),
    ("inverse", None, ("a"), ()),
    ("eval_vector_as_poly", None, ("v", "z"), ()),
    ("eval_vector_expression", "eval_vector_expression_i", ("z", "expr", "n"),
     (_ArgName("z"), sym_i, _ArgName("expr"), _ArgName("n"))),
    ("define_eval_vector_expression", "define_eval_vector_expression_i",
     ("name", "z", "expr", "n"),
     (_ArgName("name"), _ArgName("z"), sym_i, _ArgName("expr"), _ArgName("n"))),
    ("vector_concat", None, None, ()),
    ("vector_concat_skip", None, None, ()),
    ("concat_and_one", None, ("u", "v"), ()),
    ("define_concat_subvec", None, ("u", "a", "ai", "aj", "b", "bi", "bj"), ()),
    ("check_vector_eq", None, ("v", "expr", "info"),
     (_ArgName("v"), _ArgName("expr"), _ArgProcess(lambda info: '"%s"' % info, "info"))),
    ("check_expression_vector_eq", "check_expression_vector_eq_i", ("u", "v", "len", "info"),
     (sym_i, _ArgName("u"), _ArgName("v"), _ArgName("len"),
        _ArgProcess(lambda info: '"%s"' % info, "info"))),
    ("define_vec_mut", None, ("v", "expr"), ()),
    ("define_vec", None, ("v", "expr"), ()),
    ("define_mut", None, ("v", "expr"), ()),
    ("define", None, ("v", "expr"), ()),
    ("poly_from_vec", None, ("v"), ()),
    ("scalar_to_field", "to_field", ("c"), ()),
    ("vec", None, None, ()),
    ("vec", "vec_size", ("e", "length"),
     (_ArgProcess(lambda e, length:
                  "%s; (%s) as usize" % (rust(e), rust(length)),
                  "e", "length"), )),
    ("linear_combination", None, None, ()),
    ("linear_combination_base_zero", None, None, ()),
    ("power_linear_combination", None, None, ()),
    ("sum", None, None, ()),
    ("to_bytes", None, None, ()),
    ("define_sum", None, None, ()),
    ("expression_vector", "expression_vector_i", ("expr", "length"),
     (sym_i, _ArgName("expr"), _ArgName("length"))),
    ("add_vector_to_vector", None, ("u", "v"), ()),
    ("add_expression_vector_to_vector", "add_expression_vector_to_vector_i", ("v", "expr"),
     (_ArgName("v"), sym_i, _ArgName("expr"))),
    ("check_poly_eval", None, ("poly", "point", "value", "info"),
     (_ArgName("poly"), _ArgName("point"), _ArgName("value"),
      _ArgProcess(lambda info: '"%s"' % info, "info"))),
    ("fmt_ff_vector", None, ("v"), ()),
    ("define_generator", None, (), ("gamma", "E")),
    ("init_size", None, ("name", "attr"),
     (_ArgName("name"), _ArgName("attr"), "size")),
    ("sample_randomizers", None, (), ("rng", )),
    ("concat_matrix_vertically", None,
     ("result", "h", "arows", "brows", "crows",
      "acols", "bcols", "cols", "avals", "bvals", "cvals"), ()),
    ("concat_matrix_horizontally", None,
     ("result", "k", "arows", "brows", "crows",
      "acols", "bcols", "cols", "avals", "bvals", "cvals", "drows", "dvals"), ()),
    ("int_array_to_power_vector", None, ("v", "gamma"), ()),
    ("define_int_array_to_power_vector", None, ("name", "v", "gamma"), ()),
    ("define_clone_vector", None, ("name", "v"), ()),
    ("define_hadamard_vector", None, ("name", "u", "v"), ()),
    ("define_matrix_vectors", None, ("u", "w", "v", "M", "gamma"), ()),
    ("define_commit_vector", None, ("cm", "v", "deg"),
     (_ArgName("cm"), _ArgName("v"), "powers_of_g", _ArgName("deg"))),
    ("define_commit_vector", "define_commit_vector_with_pk", ("cm", "v", "deg"),
     (_ArgName("cm"), _ArgName("v"), "pk.powers", _ArgName("deg"))),
    ("commit_vector", None, ("v", "deg"),
     (_ArgName("v"), "powers_of_g", _ArgName("deg"))),
    ("commit_vector", "commit_vector_with_pk", ("v", "deg"),
     (_ArgName("v"), "pk.powers", _ArgName("deg"))),
    ("define_sparse_mvp_vector", None, ("name", "M", "v", "H", "K"), ()),
    ("define_sparse_mvp_concat_vector", None, ("name", "M", "v", "H", "K"), ()),
    ("define_left_sparse_mvp_vector", None, ("name", "M", "v", "H", "K"), ()),
    ("define_concat_vector", None, None, ()),
    ("define_concat_vector_skip", None, None, ()),
    ("define_sparse_vector", None, ("v", "indices", "vals", "n"), ()),
    ("define_sparse_zero_one_vector", None, ("v", "indices", "n"), ()),
    ("define_permutation_vector_from_wires", None, ("v", "index_pairs", "n"),
        (_ArgName("v"), "gamma", _ArgName("index_pairs"), _ArgName("n"))),
    ("sparse_mvp_vector", None, ("M", "v", "H", "K"), ()),
    ("zero_pad", None, ("v", "n"), ()),
    ("define_zero_pad_concat_vector", None, None, ()),
    ("redefine_zero_pad_concat_vector", None, None, ()),
    ("define_poly_from_vec", None, ("poly", "v"), ()),
    ("get_randomness_from_hash", None, None, ()),
    ("define_expression_vector", "define_expression_vector_i", ("name", "expr", "n"),
     (_ArgName("name"), sym_i, _ArgName("expr"), _ArgName("n"))),
    ("define_expression_vector_inverse", "define_expression_vector_inverse_i",
     ("name", "expr", "n"), (_ArgName("name"), sym_i, _ArgName("expr"), _ArgName("n"))),
    ("minus", None, ("u", "v"), ()),
    ("minus_i64", None, ("u", "v"), ()),
    ("minus_plus_one", None, ("u", "v"), ()),
    ("neg", None, ("u"), ()),
    ("mul", None, ("u", "v"), ()),
    ("define_concat_neg_vector", None, ("name", "u", "v"), ()),
    ("define_concat_uwinverse_vector", None,
     ("name", "v", "mu", "u", "nu", "w"), ()),
    ("define_uwinverse_vector", None,
     ("name", "mu", "u", "nu", "w"), ()),
    ("accumulate_vector_plus", None, ("v"), ()),
    ("accumulate_vector_mul", None, ("v"), ()),
    ("define_accumulate_vector_mul", None, ("name", "v", "n"), (
        _ArgName("name"), sym_i, _ArgName("v"), _ArgName("n"))),
    ("vector_poly_mul", None, ("u", "v", "omega"), (
        _ArgName("u"), _ArgName("v"), _ArgName("omega"),
        _ArgProcess(
            lambda vec: f"_{rust(vec)}_left_eval_dict".replace(".", "_"), "u"),
        _ArgProcess(
            lambda vec: f"_{rust(vec)}_right_eval_dict".replace(".", "_"), "v"),
    )),
    ("define_vector_poly_mul_no_dict", None, ("name", "u", "v", "omega"), ()),
    ("define_vector_poly_mul", None, ("name", "u", "v", "omega"), ()),
    ("define_shift_minus_one", None, ("name", "vec"), ()),
    ("define_vector_poly_mul_shift", None,
     ("name", "u", "v", "omega", "shiftname"), (
         _ArgName("name"), _ArgName("u"), _ArgName("v"),
         _ArgName("omega"), _ArgName("shiftname"),
         _ArgProcess(
             lambda vec: f"_{rust(vec)}_left_eval_dict".replace(".", "_"), "u"),
         _ArgProcess(
             lambda vec: f"_{rust(vec)}_right_eval_dict".replace(".", "_"), "v"),
     )),
    ("define_vector_reverse_omega_shift", None,
     ("name", "v", "omega", "shiftname"), ()),
    ("define_vector_power_mul", None, ("name", "v", "alpha", "n"), ()),
    ("define_power_power_mul", None, ("name", "alpha", "n", "beta", "m"), ()),
    ("define_commitment_linear_combination", None, None, ()),
    ("define_commitment_linear_combination_no_one", None, None, ()),
    ("add_to_first_item", None, ("v", "e"), ()),
    ("range_index", None, ("start", "end", "i"), ()),
    ("define_vector_domain_evaluations_dict", None, ("vec",),
        (_ArgProcess(lambda vec: f"_{rust(vec)}_left_eval_dict".replace(".", "_"), "vec"),
         _ArgProcess(lambda vec: f"_{rust(vec)}_right_eval_dict".replace(".", "_"), "vec"))),
]


def _rust_macro(name, argnames, outargs, *args):
  if argnames is None:
    return RustMacro(name, *args)

  if len(args) != len(argnames):
    raise Exception("Macro %s Expect %d arguments (%s), got %d" %
                    (name, len(argnames), ",".join(argnames), len(args)))

  if len(outargs) == 0:
    return RustMacro(name, *args)

  argdict = {name: value for name, value in zip(argnames, args)}

  macro = RustMacro(name)
  for e in outargs:
    if isinstance(e, _ArgName):
      macro.append(argdict[e.argname])
    elif isinstance(e, _ArgProcess):
      macro.append(e.func(*(argdict[argname] for argname in e.argnames)))
    else:
      macro.append(e)
  return macro


def _rust_builder_macro(name, argnames, outargs, *args):
  return RustBuilder(_rust_macro(name, argnames, outargs, *args))


current_module = __import__(__name__, fromlist=[None])
for macro_name, funcname, argnames, outargs in rust_macro_list:
  if funcname == None:
    funcname = macro_name
  setattr(
      current_module,
      "rust_%s" % funcname,
      (lambda macro_name, argnames, outargs:
       lambda *args:
          _rust_macro(macro_name, argnames, outargs, *args))(
          macro_name, argnames, outargs
      ))
  setattr(
      current_module,
      "rust_builder_%s" % funcname,
      (lambda macro_name, argnames, outargs:
       lambda *args:
          _rust_builder_macro(macro_name, argnames, outargs, *args))(
          macro_name, argnames, outargs
      ))
  setattr(
      current_module,
      "rust_line_%s" % funcname,
      (lambda macro_name, argnames, outargs:
       lambda *args:
          _rust_builder_macro(macro_name, argnames, outargs, *args).end())(
          macro_name, argnames, outargs
      ))


def register_rust_functions(self):
  for attr in dir(current_module):
    if attr.startswith("rust_line_"):
      f = getattr(current_module, attr)
      name = attr[len("rust_line_"):]
      setattr(self, "prover_rust_" + name,
              (lambda f: lambda *args: self.prover_computes_rust(f(*args)))(f))
      setattr(self, "verifier_rust_" + name,
              (lambda f: lambda *args: self.verifier_computes_rust(f(*args)))(f))
      setattr(self, "pp_rust_" + name,
              (lambda f: lambda *args: self.preprocess_rust(f(*args)))(f))
