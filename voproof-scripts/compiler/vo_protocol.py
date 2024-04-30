from .pc_protocol import PublicCoinProtocolExecution
from .symbol.util import simplify_max_with_hints
from .symbol.vector import NamedVector, VectorCombination, get_named_vector
from .symbol.coeff_manager import CoeffManager
from .symbol.names import reset_name_counters
from .builder.latex import tex, Itemize, add_paren_if_add, Math
from .builder.rust import *
from sympy import Integer, Max
from sympy.abc import X


class SubmitVectors(object):
  def __init__(self, submitter, vector, size, rust_size=None):
    rust_size = size if rust_size is None else rust_size
    self.submitter = submitter
    self.vectors = [(vector, size, rust_size)]

  def __len__(self):
    return len(self.vectors)

  def add_vector(self, vector, size, rust_size=None):
    rust_size = size if rust_size is None else rust_size
    self.vectors.append((vector, size, rust_size))

  def dumps(self):
    return "\\%s submits $%s$ to $\\cOV$" % \
           (self.submitter, ",".join([v.dumps()
            for v, size, _ in self.vectors]))


class ProverSubmitVectors(SubmitVectors):
  def __init__(self, vector, size, rust_size=None):
    super().__init__(
        "prover", vector, size, rust_size)


class IndexerSubmitVectors(SubmitVectors):
  def __init__(self, vector, size, rust_size=None):
    super().__init__(
        "indexer", vector, size, rust_size)


class VOQuerySide(object):
  def __init__(self, a, b):
    self.a = a
    self.b = b

  def dump_vec(v):
    ret = v.dumps()
    if not v.is_atom():
      ret = "\\left(%s\\right)" % ret
    return ret

  def _dumps(self, oper):
    return "%s\\%s %s" % (VOQuerySide.dump_vec(self.a),
                          oper, VOQuerySide.dump_vec(self.b))

  def shifts(self):
    return self.a.shifts() + self.b.shifts()

  def __mul__(self, other):
    return VOQuerySide(self.a * other, self.b)

  def __rmul__(self, other):
    return self.__mul__(other)

  def __neg__(self):
    return VOQuerySide(-self.a, self.b)

  def dumpr_at_index(self, index, coeff_manager):
    return rust(rust_mul(
        self.a.dumpr_at_index(index, coeff_manager),
        self.b.dumpr_at_index(index, coeff_manager)))

  def at_least_one_operand_is_structured(self):
    return (not isinstance(self.a, NamedVector) and
            not isinstance(self.a, VectorCombination)) or \
           (not isinstance(self.b, NamedVector) and
            not isinstance(self.b, VectorCombination))

  def _pick_the_non_constant(self, key1, key2, vec1, vec2, poly1, poly2, omega):
    if key2 == "one":
      return vec1, poly1, omega / X
    return vec2, poly2, X

  def _named_vector_constant_product_omega(
          self, coeff, key1, key2, vec1, vec2, poly1, poly2, omega):
    if key1 == "one" and key2 == "one":  # Constant-Constant
      return "$%s$" % tex(coeff)
    elif key1 == "one" or key2 == "one":  # Named-Constant
      named, named_poly, named_var = self._pick_the_non_constant(
          key1, key2, vec1, vec2, poly1, poly2, omega)
      return "$%s\\cdot %s$" % (
          add_paren_if_add(coeff),
          named_poly.dumps_var(named_var))
    else:  # Named-Named
      return "$%s\\cdot %s\\cdot %s$" % (
          add_paren_if_add(coeff),
          poly1.dumps_var(omega / X),
          poly2.dumps_var(X))

  def dump_product_items(self, omega, vec_to_poly_dict):
    hx_items = []
    a = VectorCombination._from(self.a)
    b = VectorCombination._from(self.b)
    for key1, vec1, value1 in a.key_keyed_coeffs():
      for key2, vec2, value2 in b.key_keyed_coeffs():
        hx_items.append(self._named_vector_constant_product_omega(
            simplify(value1.to_poly_expr(omega / X)
                     * value2.to_poly_expr(X)),
            key1, key2, vec1, vec2,
            "one" if key1 == "one" else vec_to_poly_dict[vec1.key()],
            "one" if key2 == "one" else vec_to_poly_dict[vec2.key()], omega))
    return hx_items


class VOQuery(object):
  def __init__(self, a, b, c=None, d=None):
    self.left_side = VOQuerySide(a, b)
    if c is not None and d is not None:
      self.right_side = VOQuerySide(c, d)
    else:
      self.right_side = None
    self.one_sided = self.right_side is None

  def dump_left_side(self):
    return self.left_side._dumps(self.oper)

  def dump_right_side(self):
    return self.right_side._dumps(self.oper)

  def dump_sides(self):
    if self.one_sided:
      return "%s\\stackrel{?}{=}\\vec{0}" % self.dump_left_side()
    return "%s\\stackrel{?}{=}%s" % \
           (self.dump_left_side(), self.dump_right_side())

  def dump_difference(self):
    if self.one_sided:
      return self.dump_left_side()
    return rust(rust_minus(self.dump_left_side(), self.dump_right_side()))

  def dumpr_at_index(self, index, coeff_manager):
    if self.one_sided:
      return self.left_side.dumpr_at_index(index, coeff_manager)
    return rust(rust_minus(
        self.left_side.dumpr_at_index(index, coeff_manager),
        self.right_side.dumpr_at_index(index, coeff_manager)))

  def dump_hadamard_difference(self):
    tmp, self.oper = self.oper, "circ"
    if self.one_sided:
      ret = self.dump_left_side()
    else:
      ret = "%s-%s" % (self.dump_left_side(), self.dump_right_side())
    self.oper = tmp
    return ret

  def dump_hadamard_difference_with_beta_power(self, beta, i):
    difference = self.dump_hadamard_difference()
    beta_power = beta ** i
    if not self.one_sided or difference.startswith("-"):
      difference = "\\left(%s\\right)" % difference

    if i > 0:
      difference = "%s\\cdot %s" % (tex(beta_power), difference)

    return "$%s$" % difference

  def dumps(self):
    return "\\verifier queries $\\cOV$ to check that $%s$" % self.dump_sides()

  def shifts(self):
    ret = self.left_side.shifts()
    if not self.one_sided:
      ret += self.right_side.shifts()
    return ret


class HadamardQuery(VOQuery):
  def __init__(self, a, b, c=None, d=None):
    super().__init__(a, b, c, d)
    self.oper = "circ"


class InnerProductQuery(VOQuery):
  def __init__(self, a, b, c=None, d=None):
    super().__init__(a, b, c, d)
    self.oper = "cdot"


class VOProtocolExecution(PublicCoinProtocolExecution):
  def __init__(self, vector_size, *args):
    super().__init__()
    self.args = args
    self.vector_size = vector_size
    self.rust_vector_size = None
    self.indexer_vectors = None
    self.hadamards = []
    self.inner_products = []
    self.vector_size_bound = Integer(0)
    self.vector_size_sum = Integer(0)
    self.coeff_manager = CoeffManager()
    # Hints provided by the user to simplify the expression
    # of the maximal vector size involved in the protocol.
    self._simplify_max_hints = None

  def simplify_max(self, expr):
    """
# There are many vectors involved in the VO protocol, with
# different sizes. To accomodate for the largest vector,
# our compiler will analyze the maximum size of the vectors
# symbolically. However, the resulting expression will be
# very complex, since the compiler does not know the relations
# between the symbols. The expression can be simplified if the
# user could provide some hints, telling the compiler which
# symbols represent integers that are guaranteed to be larger
# than others.
  """
    if self._simplify_max_hints is not None:
      return simplify_max_with_hints(expr, self._simplify_max_hints)
    return expr

  def preprocess_vector(self, vector, size):
    if self.indexer_vectors is not None:
      self.indexer_vectors.add_vector(vector, size)
    else:
      self.indexer_vectors = IndexerSubmitVectors(vector, size)

  def run_subprotocol_indexer(self, protocol, *args):
    protocol.preprocess(self, *args)

  def try_prover_redefine_vector_size_rust(self, name, value, piopexec=None):
    if self.rust_vector_size is None:
      executor = self if piopexec is None else piopexec
      self.rust_vector_size = executor.prover_redefine_symbol_rust(
          value, name)

  def try_verifier_redefine_vector_size_rust(self, name, value, piopexec=None):
    if self.rust_vector_size is None:
      executor = self if piopexec is None else piopexec
      self.rust_vector_size = executor.verifier_redefine_symbol_rust(
          value, name, positive=True)

  def _update_vector_size_bound(self, size):
    self.vector_size_bound = self.simplify_max(
        Max(self.vector_size_bound, size))
    self.vector_size_sum += size

  def prover_submit_vector(self, vector, size, rust_size=None):
    if len(self.interactions) > 0 and \
            isinstance(self.interactions[-1], ProverSubmitVectors):
      self.interactions[-1].add_vector(vector, size, rust_size)
    else:
      self.interactions.append(
          ProverSubmitVectors(vector, size, rust_size))
    self._update_vector_size_bound(size)

  def hadamard_query(self, a, b, c=None, d=None):
    self.hadamards.append(HadamardQuery(a, b, c, d))

  def inner_product_query(self, a, b, c=None, d=None):
    self.inner_products.append(InnerProductQuery(a, b, c, d))

  def run_subprotocol(self, protocol, *args):
    protocol.execute(self, *args)

  def dumps(self):
    ret = Algorithm(self.name)
    if hasattr(self, 'index'):
      ret.index = self.index
    ret.inputs = self.inputs
    ret.checks = self.checks
    for pp in self.preprocessings:
      ret.preprocesses.append(pp)
    if self.indexer_vectors is not None:
      for v, size, _ in self.indexer_vectors.vectors:
        ret.output_pk.append(v)
        ret.output_vk.append(v)
    for interaction in self.interactions:
      ret.interactions.append(interaction)
    for had in self.hadamards:
      ret.interactions.append(had.dumps())
    for inner in self.inner_products:
      ret.interactions.append(inner.dumps())
    return ret.dumps()


class VOProtocol(object):
  def __init__(self, name):
    self.name = name
    self._preprocess_args = None
    self._execute_args = None
  
  def with_preprocess_args(self, *args):
    self._preprocess_args = args
    return self
  
  def with_execute_args(self, *args):
    self._execute_args = args
    return self

  def get_named_vector_for_latex(self, arg, default_name, voexec):
    if isinstance(arg, NamedVector):
      return arg
    elif isinstance(arg, VectorCombination) or isinstance(arg, PowerVector) or \
            isinstance(arg, SparseVector) or isinstance(arg, UnitVector) or \
            isinstance(arg, StructuredVector):
      ret = get_named_vector(default_name)
      voexec.prover_computes_latex(Math(ret).assign(arg))
      return ret

    raise Exception("Invalid argument type %s" % type(arg))

  def check_argument_type(self, arg, *classtypes):
    for classtype in classtypes:
      if isinstance(arg, classtype):
        return
    raise Exception("Wrong argument type, expected %s, got %s"
                    % (
                        "/".join([t.__name__ for t in classtypes]),
                        type(arg)
                    ))

  def preprocess(self, voexec, *args):
    raise Exception("Should not call VOProtocol.preprocess directly")

  def preprocess_with_prestored_args(self, voexec):
    if self._preprocess_args is None:
      raise Exception("VOProtocol.preprocess_with_args called without arguments")
    self.preprocess(voexec, *self._preprocess_args)

  def execute(self, vopexec, *args):
    raise Exception("Should not call VOProtocol.execute directly")

  def execute_with_prestored_args(self, voexec):
    if self._execute_args is None:
      raise Exception("VOProtocol.execute_with_args called without arguments")
    self.execute(voexec, *self._execute_args)
  
  def get_minimal_vector_size(self, simplify_hints):
    voexec = VOProtocolExecution(Symbol("N"))
    voexec._simplify_max_hints = simplify_hints
    self.preprocess_with_prestored_args(voexec)
    self.execute_with_prestored_args(voexec)
    reset_name_counters()
    return voexec.vector_size_bound