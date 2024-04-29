from sympy import Symbol, latex, sympify, Integer, Expr,\
                  simplify, Max, Add, Mul, Pow, srepr
import re


def tex(expr):
  if isinstance(expr, str):
    return expr
  if hasattr(expr, "dumps") and not isinstance(expr, Expr):
    # Just in case Expr also has dumps
    return expr.dumps()
  if isinstance(expr, Expr):
    return latex(expr)
  return str(expr)


class LaTeXList(object):
  def __init__(self, _type="itemize"):
    self.items = []
    self._type = _type

  def dumps(self):
    return "\n\\begin{%s}\n\\item %s\n\\end{%s}\n\n" % \
           (self._type, "\n\\item ".join([tex(item) for item in self.items]),
            self._type)

  def append(self, item):
    if isinstance(item, list):
      self.items += item
    else:
      self.items.append(item)
    return self


class Itemize(LaTeXList):
  def __init__(self, init=None):
    super(Itemize, self).__init__("itemize")
    if init is not None:
      self.append(init)


class Enumerate(LaTeXList):
  def __init__(self, init=None):
    super(Enumerate, self).__init__("enumerate")
    if init is not None:
      self.append(init)


def encapsulate_type(item):
  if item.__class__.__name__ == "NamedVector":
    return "%s\\in\\field^n" % tex(item)
  if isinstance(item, Symbol):
    return "%s\\in\\mathbb{N}" % tex(item)
  if isinstance(item, tuple) and len(item) == 2:
    return "%s\\in %s" % (tex(item[0]), tex(item[1]))
  raise Exception("Unknown type: %s (%s)" % (type(item), tex(item)))


def name_to_label(name):
  name = re.sub('(.)([A-Z][a-z]+)', r'\1.\2', name)
  return re.sub('([a-z0-9])([A-Z])', r'\1.\2', name).lower()


def encaps_math(s):
  if s.startswith("$") or s.endswith("$"):
    return s
  return "$%s$" % s


class Algorithm(object):
  def __init__(self, name):
    self.name = name
    self.label = name_to_label(name)
    self.index = []
    self.inputs = []
    self.checks = []
    self.preprocesses = []
    self.output_pk = []
    self.output_vk = []
    self.interactions = []

  def dumps(self):
    if len(self.index) > 0:
      index = "\\Index %s\\\\" % ", ".join([encaps_math(encapsulate_type(item)) for item in self.index])
    else:
      index = ""

    inputs = ", ".join([encaps_math(encapsulate_type(item)) for item in self.inputs])
    checks = ", ".join([encaps_math(tex(item)) for item in self.checks])

    preprocesses = [pp for pp in self.preprocesses]
    indexer_sends = ""
    if len(self.output_pk) > 0:
      indexer_sends = "\\indexer sends %s to \\prover" % \
          ", ".join([encaps_math(tex(item)) for item in self.output_pk])

    vector_vks = [item for item in self.output_vk
                       if item.__class__.__name__ == "NamedVector"]
    nonvector_vks = [item for item in self.output_vk
                          if item.__class__.__name__ != "NamedVector"]
    if len(nonvector_vks) > 0:
      if len(indexer_sends) > 0:
        indexer_sends += ", sends "
      else:
        indexer_sends = "\\indexer sends "
      indexer_sends += "%s to \\verifier" % ", ".join([encaps_math(tex(item)) for item in nonvector_vks])

    if len(vector_vks) > 0:
      if len(indexer_sends) > 0:
        indexer_sends += ", submits "
      else:
        indexer_sends = "\\indexer submits "
      indexer_sends += "%s to \\cOV" % ", ".join([encaps_math(tex(item)) for item in vector_vks])

    if len(indexer_sends) > 0:
      preprocesses.append(indexer_sends)

    if len(preprocesses) > 0:
      preprocessing = """
  \\Preprocessing
  \\begin{algorithmic}[1]
    \\State %s
  \\end{algorithmic}
  \\Online
""" % "\n    \\State ".join([tex(item) for item in preprocesses])
    else:
      preprocessing = ""

    interactions = "\n    \\State ".join([tex(item) for item in self.interactions])

    return """\\begin{algorithm}[ht!]
  \\caption{$\\mathsf{%s}$ Protocol}
  \\label{alg:%s}
  %s %% Index
  \\Input %s\\\\
  \\Check %s\\\\
  %s %% Preprocessing
  \\begin{algorithmic}[1]
    \\State %s
  \\end{algorithmic}
\\end{algorithm}
""" % (self.name, self.label, index, inputs, checks, preprocessing, interactions)


class Condition(object):
  def __init__(self, first, second, condition):
    self.first = first
    self.second = second
    self.condition = condition

  def dumps(self):
    return """\\left\\{\\begin{array}{ll}\
  %s, & \\text{if}\\quad %s \\\\
  %s, & \\text{otherwise}
\\end{array}\\right.""" % (tex(self.first), tex(self.condition), tex(self.second))

class LaTeXBuilder(object):
  def __init__(self, *args):
    self.items = list(args)
    self.stack = []

  def append(self, right):
    if isinstance(right, list):
      self.items += right
    elif isinstance(right, LaTeXBuilder):
      self.items += right.items
    else:
      self.items.append(right)
    return self
  
  def append_to_last(self, right):
    if hasattr(self.items[-1], "append"):
      self.items[-1].append(right)
      return self
    raise Exception("Last item does not has append method")

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

  def sample(self, right=None):
    self.append("\\stackrel{\\$}{\\gets}")
    if right is not None:
      self.append(right)
    return self

  def equals(self, right=None):
    self.append("\\stackrel{?}{=}")
    if right is not None:
      self.append(right)
    return self

  def comma(self, right=None):
    self.append(",")
    if right is not None:
      self.append(right)
    return self

  def double_bar(self, right=None):
    self.append("\\|")
    if right is not None:
      self.append(right)
    return self

  def sim(self, right=None):
    self.append("\\sim")
    if right is not None:
      self.append(right)
    return self

  def plus(self, right=None, align=False):
    self.append("&+&" if align else "+")
    if right is not None:
      self.append(right)
    return self

  def minus(self, right=None, align=False):
    self.append("&-&" if align else "-")
    if right is not None:
      self.append(right)
    return self

  def dot(self, right=None):
    self.append("\\cdot")
    if right is not None:
      self.append(right)
    return self

  def circ(self, right=None):
    self.append("\\circ")
    if right is not None:
      self.append(right)
    return self

  def slash(self, right=None):
    self.append("/")
    if right is not None:
      self.append(right)
    return self

  def dots(self, right=None):
    self.append(",\\cdots")
    if right is not None:
      self.append(",")
      self.append(right)
    return self

  def paren(self, right=None):
    self.append("\\left(")
    if right is not None:
      self.append(right)
    self.append("\\right)")
    return self

  def bracket(self, right=None):
    self.append("\\left[")
    if right is not None:
      self.append(right)
    self.append("\\right]")
    return self
  
  def text(self, right):
    self.append("\\text{")
    self.append(right)
    self.append("}")
    return self

  def start_env(self, name, marker):
    self.append(marker)
    self.stack.append(name)
    return self

  def end_env(self, name, marker):
    if not self.stack[-1] == name:
      raise Exception("Cannot end %s. Last time is %s" % (name, self.stack[-1]))
    self.stack.pop()
    self.append(marker)
    return self
  
  def start_text(self):
    return self.start_env("text", "\\text{")
  
  def end_text(self):
    return self.end_env("text", "}")

  def start_math(self):
    return self.start_env("math", "$")

  def end_math(self):
    return self.end_env("math", "$")

  def start_paren(self):
    return self.start_env("paren", "(")

  def end_paren(self):
    return self.end_env("paren", ")")

  def sup(self, right):
    return self.append("^{").append(right).append("}")

  def sub(self, right):
    return self.append("_{").append(right).append("}")

  def math(self, right):
    self.append("$")
    self.append(right)
    self.append("$")
    return self

  def transpose(self, right, paren=True):
    if paren:
      self.append("\\left(")
      self.append(right)
      self.append("\\right)^\\mathsf{T}")
    else:
      self.append("{")
      self.append(right)
      self.append("}^\\mathsf{T}")
    return self

  def assign(self, right=None, align=False):
    self.append("&:=&" if align else ":=")
    if right is not None:
      self.append(right)
    return self

  def breakline(self):
    return self.append("\\\\")

  def eol(self):
    return self.append("\n")

  def eolb(self):
    return self.append("\\\\\n")

  def align(self):
    return self.append("&&")

  def subset(self, right):
    self.append("\\subset")
    if right is not None:
      self.append(right)
    return self

  def dumps(self):
    if len(self.stack) > 0:
      raise Exception("Stack is not empty")
    return " ".join([tex(arg) for arg in self.items])


class Math(LaTeXBuilder):
  def __init__(self, *args):
    super(Math, self).__init__()
    self.start_math()
    self.append(list(args))

  def dumps(self):
    if len(self.stack) > 1:
      raise Exception("Stack is not empty")

    if len(self.stack) == 1:
      if self.stack[0] != "math":
        raise Exception("Does not end with math")
      self.end_math()

    if self.items[0] != "$" or self.items[-1] != "$":
      raise Exception("Does not start or end with $: %s"
                      % super(Math, self).dumps())

    if len(self.items) <= 2:
      raise Exception("Empty math expression")

    return super(Math, self).dumps()


class ExpressionVector(object):
  def __init__(self, expr, length, variant=None):
    self.expr = expr
    self.length = sympify(length)
    self.variant = Symbol("i") if variant is None else variant

  def dumps(self):
    return "\\left(%s\\right)_{%s=1}^{%s}" \
           % (tex(self.expr), latex(self.variant), latex(self.length))


class AccumulationVector(object):
  def __init__(self, expr, length, accumulator="sum"):
    super(AccumulationVector, self).__init__()
    self.expr = expr
    self.length = sympify(length)
    self.accumulator = accumulator

  def dumps(self):
    return "\\left(\\%s_{j=1}^{i}%s\\right)_{i=1}^{%s}" \
           % (self.accumulator, tex(self.expr), latex(self.length))


class SumAccumulationVector(AccumulationVector):
  def __init__(self, named_vector, length):
    super(SumAccumulationVector, self).__init__(named_vector.slice("j"),
                                                length, "sum")


class ProductAccumulationDivideVector(AccumulationVector):
  def __init__(self, v1, v2, length):
    super(ProductAccumulationDivideVector, self).__init__(
        "\\left(%s/%s\\right)" % (v1.slice("j").dumps(), v2.slice("j").dumps()),
        length, "prod")


def add_paren_if_add(expr):
  if isinstance(expr, Add):
    return "\\left(%s\\right)" % latex(expr)
  return tex(expr)


def add_paren_if_not_atom(vector):
  if not vector.is_atom():
    return "\\left(%s\\right)" % tex(vector)
  return tex(vector)

