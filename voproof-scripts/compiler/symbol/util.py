from sympy import Add, Max, Symbol, Mul, Integer
from .names import get_name
from ..builder.rust import rust


def expand_max(expr):
  ret = []
  if isinstance(expr, Add):
    for arg in expr.args:
      subs = expand_max(arg)
      if len(ret) == 0:
        ret = subs
      else:
        ret = [a + b for a in ret for b in subs]
    return ret

  if isinstance(expr, Max):
    for arg in expr.args:
      ret += expand_max(arg)
    return ret

  if isinstance(expr, Symbol) or isinstance(expr, Integer):
    return [expr]

  if isinstance(expr, Mul):
    for arg in expr.args:
      subs = expand_max(arg)
      if len(ret) == 0:
        ret = subs
      else:
        ret = [a * b for a in ret for b in subs]
    return ret

  raise Exception("Unexpected type: %s" % type(expr))

def simplify_max(expr, larger=None, smaller=None):
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
  # print("Before: %s" % latex(expr))
  # print("Using: %s > %s" % (latex(larger), latex(smaller)))
  if larger is not None:
    diff = Symbol(get_name("diff"), positive=True)
    expr = expr.subs({larger: diff + smaller})

  items = expand_max(expr)
  # print("Items %s" % ",".join([latex(item) for item in items]))
  expr = Max(*items)

  if larger is not None:
    expr = expr.subs({diff: larger - smaller})
    items = expand_max(expr)
    expr = Max(*items)
    # print("Items %s" % ",".join([latex(item) for item in items]))

  # print("After: %s" % latex(expr))
  return expr


def simplify_max_with_hints(expr, hints):
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
  for larger, smaller in hints:
    expr = simplify_max(expr, larger, smaller)
  return expr


def get_rust_type(expr):
  from .poly import PolynomialCommitment
  if isinstance(expr, PolynomialCommitment):
    return "Commitment<E>"
  from .vector import NamedVector
  if isinstance(expr, NamedVector):
    return "Vec<E::ScalarField>"
  from .matrix import Matrix
  if isinstance(expr, Matrix):
    # Sparse representation of a matrix
    return "(Vec<u64>, Vec<u64>, Vec<E::ScalarField>)"
  if isinstance(expr, Symbol):
    if str(expr).startswith("W"):
      return "KZGProof<E>"
    else:
      return "E::ScalarField"
  raise Exception("Unknown rust type for: %s of type %s" %
                  (latex(expr), type(expr)))


def rust_vk(item):
  if hasattr(item, "_is_preprocessed") and item._is_preprocessed:
    return "vk.%s" % rust(item)
  return rust(item)


def rust_to_bytes_replacement(item):
  if hasattr(item, "_rust_to_bytes_replacement") and \
          item._rust_to_bytes_replacement is not None:
    return item._rust_to_bytes_replacement
  return item


def rust_pk(item):
  if hasattr(item, "_is_preprocessed") and item._is_preprocessed:
    return "pk.%s" % rust(item)
  return rust(item)


def rust_pk_vk(item):
  if hasattr(item, "_is_preprocessed") and item._is_preprocessed:
    return "pk.verifier_key.%s" % rust(item)
  return rust(item)
