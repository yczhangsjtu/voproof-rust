from sympy import sympify, Expr, Add
from .names import _NamedBasic, get_name
from .coeff_map import CoeffMap
from ..builder.latex import tex
from ..builder.rust import *


class NamedPolynomial(_NamedBasic):
  def __init__(self, name, modifier=None, subscript=None, has_prime=False):
    super(NamedPolynomial, self).__init__(name, modifier, subscript, has_prime)
    self._local_evaluate = False
    self._is_preprocessed = False
    self._vector = None

  def local_evaluate(self):
    return self._local_evaluate

  def dumps(self):
    return "%s(X)" % super(NamedPolynomial, self).dumps()

  def dumps_var(self, var):
    return "%s(%s)" % (super(NamedPolynomial, self).dumps(), tex(var))

  def to_comm(self):
    return PolynomialCommitment(self)

  def to_vec(self):
    from .vector import NamedVector
    return NamedVector(self.name, self.modifier, self.subscript, self.has_prime)

  def dumpr(self):
    return "%s_poly" % super(NamedPolynomial, self).dumpr()

  def dumpr_at_index(self, index, coeff_manager):
    return self._vector.dumpr_at_index(index, coeff_manager)


class PolynomialCommitment(object):
  def __init__(self, polynomial):
    # Must be named polynomial or named vector polynomial
    self.polynomial = polynomial
    self._is_preprocessed = polynomial._is_preprocessed
    self._rust_to_bytes_replacement = None

  def dumps(self):
    if isinstance(self.polynomial, NamedPolynomial):
      return "\\mathsf{cm}_{%s}" % super(NamedPolynomial, self.polynomial).dumps()
    else: # NamedVectorPolynomial
      return "\\mathsf{cm}_{%s}" % self.polynomial.vector.dumps()
  
  def dumpr(self):
    if isinstance(self.polynomial, NamedPolynomial):
      return "cm_%s" % super(NamedPolynomial, self.polynomial).dumpr()
    else:
      return "cm_%s" % self.polynomial.vector.dumpr()


def get_named_polynomial(name, modifier=None, has_prime=False):
  name = get_name(name, modifier=modifier, has_prime=has_prime, _type="poly")
  return NamedPolynomial(name, modifier=modifier, has_prime=has_prime)


class NamedVectorPolynomial(object):
  def __init__(self, named_vector):
    super(NamedVectorPolynomial, self).__init__()
    self.vector = named_vector
    self._is_preprocessed = False

  def local_evaluate(self):
    return self.vector.local_evaluate

  def key(self):
    return "named_vector_poly:%s" % self.vector.key()

  def dumps(self):
    return "f_{%s}(X)" % self.vector.dumps()

  def dumps_var(self, var):
    return "f_{%s}(%s)" % (self.vector.dumps(), tex(var))

  def to_comm(self):
    return PolynomialCommitment(self)

  def dumpr(self):
    return "%s_poly" % self.vector.dumpr()

  def dumpr_at_index(self, index, coeff_manager):
    return self.vector.dumpr_at_index(index, coeff_manager)
    
  def to_vec(self):
    return self.vector


class PolynomialCombination(CoeffMap):
  def __init__(self):
    super(PolynomialCombination, self).__init__()

  def copy(self):
    return PolynomialCombination._from(self)

  def _from(other):
    v = PolynomialCombination()
    if isinstance(other, int):
      return v.set("one", sympify(other))
    if isinstance(other, str):
      return v.set("one", sympify(other))
    if isinstance(other, Expr):
      return v.set("one", other)
    if isinstance(other, NamedPolynomial) or \
       isinstance(other, NamedVectorPolynomial):
      return v.set(other, 1)
    if isinstance(other, PolynomialCombination):
      for key, value in other.items():
        v._dict[key] = value
      return v
    raise Exception("Cannot convert %s to PolynomialCombination" % (type(other)))

  def __add__(self, other):
    if not isinstance(other, PolynomialCombination):
      other = PolynomialCombination._from(other)

    ret = super(PolynomialCombination, self).__add__(other)
    return PolynomialCombination._from(ret)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return PolynomialCombination._from(super(PolynomialCombination, self).__neg__())

  def __sub__(self, other):
    return self.__add__(-other)

  def __rsub__(self, other):
    return self.__neg__().__add__(other)

  def __mul__(self, other):
    return PolynomialCombination._from(super(PolynomialCombination, self).__mul__(other))

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return PolynomialCombination._from(super(PolynomialCombination, self).__div__(other))

  def dumps_var(self, var):
    not_ones = []
    one = None
    for key, poly_coeff in self.items():
      poly, coeff = poly_coeff
      if key == "one":
        one = coeff.dumps()
      else:
        not_ones.append(_multiply_if_not_one(poly.dumps_var(var), coeff))

    if one is not None:
      not_ones.append(one)

    items = []
    for item in not_ones:
      if not item.startswith("-") and len(items) > 0:
        items.append("+%s" % item)
      else:
        items.append(item)

    return "".join(items)

  def dumps(self):
    return self.dumps_var("X")

  def is_atom(self):
    if len(self._dict) > 1:
      return False

    if len(self._dict) == 0:
      return True

    for key, poly_coeff in self.items():
      if key == "one":
        poly, coeff = poly_coeff
        return not isinstance(coeff, Add)
      return True

