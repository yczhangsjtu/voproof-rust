from sympy import sympify, Expr
from .name_pair import name_pair

class QuadraticPolynomial(object):
  """
  A quadratic polynomial is a map from the following three types to sympy expressions:
  (1) a name pair of the form name1:name2 (note that the name cannot contain ":")
  (2) a name
  (3) the constant
  For example, the quadratic polynomial f(X1,X2,X3)=X1*X2+X1*X3+X2-3 is the following map:
  (1) X1:X2 => 1
  (2) X1:X3 => 1
  (3) X2 => 1
  (4) const => -3
  """

  def __init__(self):
    self.name_pair_dict = {}
    self.name_dict = {}
    self.constant = sympify(0)

  def _get_key_dict(self, name1=None, name2=None):
    if name2 is not None:
      """
      We assume that when name2 is not None, name1 must not be None.
      In this case, set the name pair
      """
      return name_pair(name1, name2), self.name_pair_dict

    if name1 is not None:
      return name1, self.name_dict

    return None, None

  def set(self, value, name1=None, name2=None):
    key, dic = self._get_key_dict(name1, name2)
    if key is not None:
      if value != 0:
        dic[key] = value
      else:
        """
        Setting the coefficient to zero means deleting the term
        """
        if key in self.name_pair_dict:
          del dic[key]
    else:
      """
      key = None means this is setting the constant
      """
      self.constant = value
  
  def get(self, name1=None, name2=None):
    key, dic = self._get_key_dict(name1, name2)
    if key is not None:
      if key in dic:
        return dic[key]
      return sympify(0)
    return self.constant

  def is_linear(self):
    return len(self.name_pair_dict) == 0

  def is_constant(self):
    return self.is_linear() and len(self.name_dict) == 0

  def _from(right):
    ret = QuadraticPolynomial()
    if isinstance(right, str):
      ret.set(right, sympify(1))
    elif isinstance(right, QuadraticPolynomial):
      ret.name_pair_dict = {key: value for key, value in right.name_pair_dict}
      ret.name_dict = {key: value for key, value in right.name_dict}
      ret.constant = right.constant
    elif isinstance(right, int):
      ret.constant = sympify(right)
    elif isinstance(right, Expr):
      ret.constant = right
    else:
      raise TypeError(f"Unexpected type: {type(right)}")
    return ret
  
  def copy(self):
    return QuadraticPolynomial._from(self)

  def __add__(self, right):
    if not isinstance(right, QuadraticPolynomial):
      right = QuadraticPolynomial._from(right)
    ret = self.copy()

    for key, value in right.name_pair_dict:
      if key in ret.name_pair_dict:
        ret.name_pair_dict[key] += value
      else:
        ret.name_pair_dict[key] = value

    for key, value in right.name_dict:
      if key in ret.name_dict:
        ret.name_dict[key] += value
      else:
        ret.name_dict[key] = value

    ret.constant += right.constant

    return ret

  def __radd__(self, right):
    return self.__add__(right)

  def __neg__(self):
    ret = QuadraticPolynomial()
    ret.name_pair_dict = {key: -value for key, value in right.name_pair_dict}
    ret.name_dict = {key: -value for key, value in right.name_dict}
    ret.constant = -right.constant
    return ret

  def __sub__(self, right):
    return self.__add__(-right)

  def __rsub__(self, right):
    return self.__neg__() + right

  def __mul__(self, right):
    right = sympify(right)
    ret = QuadraticPolynomial()
    ret.name_pair_dict = {key: right * value for key, value in right.name_pair_dict}
    ret.name_dict = {key: right * value for key, value in right.name_dict}
    ret.constant = right * right.constant
    return ret

  def __rmul__(self, right):
    return self.__mul__(right)

  def poly_and(alpha, *args):
    ret = QuadraticPolynomial()
    power = sympify(1)
    for arg in args:
      ret += power * QuadraticPolynomial._from(arg)
      power *= alpha
    return ret


class MultipleQuadraticPolynomials(object):
  """
  A collection of quadratic polynomials, used to represent a quadratic polynomial
  of dimension more than one
  """

  def __init__(self):
    self.polys = []
