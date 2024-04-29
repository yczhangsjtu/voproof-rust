from sympy import Expr, simplify
from ..builder.latex import tex
from ..builder.rust import *


class CoeffMap(object):
  def __init__(self):
    self._dict = {}

  def is_empty(self):
    return len(self._dict) == 0

  def set(self, keyed, value):
    if value is None:
      raise Exception("Value should not be None")
    key = keyed if isinstance(keyed, str) else keyed.key()
    if value == 0 or (isinstance(value, CoeffMap) and value.is_empty()) or \
       (isinstance(value, Expr) and simplify(value) == 0):
      self.remove_if_has(key)
    else:
      self._dict[key] = (keyed, value)

    return self

  def get(self, keyed):
    return self._dict[keyed.key()][1]

  def has(self, keyed):
    return keyed.key() in self._dict

  def remove_if_has(self, keyed):
    key = keyed if isinstance(keyed, str) else keyed.key()
    if key in self._dict:
      del self._dict[key]

  def items(self):
    return self._dict.items()

  def key_keyed_coeffs(self):
    for key, keyed_coeff in self.items():
      if not isinstance(keyed_coeff, tuple):
        raise TypeError(f"keyed_coeff must be a tuple, got {type(keyed_coeff)} {keyed_coeff}")
      keyed, coeff = keyed_coeff
      yield key, keyed, coeff

  def keyed_coeffs(self):
    return self._dict.values()

  def keyeds(self):
    for keyed, coeff in self._dict.values():
      yield keyed

  def coeffs(self):
    for keyed, coeff in self._dict.values():
      yield coeff

  def copy(self):
    ret = CoeffMap()
    for key, value in self._dict.items():
      if hasattr(value, 'copy'):
        ret._dict[key] = (key, value.copy())
      else:
        ret._dict[key] = (key, value)
    return ret

  def __add__(self, other):
    ret = self.copy()
    for key, keyed_value in other._dict.items():
      keyed, value = keyed_value
      if key in ret._dict:
        res = ret._dict[key][1] + value
        if res != 0:
          ret._dict[key] = (keyed, res)
        else:
          del ret._dict[key]
      else:
        ret._dict[key] = (keyed, value)

    return ret

  def __neg__(self):
    ret = CoeffMap()
    for key, keyed, value in self.key_keyed_coeffs():
      ret._dict[key] = (keyed, -value)
    return ret

  def __radd__(self, other):
    return self.__add__(other)
  
  def __sub__(self, other):
    return self.__add__(-other)
  
  def __rsub__(self, other):
    return self.__neg__()._add__(other)
  
  def __mul__(self, other):
    ret = CoeffMap()
    for key, keyed, value in self.key_keyed_coeffs():
      if value is None:
        for _key, _keyed_value in self._dict.items():
          _keyed, _value = _keyed_value
          if hasattr(_keyed, "dumps"):
            _keyed = _keyed.dumps()
          if hasattr(_value, "dumps"):
            _value = _value.dumps()
          print(_key, _keyed, _value)
        raise Exception("Value should not be None: key = %s, keyed = %s"
                        % (key, tex(keyed)))
      ret._dict[key] = (keyed, value * other)
    return ret

  def __rmul__(self, other):
    return self.__mul__(other)
  
  def __div__(self, other):
    ret = CoeffMap()
    for key, keyed_value in self._dict.items():
      keyed, value = keyed_value
      ret._dict[key] = (keyed, value / other)
    return ret


