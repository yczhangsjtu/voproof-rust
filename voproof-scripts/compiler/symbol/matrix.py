from .names import _NamedBasic

class Matrix(_NamedBasic):
  def __init__(self, name, modifier=None, subscript=None, has_prime=False):
    super(Matrix, self).__init__(name, modifier, subscript, has_prime, _type = "mat")
    self._is_preprocessed = False
  
  def as_preprocessed(self):
    self._is_preprocessed = True
    return self

