from sympy import Symbol, sympify
from ..builder.latex import tex
from ..builder.rust import *


class _NamedBasic(object):
  def __init__(self, name, modifier=None, subscript=None, has_prime=False,
               _type=None):
    if "_" in name and subscript is None:
      name, subscript = name.split("_")
    self.name = name
    self.modifier = modifier
    self.subscript = subscript
    self.has_prime = has_prime
    self._type = _type
    self._cached_expr = None

  def key(self):
    ret = ["named_basic", self.name]
    ret.append(self.modifier if self.modifier is not None else "")
    ret.append(tex(self.subscript) if self.subscript is not None else "")
    ret.append("prime" if self.has_prime else "")
    ret.append(self._type if self._type is not None else "")
    return ":".join(ret)

  def sub(self, subscript):
    self.subscript = sympify(subscript)
    self._cached_expr = None
    return self

  def tilde(self):
    self.modifier = "tilde"
    self._cached_expr = None
    return self

  def hat(self):
    self.modifier = "hat"
    self._cached_expr = None
    return self

  def bar(self):
    self.modifier = "bar"
    self._cached_expr = None
    return self

  def prime(self):
    self.has_prime = True
    self._cached_expr = None
    return self

  def dumps(self):
    if self._cached_expr is not None:
      return self._cached_expr

    # The tex(Symbol(...)) here is to automatically add
    # slash to greek letter or ell, etc.
    ret = tex(Symbol(self.name))
    if self._type is not None:
      ret = "\\%s{%s}" % (self._type, ret)
    if self.modifier is not None:
      ret = "\\%s{%s}" % (self.modifier, ret)
    if self.subscript is not None:
      ret = "{%s}_{%s}" % (ret, tex(self.subscript))
    if self.has_prime:
      ret = "%s'" % ret

    self._cached_expr = ret
    return self._cached_expr

  # Dump rust name
  def dumpr(self):
    ret = [force_lowercase(self.name)]
    if self._type is not None:
      ret.append(self._type)
    if self.modifier is not None:
      ret.append(self.modifier)
    if self.subscript is not None:
      ret.append(keep_alpha_number(str(self.subscript)))
    if self.has_prime:
      ret.append("prime")
    return "_".join(ret)

__name_counters = {}


def get_name(name, modifier=None, has_prime=False, _type=None):
  global __name_counters
  key = _NamedBasic(name, modifier=modifier,
                    has_prime=has_prime, _type=_type).key()
  if key not in __name_counters:
    __name_counters[key] = 0
    return name
  else:
    __name_counters[key] += 1
    return "%s_%d" % (name, __name_counters[key])


def reset_name_counters():
  global __name_counters
  __name_counters = {}

