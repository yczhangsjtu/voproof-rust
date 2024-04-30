from sympy import Symbol, sympify, Expr, simplify, Add, Integer, collect, Max, count_ops, S
from sympy.core.numbers import Infinity
from .names import _NamedBasic, get_name
from .util import rust_pk
from .coeff_map import CoeffMap
from ..builder.latex import tex
from ..builder.rust import *


class NamedVector(_NamedBasic):
  def __init__(self, name, modifier=None, subscript=None, has_prime=False):
    super(NamedVector, self).__init__(name, modifier=modifier, subscript=subscript,
                                      has_prime=has_prime, _type="vec")
    self.local_evaluate = False
    self.hint_computation = None
    self.randomizers = None
    self._is_preprocessed = False
    self._do_not_count_shifts = False
    self._rust_to_bytes_replacement = None
    self._do_not_randomize = False

  def key(self):
    if self._is_preprocessed:
      return "%s:pk" % super().key()
    return super().key()

  def slice(self, start, end=None):
    return VectorSlice(self, start, end)

  def is_atom(self):
    return True

  def shifts(self):
    return []

  def to_named_vector_poly(self):
    from .poly import NamedVectorPolynomial
    ret = NamedVectorPolynomial(self)
    ret._is_preprocessed = self._is_preprocessed
    return ret
  
  def can_local_evaluate(self, hint_computation):
    self.local_evaluate = True
    self.hint_computation = hint_computation
    return self
  
  def does_not_contribute_to_max_shift(self):
    self._do_not_count_shifts = True
    return self
  
  def as_preprocessed(self):
    self._is_preprocessed = True
    return self

  def get_poly_with_same_name(self):
    return get_named_polynomial(self.name,
                                modifier=self.modifier,
                                has_prime=self.has_prime)

  def __add__(self, other):
    return VectorCombination._from(self).__add__(other)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return VectorCombination._from(self).__neg__()

  def __sub__(self, other):
    return VectorCombination._from(self).__sub__(other)

  def __rsub__(self, other):
    return VectorCombination._from(self).__rsub__(other)

  def __mul__(self, other):
    return VectorCombination._from(self).__mul__(other)

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return VectorCombination._from(self).__div__(other)

  def shift(self, length, rust_length=None):
    return self.__mul__(UnitVector(length + 1,
                                   rust_length + 1 if rust_length is not None else None))

  def dumpr_at_index(self, index, coeff_manager):
    return rust(RustMacro("vector_index").append([rust_pk(self), rust(index)]))

  def _dump_symbol_rust_at_index(self, index, coeff_manager, collect_symbols=None):
    code = self.dumpr_at_index(index, coeff_manager)
    symbol = _rust_symbol_dictionary.add(code)
    return Symbol(symbol)

  def dump_symbol_hint_computation(self, z):
    code = rust(self.hint_computation(z))
    symbol = _rust_symbol_dictionary.add(code)
    return Symbol(symbol)


def get_named_vector(name, modifier=None, has_prime=False):
  name = get_name(name, modifier=modifier, has_prime=has_prime, _type="vec")
  return NamedVector(name, modifier=modifier, has_prime=has_prime)


def get_named_vectors(names, modifier=None, has_prime=False):
  return [get_named_vector(name, modifier=modifier, has_prime=has_prime) for name in names]


class VectorSlice(object):
  def __init__(self, named_vector, start, end=None):
    super(VectorSlice, self).__init__()
    self.named_vector = named_vector
    self.start = sympify(start)
    self.end = None if end is None else sympify(end)

  def get_range(self, start, end):
    if self.end is None:
      return "[%s]" % start
    if self.end == Infinity:
      return "[%s..]" % start
    slc = "[%s..%s]" % (start, end)
    return slc

  def dumps(self):
    end = tex(self.end) if self.end is not None else ""
    return "{%s}_{%s}" % (self.named_vector.dumps(),
                          self.get_range(tex(self.start), end))

  def dumpr(self):
    end = str(self.end) if self.end is not None else ""
    return "%s%s" % (self.named_vector.dumpr(),
                     self.get_range(str(self.start), end))


class UnitVector(object):
  def __init__(self, position, rust_position=None):
    # position can be Symbol, Expr or Integer
    self.position = simplify(sympify(position))
    self.rust_position = self.position if rust_position is None \
        else simplify(sympify(rust_position))

  def dumps(self):
    return "\\vec{e}_{%s}" % (tex(self.position))

  def key(self):
    return "unit_vector:%s" % (tex(self.position))

  def is_atom(self):
    return True

  def shifts(self):
    return []

  def to_poly_expr(self, var):
    if self.position == 1:
      return Symbol(rust(rust_one()))
    return var ** (self.position - 1)

  def to_poly_expr_rust(self, var):
    if self.position == 1:
      return Symbol(rust(rust_one()))
    return var ** (self.rust_position - 1)

  def __add__(self, other):
    return SparseVector._from(self).__add__(other)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return SparseVector._from(self).__neg__()

  def __sub__(self, other):
    return SparseVector._from(self).__sub__(other)

  def __rsub__(self, other):
    return SparseVector._from(self).__rsub__(other)

  def __mul__(self, other):
    if isinstance(other, UnitVector):
      return UnitVector(
          self.position + other.position - 1,
          self.rust_position + other.rust_position - 1)
    return SparseVector._from(self).__mul__(other)

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return SparseVector._from(self).__div__(other)

  def dumpr_at_index(self, index, coeff_manager):
    return rust(RustMacro("delta").append([rust(index), rust(self.rust_position)]))

  def _dump_symbol_rust_at_index(self, index, coeff_manager, collect_symbols=None):
    code = self.dumpr_at_index(index, coeff_manager)
    symbol = _rust_symbol_dictionary.add(code)
    return Symbol(symbol)

  def reverse_omega(self, omega):
    return SparseVector._from(self).reverse_omega(omega)


class SparseVector(CoeffMap):
  def __init__(self):
    super(SparseVector, self).__init__()

  def set(self, position, value, rust_position=None):
    value = simplify(sympify(value))
    if not isinstance(position, UnitVector):
      unit_vector = UnitVector(position, rust_position)
    else:
      unit_vector = position
    if value == 0:
      self.remove_if_has(unit_vector)
      return self
    return super(SparseVector, self).set(unit_vector, value)

  def get(self, position, rust_position=None):
    if not isinstance(position, UnitVector):
      unit_vector = UnitVector(position, rust_position)
    else:
      unit_vector = position
    if not self.has(unit_vector):
      return sympify(0)
    return super(SparseVector, self).get(unit_vector)

  def copy(self):
    return SparseVector._from(self)

  def _from(other):
    v = SparseVector()
    if isinstance(other, int):
      return v.set(1, sympify(other))
    if isinstance(other, str):
      return v.set(1, sympify(other))
    if isinstance(other, Expr):
      return v.set(1, other)
    if isinstance(other, UnitVector):
      return v.set(other, sympify(1))
    if isinstance(other, SparseVector) or type(other) == CoeffMap:
      for key, value in other.items():
        v._dict[key] = value
      return v
    raise Exception("Cannot convert %s to SparseVector" % (type(other)))

  def __add__(self, other):
    if isinstance(other, VectorCombination) or \
       isinstance(other, StructuredVector) or \
       isinstance(other, PowerVector):
      return other.__add__(self)

    if not isinstance(other, SparseVector):
      other = SparseVector._from(other)

    ret = super(SparseVector, self).__add__(other)
    return SparseVector._from(ret)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return SparseVector._from(super(SparseVector, self).__neg__())

  def __sub__(self, other):
    return self.__add__(-other)

  def __rsub__(self, other):
    return self.__neg__().__add__(other)

  def __mul__(self, other):
    if isinstance(other, UnitVector):
      other = SparseVector._from(other)

    if isinstance(other, PowerVector):
      other = StructuredVector._from(other)

    if isinstance(other, SparseVector):
      v = SparseVector()
      for left_key, vector_coeff in self.items():
        left_vector, left_coeff = vector_coeff
        for right_key, vector_coeff_2 in other.items():
          right_vector, right_coeff = vector_coeff_2
          vector = left_vector * right_vector
          coeff = left_coeff * right_coeff
          if v.has(vector):
            v.set(vector, v.get(vector.position) + coeff)
          else:
            v.set(vector, coeff)
      return v

    if isinstance(other, StructuredVector) or isinstance(other, VectorCombination):
      return other.__mul__(self)
    return SparseVector._from(super(SparseVector, self).__mul__(other))

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return SparseVector._from(super(SparseVector, self).__div__(other))

  def dumps(self):
    items = []
    for key, uv_coeff in self.items():
      unit_vector, coeff = uv_coeff
      items.append(_multiply_if_not_one(unit_vector.dumps(), coeff))

    if len(items) == 0:
      return "\\vec{0}"

    items_with_pluses = []
    for item in items:
      if not item.startswith("-") and len(items_with_pluses) > 0:
        items_with_pluses.append("+%s" % item)
      else:
        items_with_pluses.append(item)

    return "".join(items_with_pluses)

  def is_atom(self):
    return len(self._dict) == 1

  def shifts(self):
    return []

  def shift(self, length, rust_length=None):
    return self.__mul__(UnitVector(length + 1,
                                   rust_length + 1 if rust_length is not None else None))

  def to_poly_expr(self, var):
    items = []
    for key, uv_coeff in self.items():
      unit_vector, coeff = uv_coeff
      items.append(unit_vector.to_poly_expr(var) * coeff)
    return sum(items)

  def to_poly_expr_rust(self, var):
    items = []
    for key, uv_coeff in self.items():
      unit_vector, coeff = uv_coeff
      items.append(unit_vector.to_poly_expr_rust(var) * coeff)
    return sum(items)

  def dumpr_at_index(self, index, coeff_manager):
    ret = RustMacro("multi_delta").append(rust(index))
    for unit_vector, coeff in self.keyed_coeffs():
      coeff = coeff_manager.add(coeff)
      ret.append([to_field(coeff), unit_vector.rust_position])
    return rust(ret)

  def _dump_symbol_rust_at_index(self, index, coeff_manager, collect_symbols=None):
    ret = Integer(0)
    for unit_vector, coeff in self.keyed_coeffs():
      ret += coeff * unit_vector._dump_symbol_rust_at_index(index, coeff_manager)
    return ret

  def reverse_omega(self, omega):
    # f_v(X) => f_v(omega X^{-1})
    v = SparseVector()
    for key, uv_coeff in self.items():
      unit_vector, coeff = uv_coeff
      v.set(
          2 - unit_vector.position,
          coeff * (omega ** (unit_vector.position - 1)),
          2 - unit_vector.rust_position)
    return v


def _shift_if_not_zero(vec, shifted):
  if simplify(shifted) == 0:
    return vec
  return "{%s}^{\\to %s}" % (vec, tex(shifted))


def _multiply_if_not_one(vec, coeff):
  if simplify(coeff-1) == 0:
    return vec
  elif simplify(coeff+1) == 0:
    return "-%s" % vec
  else:
    if isinstance(coeff, Add):
      return "\\left(%s\\right)\\cdot %s" % (tex(coeff), vec)
    return "%s\\cdot %s" % (tex(coeff), vec)


def _dump_coeff_map_with_sparse_coeff(v):
  not_ones = []
  one = None
  for key, vec_value in v.items():
    vec, value = vec_value
    if key == "one":
      one = value.dumps()
      if len(one) == 0:
        raise Exception("value should not be empty: %s" % str(value))
    else:
      for key2, uv_coeff in value.items():
        unit_vector, coeff = uv_coeff
        shifted_vec = _shift_if_not_zero(vec.dumps(), unit_vector.position - 1)
        not_ones.append(_multiply_if_not_one(shifted_vec, coeff))

  if one is not None:
    not_ones.append(one)

  items = []
  for v in not_ones:
    if len(v) == 0:
      print(not_ones)
      raise Exception("v should not be empty")
    if not v.startswith("-") and len(items) > 0:
      items.append("+%s" % v)
    else:
      items.append(v)

  return "".join(items)


def _dumpr_at_index_for_sparse_coefficient(v, index, coeff_manager):
  has_one = "one" in v._dict
  ret = rust_linear_combination(v._dict["one"][1].dumpr_at_index(index, coeff_manager)) \
      if has_one else rust_linear_combination_base_zero()

  for key, vec, value in v.key_keyed_coeffs():
    if key == "one":
      continue
    for key2, unit_vector, coeff in value.key_keyed_coeffs():
      ret.append(to_field(coeff))
      ret.append(vec.dumpr_at_index(rust_minus_i64(
          index, unit_vector.rust_position), coeff_manager))

  if len(ret) == 2 and not has_one:
    if ret[0] == to_field(1):
      return rust(ret[1])
    if ret[0] == to_field(-1):
      return rust(rust_neg(ret[1]))
    if ret[1] == to_field(1):
      return rust(ret[0])
    if ret[1] == to_field(-1):
      return rust(rust_neg(ret[0]))
    if ret[0] == 0 or rust[1] == 0 or ret[0] == to_field(0) or ret[1] == to_field(0):
      return to_field(0)
    return rust(rust_mul(ret[0], ret[1]))

  return rust(ret)


class _RustSymbolDictionary(object):
  def __init__(self):
    self.rust_to_symbol = {}
    self.symbol_to_rust = {}
    self.counter = 0

    self.one = self.add("one!()")

  def get_rust(self, symbol):
    return self.symbol_to_rust[symbol]

  def get_symbol(self, code):
    return self.rust_to_symbol[code]

  def add(self, code):
    if not isinstance(code, str):
      raise TypeError("code must be str, got {}".format(type(code)))
    if code in self.rust_to_symbol:
      return self.rust_to_symbol[code]

    name = "rustsymboldict_{}_".format(self.counter)
    self.counter += 1
    self.rust_to_symbol[code] = name
    self.symbol_to_rust[name] = code
    return name

  def dumpr(self, expr):
    code = rust(expr)
    for symbol, r in self.symbol_to_rust.items():
      code = code.replace(symbol, r)
    return code


_rust_symbol_dictionary = _RustSymbolDictionary()


def custom_measure(expr):
  POW = Symbol("POW")
  MUL = Symbol("MUL")
  """
  Discourage the use of power and mul operator in simplification
  """
  count = count_ops(expr, visual=True).subs(POW, 20)
  count = count_ops(expr, visual=True).subs(MUL, 10)
  count = count.replace(Symbol, type(S.One))

  symbols = expr.atoms(Symbol)
  nsymbols = len([s for s in symbols if str(s).startswith("rustsymboldict")])
  count += nsymbols * 100

  return count
  # return len(_rust_symbol_dictionary.dumpr(expr))


def _dump_symbol_rust_at_index_for_sparse_coefficient(
    v, index, coeff_manager, collect_symbols=None):
  ret = Integer(0)
  for key, vec, value in v.key_keyed_coeffs():
    if key == "one":
      """
      The constant term is either structured vector or sparse vector
      """
      ret += value._dump_symbol_rust_at_index(index, coeff_manager)
      continue
    for key2, unit_vector, coeff in value.key_keyed_coeffs():
      coeff = coeff_manager.add(coeff)
      ret += coeff * vec._dump_symbol_rust_at_index(rust_minus_i64(
          index, unit_vector.rust_position), coeff_manager)

  ret = simplify(ret, measure=custom_measure)
  if collect_symbols is not None:
    ret = collect(ret, collect_symbols)

  return ret


class VectorCombination(CoeffMap):
  def __init__(self):
    super(VectorCombination, self).__init__()

  def copy(self):
    return VectorCombination._from(self)

  def _from(other):
    v = VectorCombination()
    if isinstance(other, int) or isinstance(other, str) or \
       isinstance(other, Expr) or isinstance(other, UnitVector):
      return v.set("one", StructuredVector._from(other))
    if isinstance(other, SparseVector) or isinstance(other, PowerVector):
      return v.set("one", StructuredVector._from(other))
    if isinstance(other, StructuredVector):
      return v.set("one", other.copy())
    if isinstance(other, NamedVector):
      return v.set(other, SparseVector._from(1))
    if isinstance(other, VectorCombination) or type(other) == CoeffMap:
      for key, value in other.items():
        v._dict[key] = value
      return v
    raise Exception("Cannot convert %s to VectorCombination" % (type(other)))

  def __add__(self, other):
    if not isinstance(other, VectorCombination):
      other = VectorCombination._from(other)

    ret = super(VectorCombination, self).__add__(other)
    return VectorCombination._from(ret)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return VectorCombination._from(super(VectorCombination, self).__neg__())

  def __sub__(self, other):
    return self.__add__(-other)

  def __rsub__(self, other):
    return self.__neg__().__add__(other)

  def __mul__(self, other):
    if isinstance(other, VectorCombination):
      raise Exception("VectorCombinations should not be multiplied together")
    if isinstance(other, StructuredVector):
      raise Exception(
          "VectorCombination should not be multiplied with StructuredVector")
    return VectorCombination._from(super(VectorCombination, self).__mul__(other))

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return VectorCombination._from(super(VectorCombination, self).__div__(other))

  def is_atom(self):
    if len(self._dict) > 1:
      return False

    if len(self._dict) == 0:
      return True

    for key, vec_value in self.items():
      vec, value = vec_value
      return value.is_atom()

  def shift(self, length, rust_length=None):
    return self.__mul__(UnitVector(length + 1,
                                   rust_length + 1 if rust_length is not None else None))

  def shifts(self):
    lengths = []
    for key, vec_value in self.items():
      if key == "one":
        continue
      vec, value = vec_value
      if vec._do_not_count_shifts:
        continue
      for key2, uv_coeff in value.items():
        unit_vector, coeff = uv_coeff
        lengths.append(unit_vector.position - 1)
    return lengths

  def dumps(self):
    return _dump_coeff_map_with_sparse_coeff(self)

  def dumpr_at_index(self, index, coeff_manager, collect_symbols=None):
    """
    Old version: dump a linear combination rust macro

    return _dumpr_at_index_for_sparse_coefficient(self, index)
    """
    return _rust_symbol_dictionary.dumpr(
        self._dump_symbol_rust_at_index(
          index, coeff_manager, collect_symbols=collect_symbols))

  def _dump_symbol_rust_at_index(self, index, coeff_manager, collect_symbols=None):
    return _dump_symbol_rust_at_index_for_sparse_coefficient(
        self, index, coeff_manager, collect_symbols=collect_symbols)

  def dump_named_vectors(self, result):
    for key, vec_value in self.items():
      if key != "one" and key not in result:
        vec, value = vec_value
        result[key] = vec


class PowerVector(object):
  def __init__(self, alpha, size, rust_size=None):
    # alpha and size can be Symbol or Integer
    self.alpha = simplify(sympify(alpha))
    self.size = simplify(sympify(size))
    self.rust_size = self.size if rust_size is None else simplify(
        sympify(rust_size))

  def key(self):
    return "power_vector:%s:%s" % (tex(self.alpha), tex(self.size))

  def dumps(self):
    return "\\vec{%s}^{%s}" % (tex(self.alpha), tex(self.size))

  def is_atom(self):
    return True

  def shifts(self):
    return []

  def __add__(self, other):
    return StructuredVector._from(self).__add__(other)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return StructuredVector._from(self).__neg__()

  def __sub__(self, other):
    return StructuredVector._from(self).__sub__(other)

  def __rsub__(self, other):
    return StructuredVector._from(self).__rsub__(other)

  def __mul__(self, other):
    if isinstance(other, StructuredVector):
      raise Exception(
          "StructuredVector cannot be multiplied with power vector")
    if isinstance(other, PowerVector):
      raise Exception("PowerVectors cannot be multiplied together")
    return StructuredVector._from(self).__mul__(other)

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return StructuredVector._from(self).__div__(other)

  def shift(self, length, rust_length=None):
    return self.__mul__(UnitVector(length + 1,
                                   rust_length + 1 if rust_length is not None else None))

  def to_poly_expr(self, var):
    if self.size == 0:
      return 0
    return ((self.alpha * var) ** self.size - Symbol("one!()")) / (self.alpha * var - Symbol("one!()"))

  def to_poly_expr_rust(self, var):
    if self.size == 0 or self.rust_size == 0:
      return 0
    return ((self.alpha * var) ** self.rust_size - Symbol("one!()")) / (self.alpha * var - Symbol("one!()"))

  def dumpr_at_index(self, index, coeff_manager):
    """
    In case the index is always larger than the size, then directly return zero
    """
    if isinstance(index, Expr) and \
            simplify(Max(self.rust_size - 1, index) - index) == 0:
      return rust(rust_zero())

    if self.alpha != 1:
      base = coeff_manager.add(self.alpha)
      return rust(RustMacro("power_vector_index").append([
          rust(base, to_field=True), self.rust_size, index]))
    elif self.size == 0 or self.rust_size == 0:
      return rust(rust_zero())
    else:
      return rust(rust_range_index(1, self.rust_size, index))

  def _dump_symbol_rust_at_index(self, index, coeff_manager, collect_symbols=None):
    """
    In case the index is always larger than the size, then directly return zero
    """
    if isinstance(index, Expr) and \
            simplify(Max(self.rust_size - 1, index) - index) == 0:
      return Integer(0)

    code = self.dumpr_at_index(index, coeff_manager)
    symbol = _rust_symbol_dictionary.add(code)
    return Symbol(symbol)

  def reverse_omega(self, omega):
    return StructuredVector._from(self).reverse_omega(omega)


class StructuredVector(CoeffMap):
  def __init__(self):
    super(StructuredVector, self).__init__()

  def copy(self):
    return StructuredVector._from(self)

  def _from(other):
    v = StructuredVector()
    if isinstance(other, int) or isinstance(other, str) or \
       isinstance(other, Expr) or isinstance(other, UnitVector):
      return v.set("one", SparseVector._from(other))
    if isinstance(other, SparseVector):
      return v.set("one", other.copy())
    if isinstance(other, PowerVector):
      return v.set(other, SparseVector._from(1))
    if isinstance(other, StructuredVector) or type(other) == CoeffMap:
      for key, value in other.items():
        v._dict[key] = value
      return v
    raise Exception("Cannot convert %s to StructuredVector" % (type(other)))

  def __add__(self, other):
    if isinstance(other, VectorCombination) or \
       isinstance(other, NamedVector):
      return other.__add__(self)

    if not isinstance(other, StructuredVector):
      other = StructuredVector._from(other)

    ret = super(StructuredVector, self).__add__(other)
    return StructuredVector._from(ret)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return StructuredVector._from(super(StructuredVector, self).__neg__())

  def __sub__(self, other):
    return self.__add__(-other)

  def __rsub__(self, other):
    return self.__neg__().__add__(other)

  def __mul__(self, other):
    if isinstance(other, StructuredVector):
      raise Exception("Structured vectors cannot be multiplied together")
    if isinstance(other, PowerVector):
      raise Exception(
          "Structured vector cannot be multiplied with a PowerVector")
    return StructuredVector._from(super(StructuredVector, self).__mul__(other))

  def __rmul__(self, other):
    return self.__mul__(other)

  def __div__(self, other):
    return StructuredVector._from(super(StructuredVector, self).__div__(other))

  def dumps(self):
    return _dump_coeff_map_with_sparse_coeff(self)

  def is_atom(self):
    if len(self._dict) > 1:
      return False

    if len(self._dict) == 0:
      return True

    for key, vec_value in self.items():
      vec, value = vec_value
      return value.is_atom()

  def shifts(self):
    return []

  def shift(self, length, rust_length=None):
    return self.__mul__(UnitVector(length + 1,
                                   rust_length + 1 if rust_length is not None else None))

  def to_poly_expr(self, var):
    items = []
    for key, power_value in self.items():
      vector, value = power_value
      if key == "one":
        items.append(value.to_poly_expr(var))
      else:
        items.append(vector.to_poly_expr(var) * value.to_poly_expr(var))
    return sum(items)

  def to_poly_expr_rust(self, var):
    items = []
    for key, power_value in self.items():
      vector, value = power_value
      if key == "one":
        items.append(value.to_poly_expr_rust(var))
      else:
        items.append(vector.to_poly_expr_rust(
            var) * value.to_poly_expr_rust(var))
    return sum(items)

  def dumpr_at_index(self, index, coeff_manager, collect_symbols=None):
    """
    Old version: dump a linear combination rust macro

    return _dumpr_at_index_for_sparse_coefficient(self, index)
    """
    return _rust_symbol_dictionary.dumpr(
        self._dump_symbol_rust_at_index(
          index, coeff_manager, collect_symbols=collect_symbols))

  def _dump_symbol_rust_at_index(self, index, coeff_manager, collect_symbols=None):
    return _dump_symbol_rust_at_index_for_sparse_coefficient(
        self, index, coeff_manager, collect_symbols=collect_symbols)

  def reverse_omega(self, omega):
    ret = StructuredVector()
    for key, power_value in self.items():
      vector, value = power_value
      if key == "one":
        ret._dict[key] = (key, value.reverse_omega(omega))
      else:
        # f(X) => f(omega X^{-1}) transforms the power vector to the coefficients of
        # (X^{-(k-1)}(alpha omega)^{k-1}) * (1 + (alpha omega)^{-1} X + ...)
        # which is a transformed power vector. The transformation is then applied
        # to the coefficient for this power vector
        ret._dict[key] = (PowerVector(1/(vector.alpha * omega), vector.size),
                          (value.reverse_omega(omega) *
                          ((vector.alpha * omega) ** (vector.size - 1)))
                          .shift(-vector.size + 1))
    return ret


def vec_lists_dump_at_index_then_inner_product(
    vec_pairs, index, coeff_manager, collect_symbols=None):
  ret = Integer(0)
  for vec1, vec2 in vec_pairs:
    ret += vec1._dump_symbol_rust_at_index(index, coeff_manager, collect_symbols) * \
        vec2._dump_symbol_rust_at_index(index, coeff_manager, collect_symbols)

  ret = simplify(ret, measure=custom_measure)
  if collect_symbols is not None:
    ret = collect(ret, collect_symbols)
  return _rust_symbol_dictionary.dumpr(ret)


def list_sum_to_rust_map(values, collect_symbols=None):
  ret = sum(values)
  ret = simplify(ret, measure=custom_measure)
  if collect_symbols is not None:
    ret = collect(ret, collect_symbols)
  return _rust_symbol_dictionary.dumpr(ret)


class NamedVectorPair(object):
  def __init__(self, u, v):
    if not isinstance(u, NamedVector) and not isinstance(v, NamedVector):
      raise Exception("At least one of u, v should be NamedVector")
    if not isinstance(u, NamedVector) and u is not None:
      raise Exception("u should be either NamedVector or None")
    if not isinstance(v, NamedVector) and v is not None:
      raise Exception("v should be either NamedVector or None")
    self.u = u
    self.v = v

  def key(self):
    left = self.u.key() if self.u is not None else "one"
    right = self.v.key() if self.v is not None else "one"
    return left + ":vector_pair:" + right


class StructuredVectorPair(object):
  def __init__(self, u, v):
    if not isinstance(u, StructuredVector) and not isinstance(v, StructuredVector):
      raise Exception("At least one of u, v should be StructuredVector")
    if not isinstance(u, StructuredVector) and u is not None:
      raise Exception("u should be either StructuredVector or None")
    if not isinstance(v, StructuredVector) and v is not None:
      raise Exception("v should be either StructuredVector or None")
    self.u = u
    self.v = v

  def key(self):
    left = self.u.key() if self.u is not None else "one"
    right = self.v.key() if self.v is not None else "one"
    return left + ":struct_vector_pair:" + right

  def _from(other):
    if isinstance(other, int) or isinstance(other, str) or \
       isinstance(other, Expr) or isinstance(other, UnitVector) or \
       isinstance(other, SparseVector) or isinstance(other, PowerVector):
      other = StructuredVector._from(other)
    if isinstance(other, StructuredVector):
      return StructuredVectorPair(None, other)

  def copy(self):
    left = self.u.copy() if self.u is not None else None
    right = self.v.copy() if self.v is not None else None
    return StructuredVectorPair(left, right)

  def __neg__(self):
    if self.u is not None:
      return StructuredVectorPair(-self.u, self.v)
    return StructuredVectorPair(self.u, -self.v)


class StructuredVectorPairCombination(object):
  def __init__(self):
    self.pairs = []
    self.one = None

  def copy(self):
    return StructuredVectorPairCombination._from(self)

  def add_pair(self, pair):
    self.pairs.append(pair)
    return self

  def add_structured_vector(self, vec):
    if self.one is not None:
      self.one = self.one + vec
    else:
      self.one = vec
    return self

  def _from(other):
    v = StructuredVectorPairCombination()
    if isinstance(other, int) or isinstance(other, str) or \
       isinstance(other, Expr) or isinstance(other, UnitVector) or \
       isinstance(other, SparseVector) or isinstance(other, PowerVector) or \
       isinstance(other, StructuredVector):
      return v.add_structured_vector(StructuredVector._from(other))
    if isinstance(other, StructuredVectorPair):
      return v.add_pair(other)
    if isinstance(other, tuple) and isinstance(other[0], StructuredVector) and \
       isinstance(other[1], StructuredVector):
      return v.add_pair(StructuredVectorPair(other[0], other[1]))
    if isinstance(other, StructuredVectorPairCombination):
      v.pairs = [pair for pair in other.pairs]
      v.one = other.one
      return v
    raise Exception(
        "Cannot convert %s to StructuredVectorPairCombination" % (type(other)))

  def __add__(self, other):
    if not isinstance(other, StructuredVectorPairCombination):
      other = StructuredVectorPairCombination._from(other)

    ret = StructuredVectorPairCombination()
    ret.pairs = self.pairs + other.pairs
    ret.one = None if self.one is None and other.one is None \
        else (StructuredVector._from(0) if self.one is None else self.one) + \
        (StructuredVector._from(0) if other.one is None else other.one)
    return ret

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    ret = StructuredVectorPairCombination()
    ret.pairs = [-pair for pair in self.pairs]
    ret.one = None if self.one is None else -self.one
    return ret

  def __sub__(self, other):
    return self.__add__(-other)

  def __rsub__(self, other):
    return self.__neg__().__add__(other)


class NamedVectorPairCombination(CoeffMap):
  def __init__(self):
    super(NamedVectorPairCombination, self).__init__()

  def copy(self):
    return NamedVectorPairCombination._from(self)

  def _from(other):
    v = NamedVectorPairCombination()
    if isinstance(other, int) or isinstance(other, str) or \
       isinstance(other, Expr) or isinstance(other, UnitVector) or \
       isinstance(other, SparseVector) or isinstance(other, PowerVector) or \
       isinstance(other, StructuredVector) or isinstance(other, StructuredVectorPair):
      return v.set("one", StructuredVectorPairCombination._from(other))
    if isinstance(other, StructuredVectorPairCombination):
      return v.set("one", other.copy())
    if isinstance(other, tuple) and isinstance(other[0], NamedVector) and \
       isinstance(other[1], NamedVector):
      return v.set(NamedVectorPair(other[0], other[1]), StructuredVector._from(1))
    if isinstance(other, tuple) and isinstance(other[0], NamedVectorPair) and \
       isinstance(other[1], StructuredVector):
      return v.set(other[0], other[1])
    if isinstance(other, tuple) and isinstance(other[0], NamedVectorPair) and \
       isinstance(other[1], SparseVector):
      return v.set(other[0], StructuredVector._from(other[1]))
    if isinstance(other, NamedVectorPair):
      return v.set(other, StructuredVector._from(1))
    if isinstance(other, NamedVectorPairCombination) or type(other) == CoeffMap:
      for key, value in other.items():
        v._dict[key] = value
      return v
    raise Exception(
        "Cannot convert %s to NamedVectorPairCombination" % (str(other)))

  def __add__(self, other):
    if not isinstance(other, NamedVectorPairCombination):
      other = NamedVectorPairCombination._from(other)

    ret = super(NamedVectorPairCombination, self).__add__(other)
    return NamedVectorPairCombination._from(ret)

  def __radd__(self, other):
    return self.__add__(other)

  def __neg__(self):
    return NamedVectorPairCombination._from(super(NamedVectorPairCombination, self).__neg__())

  def __sub__(self, other):
    return self.__add__(-other)

  def __rsub__(self, other):
    return self.__neg__().__add__(other)

  def generate_vector_combination(self, omega, coeff_manager):
    named_vector_structure_pairs = []
    structured_vector_pair_combination = None
    visited_vector_names = set()
    ret = RustBuilder()
    for key, vector_pair, coeff in self.key_keyed_coeffs():
      if key == "one":
        structured_vector_pair_combination = coeff
      elif vector_pair.u is not None and vector_pair.v is not None:
        v = get_named_vector("v")
        to_shift = Symbol(get_name("shiftlength"))
        if rust_pk(vector_pair.u) not in visited_vector_names:
          ret.append(rust_define_vector_domain_evaluations_dict(rust_pk(vector_pair.u))).end()
          visited_vector_names.add(rust_pk(vector_pair.u))
        if rust_pk(vector_pair.v) not in visited_vector_names:
          ret.append(rust_define_vector_domain_evaluations_dict(rust_pk(vector_pair.v))).end()
          visited_vector_names.add(rust_pk(vector_pair.v))
        ret.append(rust_define_vector_poly_mul_shift(
            v, rust_pk(vector_pair.u), rust_pk(vector_pair.v), omega, to_shift
        )).end()
        named_vector_structure_pairs.append((v, coeff.shift(-to_shift)))
      elif vector_pair.u is not None:
        v = get_named_vector("v")
        to_shift = Symbol(get_name("shiftlength"))
        ret.append(rust_define_vector_reverse_omega_shift(
            v, vector_pair.u, omega, to_shift
        )).end()
        named_vector_structure_pairs.append((v, coeff.shift(-to_shift)))
      elif vector_pair.v is not None:
        named_vector_structure_pairs.append((vector_pair.v, coeff))
      else:
        raise Exception("Invalid named vector pair")

    named_power_sparse_tuples = []
    vector_combination = VectorCombination()
    power_power_sparse_tuples = []
    for v, st in named_vector_structure_pairs:
      for key, p, coeff in st.key_keyed_coeffs():
        if key == "one":
          vector_combination += v * coeff
        else:
          named_power_sparse_tuples.append((v, p, coeff))

    if structured_vector_pair_combination is not None:
      if structured_vector_pair_combination.one is not None:
        vector_combination += structured_vector_pair_combination.one
      for structured_vector_pair in structured_vector_pair_combination.pairs:
        if structured_vector_pair.u is not None and \
           structured_vector_pair.v is not None:
          for left_key, left_p_coeff in structured_vector_pair.u.items():
            left_p, left_coeff = left_p_coeff
            for right_key, right_p_coeff in structured_vector_pair.v.items():
              right_p, right_coeff = right_p_coeff
              if left_key != "one" and right_key != "one":
                # convolution(left_coeff, right_coeff, omega)
                coeff = left_coeff * right_coeff
                power_power_sparse_tuples.append((left_p, right_p, coeff))
              elif left_key != "one":
                # convolution(left_p * left_coeff, right_coeff, omega)
                vector_combination += left_p * left_coeff * right_coeff
              elif right_key != "one":
                # convolution(left_coeff, right_coeff * right_p, omega)
                vector_combination += left_coeff * right_coeff * right_p
              else:
                # convolution(left_coeff, right_coeff, omega)
                vector_combination += left_coeff * right_coeff

    for v, p, s in named_power_sparse_tuples:
      vec = get_named_vector("v")
      base = coeff_manager.add(p.alpha)
      ret.append(rust_define_vector_power_mul(
          vec, rust_pk(v), rust(base, to_field=True), p.size
      )).end()
      vector_combination += vec * s

    for p1, p2, s in power_power_sparse_tuples:
      v = get_named_vector("v")
      base1 = coeff_manager.add(p1.alpha)
      base2 = coeff_manager.add(p2.alpha)
      ret.append(rust_define_power_power_mul(
          v, rust(base1, to_field=True), p1.size, rust(base2, to_field=True), p2.size)
      ).end()
      vector_combination += v * s

    return ret, vector_combination


def convolution(left, right, omega):
  if isinstance(left, VectorCombination) and isinstance(right, VectorCombination):
    ret = NamedVectorPairCombination()
    # Multiplying vector combinations, named vectors are combined to named vector pairs
    # structured vectors are combined to structured vector pairs
    # the coefficients are convoluted
    for left_key, left_vector_coeff in left.items():
      for right_key, right_vector_coeff in right.items():
        left_vector, left_coeff = left_vector_coeff
        right_vector, right_coeff = right_vector_coeff
        coeff = convolution(left_coeff, right_coeff, omega)
        if left_key == "one" and right_key == "one":
          ret += coeff
        elif left_key != "one" and right_key == "one":
          ret += (NamedVectorPair(left_vector, None), coeff)
        elif left_key == "one" and right_key != "one":
          ret += (NamedVectorPair(None, right_vector), coeff)
        else:
          ret += (NamedVectorPair(left_vector, right_vector), coeff)
    return ret

  if isinstance(left, VectorCombination):
    ret = NamedVectorPairCombination()
    for left_key, left_vector_coeff in left.items():
      left_vector, left_coeff = left_vector_coeff
      coeff = convolution(left_coeff, right, omega)
      if left_key == "one":
        ret += coeff
      else:
        ret += (NamedVectorPair(left_vector, None), coeff)
    return ret

  if isinstance(right, VectorCombination):
    ret = NamedVectorPairCombination()
    for right_key, right_vector_coeff in right.items():
      right_vector, right_coeff = right_vector_coeff
      coeff = convolution(left, right_coeff, omega)
      if left_key == "one":
        ret += coeff
      else:
        ret += (NamedVectorPair(None, right_vector), coeff)
    return ret

  if isinstance(left, StructuredVector) and isinstance(right, StructuredVector):
    return StructuredVectorPair(left.reverse_omega(omega), right)

  return left.reverse_omega(omega) * right
