"""
The coefficients can be very length and complex. To avoid computing them
over and over again for every index, we can compute them once and for all.
So we replace each coefficient by a symbol, and maintain a dictionary for
the map between symbols and coefficients
"""
from .names import get_name
from sympy import Symbol, srepr, sympify, simplify
from ..builder.latex import tex
from ..builder.rust import rust

class CoeffManager(object):
  def __init__(self):
    self._dict = {}
    """
    Sometimes, new coefficient-expression relations may be added by some subprocedure,
    these relations should be processed to generate rust code. So the subprocedure
    relations are temporarily stored and processed when the main execution recorder
    is back into control.
    """
    self._to_be_processed = []

  def add(self, expr):
    expr = simplify(sympify(expr))
    if expr == 1 or expr == 0 or expr == -1 or isinstance(expr, Symbol):
      return expr

    if rust(expr).startswith("1"):
      """
      This is a hack. If the expression starts with one, but is not
      a power, then it contains the field element "one", but unfortunately
      use the integer to represent it. In this case, force this expression
      into a string while transforming all the integers into field elements
      """
      expr = rust(expr, to_field=True)

    key = tex(expr)
    if key in self._dict:
      return self._dict[key]
    sym = Symbol(get_name("c"))
    self._dict[key] = sym
    self._to_be_processed.append(expr)
    return sym

  def has(self, expr):
    return tex(expr) in self._dict

  def get(self, expr):
    key = tex(expr)
    return self._dict[key]

  def process_coeffs(self):
    ret = [(self.get(expr), rust(expr)) for expr in self._to_be_processed]
    self._to_be_processed = []
    return ret
