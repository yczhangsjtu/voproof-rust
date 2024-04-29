from ..compiler.builder.rust import *
from .quadpoly import QuadraticPolynomial, MultipleQuadraticPolynomials


class RAMStepCircuit(object):
  """
  This is the base class (or interface) for the stepping function of a RAM.
  For any stepping function, we should be able to produced a quadratic
  polynomial that verifies the input-output pairs of this function. This is
  required to generate the VO protocol for the RAM
  """

  def __init__(self):
    raise Exception("Should not be invoked directly")

  def dump_quadratic_polynomial(self):
    raise Exception("Should not be invoked directly")

  def dump_variable_names(self):
    raise Exception("Should not be invoked directly")


class RISCCircuit(RAMStepCircuit):
  """
  This is the step function for the RISC architecture designed in the VORAM
  paper.
  """

  def __init__(self):
    self.olda = "olda"
    self.oldb = "oldb"
    self.oldpc = "oldpc"
    self.oldmode = "oldmode"
    self.newa = "newa"
    self.newb = "newb"
    self.newpc = "newpc"
    self.newmode = "newmode"
    self.roval = "roval"
    self.rwval = "rwval"
    self.op = "op"
    self.roaddr = "roaddr"
    self.rwaddr = "rwaddr"
    self.wval = "wval"

  def dump_quadratic_polynomial(self):
    ret = MultipleQuadraticPolynomials()
    return ret
