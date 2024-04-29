from .builder.latex import tex, Math, LaTeXBuilder
from .builder.rust import *
from .symbol.names import get_name
from .symbol.coeff_manager import CoeffManager
from sympy import Symbol


class Computes(object):
  def __init__(self, latex_builder, rust_builder, owner=None):
    self.latex_builder = latex_builder
    self.rust_builder = rust_builder
    self.owner = owner

  def dumps(self):
    ret = tex(self.latex_builder)
    if self.owner is not None:
      ret = "\\%s computes %s" % (self.owner, ret)
    return ret

  def dumpr(self):
    return rust(self.rust_builder)


class IndexerComputes(Computes):
  def __init__(self, latex_builder, rust_builder, has_indexer=True):
    super().__init__(latex_builder, rust_builder,
                     "indexer" if has_indexer else None)


class ProverComputes(Computes):
  def __init__(self, latex_builder, rust_builder, has_prover=True):
    super().__init__(latex_builder, rust_builder,
                     "prover" if has_prover else None)


class VerifierComputes(Computes):
  def __init__(self, latex_builder, rust_builder, has_verifier=True):
    super().__init__(latex_builder, rust_builder,
                     "verifier" if has_verifier else None)


class VerifierSendRandomnesses(object):
  def __init__(self, *args):
    self.names = args

  def add_randomnesses(self, *names):
    self.names += names

  def dumps(self):
    return "\\verifier sends %s to \\prover" % \
           Math(",".join([tex(name) for name in self.names])) \
           .sample(Fstar).dumps()


class InvokeSubprotocol(object):
  def __init__(self, name, *args):
    self.args = args
    self.name = name

  def dumps(self):
    return "\\prover and \\verifier invokes protocol " \
        "$\\mathsf{%s}$ with inputs %s" % \
           (self.name, ", ".join(["$%s$" % tex(arg) for arg in self.args]))


class IndexerInvokeSubprotocol(object):
  def __init__(self, name, *args):
    self.args = args
    self.name = name

  def dumps(self):
    return "\\indexer invokes the indexer of protocol " \
        "$\\mathsf{%s}$ with inputs %s" % \
           (self.name, ", ".join(["$%s$" % tex(arg) for arg in self.args]))


class PublicCoinProtocolExecution(object):
  def __init__(self):
    self.prover_inputs = []
    self.verifier_inputs = []
    self.preprocessings = []
    self.indexer_output_pk = []
    self.indexer_output_vk = []
    self.interactions = []
    register_rust_functions(self)
    self.coeff_manager = CoeffManager()

  def redefine_coeff(self, expr):
    if self.coeff_manager.has(expr):
      return self.coeff_manager.get(expr)
    sym = self.coeff_manager.set(expr)
    self.process_redefine_coeffs()
    return sym

  def process_redefine_coeffs(self):
    for sym, expr in self.coeff_manager.process_coeffs():
      self.prover_computes_rust(rust_line_define(sym, expr), redefine_coeff=False)

  def input_instance(self, arg):
    self.verifier_inputs.append(arg)
    self.prover_inputs.append(arg)

  def input_witness(self, arg):
    self.prover_inputs.append(arg)

  def preprocess(self, latex_builder, rust_builder):
    self.preprocessings.append(
        IndexerComputes(latex_builder, rust_builder))

  def preprocess_rust(self, rust_builder):
    self.preprocess(LaTeXBuilder(), rust_builder)

  def preprocess_latex(self, latex_builder):
    self.preprocess(latex_builder, RustBuilder())

  def preprocess_output_pk(self, expr):
    self.indexer_output_pk.append(expr)

  def preprocess_output_vk(self, expr):
    self.indexer_output_vk.append(expr)

  def prover_computes(self, latex_builder, rust_builder):
    self.interactions.append(ProverComputes(latex_builder, rust_builder))

  def prover_computes_latex(self, latex_builder):
    self.prover_computes(latex_builder, RustBuilder())

  def prover_computes_rust(self, rust_builder, redefine_coeff=True):
    if redefine_coeff:
      self.process_redefine_coeffs()
    self.prover_computes(LaTeXBuilder(), rust_builder)

  def prover_redefine_symbol_rust(self, s, name):
    new_s = Symbol(get_name(name))
    self.prover_rust_define(new_s, s)
    return new_s

  def verifier_computes(self, latex_builder, rust_builder):
    self.interactions.append(VerifierComputes(latex_builder, rust_builder))

  def verifier_computes_latex(self, latex_builder):
    self.verifier_computes(latex_builder, RustBuilder())

  def verifier_computes_rust(self, rust_builder):
    self.verifier_computes(LaTeXBuilder(), rust_builder)

  def verifier_redefine_symbol_rust(self, s, name, positive=False):
    if positive:
      new_s = Symbol(get_name(name))
    else:
      new_s = Symbol(get_name(name), positive=True)
    self.verifier_computes_rust(rust_line_define(new_s, s))
    return new_s

  def invoke_subprotocol(self, name, *args):
    self.interactions.append(InvokeSubprotocol(name, *args))

  def verifier_send_randomness(self, *args):
    # If the verifier already sent some randomnesses in the last step,
    # this simply appends to the randomnesses
    # args should be Symbol
    if len(self.interactions) > 0 and \
            isinstance(self.interactions[-1], VerifierSendRandomnesses):
      self.interactions[-1].add_randomnesses(*args)
    else:
      self.interactions.append(VerifierSendRandomnesses(*args))

  def verifier_generate_and_send_rand(self, name):
    ret = Symbol(get_name(name))
    self.verifier_send_randomness(ret)
    return ret

