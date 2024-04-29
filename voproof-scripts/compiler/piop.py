from .pc_protocol import PublicCoinProtocolExecution
from .symbol.util import rust_vk
from .symbol.vector import list_sum_to_rust_map
from .builder.latex import tex, LaTeXBuilder, Enumerate, Itemize, Math
from .builder.rust import *


class SendPolynomials(object):
  def __init__(self, sender, polynomial, degree, rust_degree=None):
    rust_degree = degree if rust_degree is None else rust_degree
    self.sender = sender
    self.polynomials = [(polynomial, degree, rust_degree)]

  def __len__(self):
    return len(self.polynomials)

  def add_polynomial(self, polynomial, degree, rust_degree=None):
    rust_degree = degree if rust_degree is None else rust_degree
    self.polynomials.append((polynomial, degree, rust_degree))

  def dumps(self):
    return "\\%s sends %s to \\verifier" % \
        (self.sender, ", ".join(["$[%s]$ of degree $%s$" % (p.dumps(), tex(degree-1))
                                 for p, degree, rust_degree in self.polynomials]))


class ProverSendPolynomials(SendPolynomials):
  def __init__(self, polynomial, degree, rust_degree):
    super().__init__(
        "prover", polynomial, degree, rust_degree)


class IndexerSendPolynomials(SendPolynomials):
  def __init__(self, polynomial, degree, rust_degree):
    super().__init__(
        "indexer", polynomial, degree, rust_degree)


class EvalQuery(object):
  # name = poly(point)
  def __init__(self, name, point, poly):
    self.point = point
    self.poly = poly
    self.name = name

  def dumps(self):
    return "\\verifier queries $[%s]$ at point $%s$ to obtain $%s$" \
           % (self.poly.dumps(), tex(self.point), tex(self.name))

  def dumps_check(self):
    return "\\verifier queries $[%s]$ at point $%s$ and checks if the response is $%s$" \
           % (self.poly.dumps(), tex(self.point), tex(self.name))


class CombinationCoeffBuilder(object):
  def __init__(self, poly, coeff, latex_builder, rust_builder, shifts=0):
    """The coeff here must be symbol"""
    self.poly = poly
    self.coeff = coeff
    self.latex_builder = latex_builder
    self.rust_builder = rust_builder
    self.shifts = shifts

  def transform_lists_to_builders(self, alpha):
    """
    Assume that the latex builder and rust builder are currently lists
    Transform them into Itemize() and rust_define_sum respectively
    """
    self.latex_builder = LaTeXBuilder().start_math().append(self.coeff) \
        .assign().end_math().space("the sum of:") \
        .append(Itemize([Math(item) for item in self.latex_builder])) \
        if len(self.latex_builder) > 1 else \
        Math(self.coeff).assign(self.latex_builder[0])

    self.rust_builder = rust_line_define(
        self.coeff, list_sum_to_rust_map(self.rust_builder, collect_symbols=alpha))


class CombinePolynomialComputes(object):
  def __init__(self):
    self.coefficient_items = []
    self.coefficient_rust_items = []
    self.oracle_items = []
    self.poly_latex_items = []
    self.poly_rust_items = []
    self.commit_latex_items = []
    self.commit_rust_items = []


class CombinePolynomial(object):
  def __init__(self, poly, coeff_builders, length):
    self.poly = poly
    self.coeff_builders = coeff_builders
    self.length = length

  def dump_computes(self):
    computes = CombinePolynomialComputes()
    oracle_sum_items, poly_sum_items, commit_sum_items = [], [], []
    poly_sum_rust_items, commit_sum_rust_items = [], []
    latex_one, rust_const = None, None

    for key, coeff_builder in self.coeff_builders.items():
      computes.coefficient_items.append(coeff_builder.latex_builder)
      computes.coefficient_rust_items.append(coeff_builder.rust_builder)
      if key == "one":
        latex_one = latex(coeff_builder.coeff)
        rust_const = rust(coeff_builder.coeff)
        continue

      oracle_sum_items.append("%s\\cdot [%s]" % (
          latex(coeff_builder.coeff), coeff_builder.poly.dumps()))
      commit_sum_items.append("%s\\cdot %s" % (
          latex(coeff_builder.coeff), coeff_builder.poly.to_comm()))
      commit_sum_rust_items.append(rust_vk(coeff_builder.poly.to_comm()))
      commit_sum_rust_items.append(rust(coeff_builder.coeff))
      poly_sum_items.append("%s\\cdot %s" % (
          latex(coeff_builder.coeff), coeff_builder.poly.dumps()))
      poly_sum_rust_items.append(rust(coeff_builder.coeff))
      poly_sum_rust_items.append(
          coeff_builder.poly.dumpr_at_index(sym_i - coeff_builder.shifts, None))

    computes.poly_rust_items.append(
        rust_line_define_vec_mut(self.poly.to_vec(), rust_expression_vector_i(
            rust_linear_combination_base_zero(poly_sum_rust_items),
            self.length)))

    if "one" in self.coeff_builders:
      coeff = self.coeff_builders["one"].coeff
      latex_one = latex(coeff)
      oracle_sum_items.append(latex_one)
      poly_sum_items.append(latex_one)
      commit_sum_items.append("%s\\cdot \\mathsf{com}(1)" % latex_one)

      rust_const = rust(coeff)
      computes.poly_rust_items.append(
          rust_line_add_to_first_item(self.poly.to_vec(), rust_const))
      computes.commit_rust_items.append(
          rust_line_define_commitment_linear_combination(
              self.poly.to_comm(), "vk", rust_const, *commit_sum_rust_items))
    else:
      computes.commit_rust_items.append(
          rust_line_define_commitment_linear_combination_no_one(
              self.poly.to_comm(), *commit_sum_rust_items))

    computes.oracle_items.append(
        Math("[%s]" % self.poly.dumps()).assign("+".join(oracle_sum_items)))
    computes.poly_latex_items.append(
        Math("%s" % self.poly.dumps()).assign("+".join(poly_sum_items)))
    computes.commit_latex_items.append(
        Math("%s" % self.poly.to_comm()).assign("+".join(commit_sum_items)))

    return computes


class PIOPExecution(PublicCoinProtocolExecution):
  def __init__(self, *args):
    super().__init__()
    self.args = args
    self.indexer_polynomials = None
    self.eval_queries = []
    self.poly_combines = []
    self.eval_checks = []
    self.prover_polynomials = []
    self.distinct_points = set()
    self.debug_mode = False
    self._symbol_dict = {}
    self._power_poly_dict = {}
    self._auto_vector_dict = {}

  def preprocess_polynomial(self, polynomial, degree, rust_degree=None):
    polynomial._is_preprocessed = True
    if self.indexer_polynomials is not None:
      self.indexer_polynomials.add_polynomial(
          polynomial, degree, rust_degree)
    else:
      self.indexer_polynomials = IndexerSendPolynomials(
          polynomial, degree, rust_degree)

  def prover_send_polynomial(self, polynomial, degree, rust_degree=None):
    if len(self.interactions) > 0 and \
            isinstance(self.interactions[-1], ProverSendPolynomials):
      self.interactions[-1].add_polynomial(
          polynomial, degree, rust_degree)
    else:
      self.interactions.append(ProverSendPolynomials(
          polynomial, degree, rust_degree))

    self.prover_polynomials.append(
        ProverSendPolynomials(polynomial, degree, rust_degree))

  def eval_query(self, name, point, poly):
    self.eval_queries.append(EvalQuery(name, point, poly))
    self.distinct_points.add(tex(point))

  def eval_query_for_possibly_local_poly(self, name, point, poly, vec, size):
    if not vec.local_evaluate:
      self.eval_query(name, point, poly)
      self.prover_rust_define_eval_vector_expression_i(
          name, point, vec.dumpr_at_index(sym_i, self.coeff_manager), size)
    else:
      self.verifier_computes_latex(Math(name).assign(poly.dumps_var(point)))
      self.verifier_rust_define(name, vec.hint_computation(point))

  def combine_polynomial(self, poly, coeff_latex_builders, length):
    self.poly_combines.append(CombinePolynomial(
        poly, coeff_latex_builders, length))

  def eval_check(self, left, point, poly):
    # eval_check is handled differently from eval_query
    # verifier uses eval_query to get the value of f(z)
    # but uses eval_check to check if some known y =? f(z)
    # when compiled to zkSNARK, for each eval query, the prover
    # needs to send the query response y to the verifier
    # before they run the evaluation protocol
    # but for each eval check, the prover doesn't need to
    # thus saving a field element in the zkSNARK proof
    self.eval_checks.append(EvalQuery(left, point, poly))
    self.distinct_points.add(tex(point))

  def _format_string(*args):
    if not isinstance(args[0], str):
      raise Exception("The first argument must be string")
    return ('"%s"' % args[0],) + tuple(rust(arg) for arg in args[1:])

  def pp_debug(self, *args):
    if self.debug_mode:
      self.preprocess_rust(
          rust_builder_macro(
              "println",
              *PIOPExecution._format_string(*args)
          ).end()
      )

  def prover_debug(self, *args):
    if self.debug_mode:
      self.prover_computes_rust(
          rust_builder_macro(
              "println",
              *PIOPExecution._format_string(*args)
          ).end()
      )

  def dumps(self):
    ret = Enumerate()
    for pp in self.preprocessings:
      ret.append(pp.dumps())
    ret.append(self.indexer_polynomials.dumps())
    if len(self.indexer_output_vk) > 0:
      ret.append("\\indexer sends $%s$ to \\verifier"
                 % ",".join([tex(v) for v in self.indexer_output_vk]))
    if len(self.indexer_output_pk) > 0:
      ret.append("\\indexer sends $%s$ to \\prover"
                 % ",".join([tex(p) for p in self.indexer_output_pk]))
    for interaction in self.interactions:
      ret.append(interaction.dumps())
    for query in self.eval_queries:
      ret.append(query.dumps())
    for polycom in self.poly_combines:
      computes = polycom.dump_computes()
      ret.append(VerifierComputes(
          computes.coefficient_items, RustBuilder()).dumps())
      ret.append(VerifierComputes(
          computes.oracle_items, RustBuilder()).dumps())
    for query in self.eval_checks:
      ret.append(query.dumps_check())
    return ret.dumps()

