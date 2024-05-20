from .symbol.names import get_name
from .symbol.poly import NamedVectorPolynomial
from .symbol.util import rust_pk_vk, rust_vk, get_rust_type, \
    rust_to_bytes_replacement
from .builder.latex import tex, LaTeXBuilder, Math, Enumerate, Itemize
from .builder.rust import *
from .piop import ProverSendPolynomials
from .pc_protocol import IndexerComputes, ProverComputes, \
    VerifierComputes, VerifierSendRandomnesses
from sympy import Symbol


class ZKSNARK(object):
  def __init__(self):
    self.indexer_computations = []
    self.prover_computations = []
    self.verifier_computations = []
    self.vk = []
    self.pk = []
    self.proof = []
    self.debug_mode = False
    register_rust_functions(self)

  def preprocess(self, latex_builder, rust_builder):
    self.indexer_computations.append(
        IndexerComputes(latex_builder, rust_builder, has_indexer=False))

  def preprocess_output_vk(self, expr):
    self.vk.append(expr)

  def preprocess_output_pk(self, expr):
    self.pk.append(expr)

  def prover_computes(self, latex_builder, rust_builder):
    if isinstance(latex_builder, str):
      raise Exception("latex_builder cannot be str: %s" % latex_builder)
    self.prover_computations.append(
        ProverComputes(latex_builder, rust_builder, False))

  def prover_computes_latex(self, latex_builder):
    self.prover_computes(latex_builder, RustBuilder())

  def prover_computes_rust(self, rust_builder):
    self.prover_computes(LaTeXBuilder(), rust_builder)

  def verifier_computes(self, latex_builder, rust_builder):
    self.verifier_computations.append(
        VerifierComputes(latex_builder, rust_builder, False))

  def verifier_computes_latex(self, latex_builder):
    self.verifier_computes(latex_builder, RustBuilder())

  def verifier_computes_rust(self, rust_builder):
    self.verifier_computes(LaTeXBuilder(), rust_builder)

  def prover_verifier_computes(self, latex_builder, rust_builder):
    self.prover_computes(latex_builder, rust_builder)
    self.verifier_computes(latex_builder, rust_builder)

  def prover_verifier_computes_latex(self, latex_builder):
    self.prover_computes_latex(latex_builder)
    self.verifier_computes_latex(latex_builder)

  def prover_verifier_computes_rust(self, rust_builder):
    self.prover_computes_rust(rust_builder)
    self.verifier_computes_rust(rust_builder)

  def dump_indexer(self):
    enum = Enumerate()
    for computation in self.indexer_computations:
      enum.append(computation.dumps())
    itemize = Itemize()
    itemize.append("$\\mathsf{pk}:=(%s)$" %
                   ",".join([tex(v) for v in self.vk]))
    itemize.append("$\\mathsf{vk}:=(%s)$" % ",".join(
        [tex(p) for p in self.pk] + [tex(v) for v in self.vk]))
    enum.append("Output\n" + itemize.dumps())
    return enum.dumps()

  def dump_indexer_rust(self):
    return "".join(
        [computation.dumpr() for computation in self.indexer_computations])

  def dump_prover(self):
    enum = Enumerate()
    for computation in self.prover_computations:
      enum.append(computation.dumps())
    enum.append("Output $\\pi:=\\left(%s\\right)$" %
                ",".join(tex(p) for p in self.proof))
    return enum.dumps()

  def dump_prover_rust(self):
    return "".join([computation.dumpr() for computation in self.prover_computations])

  def dump_verifier(self):
    enum = Enumerate()
    for computation in self.verifier_computations:
      enum.append(computation.dumps())
    return enum.dumps()

  def dump_proof_init(self):
    return ("\n" + " " * 8).join(["let %s = proof.%s;" % (rust(item), rust(item))
                                  for item in self.proof])

  def dump_verifier_rust(self):
    return self.dump_proof_init() + \
        "".join([computation.dumpr()
                 for computation in self.verifier_computations])

  def dump_definition(self, items):
    return "\n    ".join([
        "pub %s: %s," % (rust(item), get_rust_type(item))
        for item in items])

  def dump_construction(self, items):
    return ("\n" + " " * 12).join([
        "%s: %s," % (rust(item), rust(item))
        for item in items])

  def dump_vk_definition(self):
    return self.dump_definition(self.vk)

  def dump_pk_definition(self):
    return self.dump_definition(self.pk)

  def dump_proof_definition(self):
    return self.dump_definition(self.proof)

  def dump_vk_construction(self):
    return self.dump_construction(self.vk)

  def dump_pk_construction(self):
    return self.dump_construction(self.pk)

  def dump_proof_construction(self):
    return self.dump_construction(self.proof)


class KZGQueryInfo(object):
  def __init__(self):
    self.comm = None
    self.name = None
    self.poly = None
    self.rust_comm = None
    self.rust_name = None
    self.rust_poly = None


class KZGPointInfo(object):
  def __init__(self):
    self.proof_symbol = None
    self.point = None
    self.queries_info = []

  def _add_query(self, name, poly):
    query = KZGQueryInfo()
    query.comm = poly.to_comm()
    query.name = name
    query.poly = poly.dumps()
    query.rust_poly = rust(poly)
    query.rust_comm = rust_vk(poly.to_comm())
    query.rust_name = rust_zero() if name == 0 else name
    self.queries_info.append(query)

  def add_query(self, query):
    self._add_query(query.name, query.poly)


class KZGInfo(object):
  def __init__(self):
    self.points_info = []

  def generate_computations_latex(self):
    proof_str = ",".join(tex(p.proof_symbol) for p in self.points_info)
    open_computation = Math("\\left(%s\\right)" % proof_str)
    open_computation.assign("\\mathsf{open}")
    lists = "\\\\\n".join([("\\{%s\\}," % (
                            ",".join([("%s\\left(%s,%s,%s\\right)" %
                                       ("\\\\\n" if i % 3 == 0 and i > 0 else "",
                                        tex(query.comm), tex(query.name), tex(query.poly)))
                                      for i, query in enumerate(point_info.queries_info)])
                            )) for point_info in self.points_info])
    points = "\\left\\{%s\\right\\}" % (
        ",".join(tex(point_info.point) for point_info in self.points_info))
    array = "\\begin{array}{l}\n%s\\\\\n%s\n\\end{array}" % (lists, points)
    open_computation.paren(array)

    array = "\\begin{array}{l}\n%s\\\\\n%s\n\\left\\{%s\\right\\},[x]_2\\end{array}" \
            % (lists, points, proof_str)
    verify_computation = Math("\\mathsf{vrfy}").paren(array).equals(1)
    return open_computation, verify_computation

  def generate_computations_rust(self):
    fcomms = [q.rust_comm for q in self.points_info[0].queries_info]
    gcomms = [q.rust_comm for q in self.points_info[1].queries_info]
    fnames = [q.rust_name for q in self.points_info[0].queries_info]
    gnames = [q.rust_name for q in self.points_info[1].queries_info]
    fpolys = [q.rust_poly for q in self.points_info[0].queries_info]
    gpolys = [q.rust_poly for q in self.points_info[1].queries_info]

    open_computation_rust = RustBuilder()
    open_computation_rust.append(rust_define("fs", rust_vec(fpolys))).end()
    open_computation_rust.append(rust_define("gs", rust_vec(gpolys))).end()

    compute_zs = RustBuilder()
    compute_zs.append(rust_define("z1", self.points_info[0].point)).end()
    compute_zs.append(rust_define("z2", self.points_info[1].point)).end()

    verify_computation_rust = RustBuilder()
    verify_computation_rust.append(rust_define(
        "f_commitments", rust_vec(fcomms))).end()
    verify_computation_rust.append(rust_define(
        "g_commitments", rust_vec(gcomms))).end()
    verify_computation_rust.append(
        rust_define("f_values", rust_vec(fnames))).end()
    verify_computation_rust.append(
        rust_define("g_values", rust_vec(gnames))).end()
    return open_computation_rust, verify_computation_rust, compute_zs


class ZKSNARKFromPIOPExecKZG(ZKSNARK):
  def __init__(self, piopexec):
    super().__init__()
    self.debug_mode = piopexec.debug_mode
    self.process_piopexec(piopexec)

  def _process_indexer_polynomial(self, poly, degree, rust_degree):
    self.preprocess(Math(poly.to_comm()).assign(
        "\\mathsf{com}\\left(%s, \\mathsf{srs}\\right)" % poly.dumps()),
        rust_line_define_commit_vector(poly.to_comm(), poly.vector, rust_degree))
    self.preprocess_output_vk(poly.to_comm())
    self.transcript.append(poly.to_comm())

  def _process_piopexec_indexer(self, piopexec):
    for preprocess in piopexec.preprocessings:
      self.preprocess(preprocess.latex_builder, preprocess.rust_builder)

    if piopexec.indexer_polynomials is not None:
      for poly, degree, rust_degree in piopexec.indexer_polynomials.polynomials:
        self._process_indexer_polynomial(poly, degree, rust_degree)

    for p in piopexec.indexer_output_pk:
      self.preprocess_output_pk(p)

    for v in piopexec.indexer_output_vk:
      self.preprocess_output_vk(v)
      self.transcript.append(v)

  def _generate_randomness_from_hashes(self, names):
    for i, r in enumerate(names):
      self.prover_verifier_computes_latex(
          Math(r).assign("\\mathsf{H}_{%d}(%s)"
                         % (i+1, ",".join([tex(x) for x in self.transcript]))))
      self.prover_rust_get_randomness_from_hash(
          r, to_field(i+1), *[
            rust_pk_vk(rust_to_bytes_replacement(x)) for x in self.transcript])
      self.verifier_rust_get_randomness_from_hash(
          r, to_field(i+1), *[
            rust_vk(rust_to_bytes_replacement(x)) for x in self.transcript])

  def _process_prover_send_polynomials(self, polynomials):
    for poly, degree, rust_degree in polynomials:
      if not isinstance(poly, NamedVectorPolynomial):
        raise Exception(
            "Unrecognized polynomial type: %s" % type(poly))
      self.prover_computes_latex(Math(poly.to_comm()).assign(
          "\\mathsf{com}\\left(%s, \\mathsf{srs}\\right)"
          % (poly.dumps())))
      self.prover_rust_define_commit_vector_with_pk(
          poly.to_comm(), poly.vector, rust_degree)
      self.transcript.append(poly.to_comm())
      self.proof.append(poly.to_comm())

  def _process_piopexec_interactions(self, piopexec):
    for interaction in piopexec.interactions:
      if isinstance(interaction, ProverComputes):
        self.prover_computes(
            interaction.latex_builder, interaction.rust_builder)
      elif isinstance(interaction, VerifierComputes):
        self.prover_computes(
            interaction.latex_builder, interaction.rust_builder)
        self.verifier_computes(
            interaction.latex_builder, interaction.rust_builder)
      elif isinstance(interaction, VerifierSendRandomnesses):
        self._generate_randomness_from_hashes(interaction.names)
      if isinstance(interaction, ProverSendPolynomials):
        self._process_prover_send_polynomials(interaction.polynomials)

  def _process_piopexec_computes_query_results(self, piopexec):
    self.prover_computes_latex(Math(",".join(["%s:=%s" %
                                              (tex(query.name), tex(
                                                  query.poly.dumps_var(query.point)))
                                              for query in piopexec.eval_queries])))
    self.proof += [query.name for query in piopexec.eval_queries]

  def _process_polynomial_combination(self, piopexec):
    for poly_combine in piopexec.poly_combines:
      computes = poly_combine.dump_computes()
      for item in computes.coefficient_items:
        self.prover_computes_latex(item)
        self.verifier_computes_latex(item)
      for rust_item in computes.coefficient_rust_items:
        self.prover_computes_rust(rust_item)
        self.verifier_computes_rust(rust_item)
      for item in computes.poly_latex_items:
        self.prover_computes_latex(item)
      for item in computes.poly_rust_items:
        self.prover_computes_rust(item)
      for item in computes.commit_latex_items:
        self.prover_computes_latex(item)
        self.verifier_computes_latex(item)
      for item in computes.commit_rust_items:
        self.prover_computes_rust(item)
        self.verifier_computes_rust(item)

      self.transcript.append(poly_combine.poly.to_comm())

      if piopexec.debug_mode:
        self.prover_rust_assert_eq(
            poly_combine.poly.to_comm(),
            rust_commit_vector_with_pk(
                poly_combine.poly.to_vec(),
                poly_combine.length))

  def _generate_points_poly_dict(self, queries):
    points_poly_dict = {}
    for query in queries:
      self.prover_rust_define_poly_from_vec(query.poly, query.poly.to_vec())
      key = tex(query.point)
      if key not in points_poly_dict:
        points_poly_dict[key] = []
      points_poly_dict[key].append(query)
    return points_poly_dict

  def _parepare_for_kzg_open(self, piopexec, points_poly_dict, transcript):
    kzginfo = KZGInfo()
    for key, queries in points_poly_dict.items():
      point = queries[0].point
      kzgpoint_info = KZGPointInfo()
      kzginfo.points_info.append(kzgpoint_info)
      kzgpoint_info.proof_symbol = Symbol(get_name("W"))
      kzgpoint_info.point = point
      transcript.append(point)
      for query in queries:
        kzgpoint_info.add_query(query)
        kzgquery_info = kzgpoint_info.queries_info[-1]
        if not isinstance(query.name, int):
          transcript.append(query.name)
        else:
          # Only make this check when the query result is an expected constant
          self.prover_rust_check_poly_eval(
              kzgquery_info.rust_poly,
              kzgpoint_info.point,
              kzgquery_info.rust_name,
              "g does not evaluate to 0 at z")

    return kzginfo

  def _check_naive_g_evals_to_zero(self, piopexec):
    if piopexec.debug_mode:
      z = [query.point for query in piopexec.eval_checks if query.name == 0][0]
      naive_g = piopexec.naive_g
      # Note that naive_g is not the same as g, because naive_g does not decompose
      # the vector combination and replace all the coefficients with their evaluation
      # at z. But naive_g should evaluate to zero
      self.prover_rust_define_poly_from_vec(
          naive_g.to_named_vector_poly(), naive_g)
      self.prover_rust_check_poly_eval(
          naive_g.to_named_vector_poly(),
          z,
          rust_zero(),
          "naive g does not evaluate to 0 at z")

  def _generate_open_and_verify_computations(self, piopexec):
    points_poly_dict = self._generate_points_poly_dict(
        piopexec.eval_queries + piopexec.eval_checks)
    kzginfo = self._parepare_for_kzg_open(piopexec, points_poly_dict, self.transcript)

    self.proof += [p.proof_symbol for p in kzginfo.points_info]
    open_computation, verify_computation = \
        kzginfo.generate_computations_latex()
    open_computation_rust, verify_computation_rust, compute_zs = \
        kzginfo.generate_computations_rust()

    compute_rand_xi = RustBuilder()
    compute_rand_xi.append(rust_line_get_randomness_from_hash(
        "rand_xi", to_field(1),
        *[rust_vk(rust_to_bytes_replacement(x)) for x in self.transcript]))
    compute_rand_xi.append(rust_line_get_randomness_from_hash(
        "rand_xi_2", to_field(2),
        *[rust_vk(rust_to_bytes_replacement(x)) for x in self.transcript]))

    self.prover_computes(open_computation, open_computation_rust)
    self.prover_computes_rust(compute_rand_xi)
    self.prover_computes_rust(compute_zs)
    self.verifier_computes_rust(compute_zs)
    self.verifier_computes_rust(compute_rand_xi)
    self.verifier_computes(verify_computation, verify_computation_rust)

  def process_piopexec(self, piopexec):
    self.transcript = [x for x in piopexec.verifier_inputs]
    self._process_piopexec_indexer(piopexec)
    self._process_piopexec_interactions(piopexec)
    self._process_piopexec_computes_query_results(piopexec)
    self._process_polynomial_combination(piopexec)
    self._check_naive_g_evals_to_zero(piopexec)
    self._generate_open_and_verify_computations(piopexec)
