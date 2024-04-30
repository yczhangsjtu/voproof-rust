from .pc_protocol import ProverComputes, VerifierComputes, \
    VerifierSendRandomnesses
from .vo_protocol import VOProtocolExecution, ProverSubmitVectors, VOQuerySide
from .piop import CombinationCoeffBuilder
from .symbol.vector import NamedVector, PowerVector, UnitVector, \
    get_named_vector, VectorCombination, convolution, NamedVectorPairCombination, \
    vec_lists_dump_at_index_then_inner_product
from .symbol.names import get_name
from .symbol.poly import get_named_polynomial
from .symbol.coeff_manager import CoeffManager
from .builder.latex import LaTeXBuilder, AccumulationVector, Math, Itemize, \
    add_paren_if_add, tex
from .builder.rust import *
from sympy import Symbol, Integer, UnevaluatedExpr, Max, simplify
from sympy.abc import X
from itertools import chain

F = Symbol("\\mathbb{F}")
Fstar = Symbol("\\mathbb{F}^*")
sym_i = Symbol("i", positive=True)


class ExtendedHadamard(object):
  def __init__(self, alpha):
    self.items = []
    self.alpha = alpha
    self.alpha_power = Integer(1)
    self.ignore_in_t = set()
    self.beta = None
    self.beta_power = None

  def ignore_index(self, index):
    self.ignore_in_t.add(index)

  def ignore_last(self):
    self.ignore_index(len(self.items) - 1)

  def ignored(self, index):
    return index in self.ignore_in_t

  def append(self, right):
    self.items.append(right)

  def add_side(self, side):
    if self.beta_power is None:
      self.append(self.alpha_power * side)
    else:
      self.append(self.alpha_power * self.beta_power * side)

  def add_side_raw(self, side):
    self.append(side)

  def start_adding_sides(self, beta=None):
    self.beta = beta
    self.beta_power = Integer(1) if beta is not None else None

  def end_adding_sides(self):
    self.alpha_power = self.alpha_power * self.alpha
    self.beta = None
    self.beta_power = None

  def clear_beta(self):
    self.beta = None
    self.beta_power = None

  def next_beta(self):
    self.beta_power = self.beta_power * self.beta

  def add_hadamard_query(self, query):
    """
    vec{a} circ vec{b} - vec{c} circ vec{d}
    the right side might be zero (one sided)
    """
    self.start_adding_sides()

    self.add_side(query.left_side)
    ret = (self.alpha_power, self.items[-1], None)
    if not query.one_sided:
      self.add_side(-query.right_side)
      ret = (self.alpha_power, self.items[-1], self.items[-2])
    elif query.left_side.at_least_one_operand_is_structured():
      """
      One sided, and one of the operand is only a structured vector,
      then no need to include this vector in t, because the structured
      vector will be all zero outside the n-window
      """
      self.ignore_last()

    self.end_adding_sides()
    return ret

  def dump_itemize(self):
    return Itemize().append([Math(side._dumps("circ"))
                             for i, side in enumerate(self.items)
                             if not self.ignored(i)])

  def dump_linear_combination_at_i(self, vector_size, coeff_manager):
    """
    Because the first n elements of t should be zero, we only
    care about the vector starting from n+1
    """
    return vec_lists_dump_at_index_then_inner_product([
        (side.a, side.b)
        for i, side in enumerate(self.items)
        if not self.ignored(i)
    ], simplify(sym_i + vector_size), coeff_manager, collect_symbols=self.alpha)

    """
    rust_linear_combination_base_zero(*[
        operand.dumpr_at_index(simplify(sym_i + vector_size))
        for i, side in enumerate(self.items)
        for operand in [side.a, side.b]
        if not self.ignored(i)
    ])
    """

  def dump_product_items(self, omega, vec_to_poly_dict):
    hx_items = Itemize()
    for side in self.items:
      hx_items.append(side.dump_product_items(omega, vec_to_poly_dict))
    return hx_items

  def named_vecs_in_left_operands(self):
    ret = {}
    for had in self.items:
      if isinstance(had.a, NamedVector):
        ret[had.a.key()] = had.a
      elif isinstance(had.a, VectorCombination):
        had.a.dump_named_vectors(ret)
    return ret

  def dump_named_vectors(self):
    ret = {}
    for i, side in enumerate(self.items):
      a = VectorCombination._from(side.a)
      b = VectorCombination._from(side.b)
      for vec in chain(a.keyeds(), b.keyeds()):
        if isinstance(vec, NamedVector):
          ret[vec.key()] = vec
    return list(ret.values())

  def generate_hx_vector_pair_combination(self, omega):
    hx_vector_combination = NamedVectorPairCombination()
    for i, side in enumerate(self.items):
      a = VectorCombination._from(side.a)
      b = VectorCombination._from(side.b)
      atimesb = convolution(a, b, omega)
      hx_vector_combination += atimesb
    return hx_vector_combination

  def generate_hx_vector_combination(self, omega, coeff_manager):
    return self.generate_hx_vector_pair_combination(omega) \
        .generate_vector_combination(omega, coeff_manager)

  def dump_hz_rust(self, z0, z, size, coeff_manager):
    lc = rust_linear_combination_base_zero()
    for had in self.items:
      lc.append(rust_eval_vector_expression_i(
          z0, VectorCombination._from(had.a).dumpr_at_index(sym_i, coeff_manager), size))
      lc.append(rust_eval_vector_expression_i(
          z, VectorCombination._from(had.b).dumpr_at_index(sym_i, coeff_manager), size))
    return lc


class PIOPFromVOProtocol(object):
  def __init__(self, vo, vector_size, degree_bound):
    self.vo = vo
    self.vector_size = vector_size
    self.degree_bound = degree_bound
    self.debug_mode = False

  def debug(self, info):
    if self.debug_mode:
      print(info)

  def preprocess(self, piopexec):
    voexec = VOProtocolExecution(self.vector_size)
    vec_to_poly_dict = {}
    self.vo.preprocess_with_prestored_args(voexec)
    piopexec.debug_mode = self.debug_mode
    piopexec.degree_bound = self.degree_bound

    for pp in voexec.preprocessings:
      piopexec.preprocess(pp.latex_builder, pp.rust_builder)
    for vector, size, _ in voexec.indexer_vectors.vectors:
      poly = vector.to_named_vector_poly()
      piopexec.preprocess_polynomial(poly, size)
      vec_to_poly_dict[vector.key()] = poly
      piopexec.pp_debug(
          "vector %s of length {} = \n[{}]" % rust(vector),
          "%s.len()" % rust(vector),
          rust_fmt_ff_vector(vector)
      )
    piopexec.indexer_output_pk = voexec.indexer_output_pk
    piopexec.indexer_output_vk = voexec.indexer_output_vk
    piopexec.reference_to_voexec = voexec
    piopexec.vec_to_poly_dict = vec_to_poly_dict

  def _generate_new_randomizer(self, samples, k):
    randomizer = get_named_vector("delta")
    samples.append([randomizer, k])
    return randomizer

  def _process_prover_submitted_vector(self, piopexec, v, size, rust_size, samples):
    rust_n = piopexec.reference_to_voexec.rust_vector_size
    poly = v.to_named_vector_poly()

    # Sample the randomizer
    if not v._do_not_randomize:
      randomizer = self._generate_new_randomizer(samples, 1)

      # Zero pad the vector to size n then append the randomizer
      piopexec.prover_computes(
          Math(randomizer).sample(self.Ftoq).comma(
              Math(v)).assign(v).double_bar(randomizer),
          rust_line_redefine_zero_pad_concat_vector(v, rust_n, randomizer))

      piopexec.prover_send_polynomial(
          poly, self.vector_size + self.q, rust_n + self.q)
    else:
      piopexec.prover_send_polynomial(poly, size, rust_size)

    # piopexec.prover_rust_define_poly_from_vec(poly, v)
    piopexec.vec_to_poly_dict[v.key()] = poly

    piopexec.prover_debug(
        "vector %s of length {} = \\n[{}]" % rust(v), "%s.len()" % rust(v),
        rust_fmt_ff_vector(v),
    )

  def _process_interactions(self, piopexec, samples):
    voexec = piopexec.reference_to_voexec
    for interaction in voexec.interactions:
      if isinstance(interaction, ProverComputes):
        piopexec.prover_computes(
            interaction.latex_builder, interaction.rust_builder)
      elif isinstance(interaction, VerifierComputes):
        piopexec.verifier_computes(
            interaction.latex_builder, interaction.rust_builder)
      elif isinstance(interaction, VerifierSendRandomnesses):
        piopexec.verifier_send_randomness(*interaction.names)
      elif isinstance(interaction, ProverSubmitVectors):
        """
        Since the value n can be long and complex, define a new symbol in rust
        and put the long expression of n in this new symbol. This rust version
        of symbol should never be used outside rust context
        Must be postponed to here because only now it is guaranteed that all the
        necessary variables that n depends on are defined
        """
        voexec.try_verifier_redefine_vector_size_rust(
            "n", voexec.vector_size, piopexec)
        for v, size, rust_size in interaction.vectors:
          self._process_prover_submitted_vector(
              piopexec, v, size, rust_size, samples)
      else:
        raise ValueError(
            "Interaction of type %s should not appear" % type(interaction))

  """
  Check that the hadamard product of a query is indeed zero
  """

  def _check_hadamard_sides(self, piopexec, i, check_individual_hadamard,
                            alpha_power, side1, side2=None):
    if side2 is None:
      side = side1
      check_individual_hadamard.append(rust_check_vector_eq(
          rust_expression_vector_i(
              rust_mul(
                  (side.a * (1/alpha_power)).dumpr_at_index(sym_i,
                                                            piopexec.coeff_manager),
                  side.b.dumpr_at_index(sym_i, piopexec.coeff_manager)),
              piopexec.reference_to_voexec.rust_vector_size),
          rust_vec_size(
              rust_zero(), piopexec.reference_to_voexec.rust_vector_size),
          "The %d\'th hadamard check is not satisfied" % (i+1)
      )).end()
    else:
      check_individual_hadamard.append(rust_check_expression_vector_eq_i(
          rust_mul(
              (side1.a * (1/alpha_power)).dumpr_at_index(sym_i, piopexec.coeff_manager),
              side1.b.dumpr_at_index(sym_i, piopexec.coeff_manager)),
          rust_neg(rust_mul(
              (side2.a * (1/alpha_power)).dumpr_at_index(sym_i, piopexec.coeff_manager),
              side2.b.dumpr_at_index(sym_i, piopexec.coeff_manager))),
          piopexec.reference_to_voexec.rust_vector_size,
          "The %d\'th hadamard check is not satisfied" % (i+1)
      )).end()

  def _process_inner_product(self, piopexec, extended_hadamard,
                             shifts, samples, alpha):
    voexec = piopexec.reference_to_voexec
    beta = piopexec.verifier_generate_and_send_rand("beta")
    r = get_named_vector("r")
    rust_n = voexec.rust_vector_size
    n = voexec.vector_size

    extended_hadamard.start_adding_sides(beta)
    for i, inner in enumerate(voexec.inner_products):
      extended_hadamard.add_side(inner.left_side)
      if not inner.one_sided:
        extended_hadamard.add_side(-inner.right_side)
      shifts += inner.shifts()
      extended_hadamard.next_beta()

    piopexec.prover_computes_latex(
        LaTeXBuilder().start_math().append(r).assign().end_math()
                      .space("the sum of:").eol()
                      .append(
            Itemize().append([
                inner.dump_hadamard_difference_with_beta_power(beta, i)
                for i, inner in enumerate(voexec.inner_products)
            ])))

    piopexec.prover_rust_define_expression_vector_i(
        r,
        rust_power_linear_combination(beta).append([
            inner.dumpr_at_index(sym_i, piopexec.coeff_manager)
            for i, inner in enumerate(voexec.inner_products)
        ]), rust_n)

    randomizer = self._generate_new_randomizer(samples, 1)
    rtilde = get_named_vector("r", modifier="tilde")

    """
    tilde{r} is the accumulation vector of r combined with the randomizer
    """
    piopexec.prover_computes_latex(Math(randomizer).sample(self.Ftoq)
                                   .comma(rtilde).assign(AccumulationVector(r.slice("j"), n))
                                   .double_bar(randomizer))
    piopexec.prover_rust_define_concat_vector(
        rtilde,
        rust_accumulate_vector_plus(r),
        randomizer)

    fr = rtilde.to_named_vector_poly()
    # piopexec.prover_rust_define_poly_from_vec(fr, rtilde)

    piopexec.prover_send_polynomial(fr, n + self.q, rust_n + self.q)
    piopexec.vec_to_poly_dict[rtilde.key()] = fr

    extended_hadamard.clear_beta()
    extended_hadamard.add_side(-VOQuerySide(PowerVector(1, n, rust_n),
                                            rtilde - rtilde.shift(1)))
    extended_hadamard.end_adding_sides()

    extended_hadamard.add_side(VOQuerySide(UnitVector(n, rust_n), rtilde))

    # This last hadamard check involves only a named vector times
    # a unit vector, it does not contributes to t
    extended_hadamard.ignore_last()

  def _process_vector_t(self, piopexec, samples, extended_hadamard):
    rust_n = piopexec.reference_to_voexec.rust_vector_size
    n = piopexec.reference_to_voexec.vector_size
    max_shift = piopexec.max_shift
    rust_max_shift = piopexec.rust_max_shift

    t = get_named_vector("t")
    randomizer = self._generate_new_randomizer(samples, 1)

    piopexec.prover_computes_latex(
        LaTeXBuilder().start_math()
        .append(randomizer)
        .sample(self.Ftoq).comma(t)
        .assign(randomizer).double_bar().end_math()
        .space("the sum of:").eol()
        .append(extended_hadamard.dump_itemize()))

    piopexec.prover_rust_define_vec(
        t, rust_vector_concat(
            randomizer,
            rust_expression_vector_i(
                extended_hadamard.dump_linear_combination_at_i(
                    rust_n, piopexec.coeff_manager),
                2 * self.q + rust_max_shift)))

    tx = t.to_named_vector_poly()
    piopexec.vec_to_poly_dict[t.key()] = tx
    piopexec.prover_send_polynomial(
        tx, 2 * self.q + max_shift, 2 * self.q + rust_max_shift)

    extended_hadamard.add_side_raw(VOQuerySide(
        -PowerVector(1, max_shift + self.q, rust_max_shift +
                     self.q).shift(n, rust_n),
        t.shift(n - self.q, rust_n - self.q)
    ))

  def _process_extended_hadamards(self, piopexec, samples):
    """
    Although alpha is sent to the prover after the prover sends all the
    vectors except t, this symbol is used in processing the extended hadamard
    queries. So first declare it here.
    """
    alpha = Symbol(get_name('alpha'))
    """
    A list of VO query sides, each is of the form vec{a} circ vec{b}
    together they should sum to zero
    """
    extended_hadamard = ExtendedHadamard(alpha)
    """
    Used to records all the shifts appeared in the vectors,
    and finally compute the maximal shift
    """
    shifts = []

    voexec = piopexec.reference_to_voexec
    rust_n = voexec.rust_vector_size
    n = voexec.vector_size

    if self.debug_mode:
      check_individual_hadmard = RustBuilder()

    """
    Some hadamard checks are guaranteed to be zero
    if the prover is honest. In that case, there is no
    need for the honest prover to include those terms
    in t. The hadamard queries that are ignored is stored
    in this set
    """
    for i, had in enumerate(voexec.hadamards):
      alpha_power, side1, side2 = extended_hadamard.add_hadamard_query(had)
      if self.debug_mode and self.debug_check_hadamard_side:
        self._check_hadamard_sides(
            piopexec, i, check_individual_hadmard, alpha_power, side1, side2)
      shifts += had.shifts()

    if self.debug_mode:
      piopexec.prover_computes_rust(check_individual_hadmard)

    self.debug("Process inner products")
    if len(voexec.inner_products) > 0:
      self._process_inner_product(
          piopexec, extended_hadamard, shifts, samples, alpha)

    max_shift = voexec.simplify_max(Max(*shifts))
    rust_max_shift = piopexec.prover_redefine_symbol_rust(
        max_shift, "maxshift")
    piopexec.verifier_send_randomness(alpha)
    piopexec.max_shift = max_shift
    piopexec.rust_max_shift = rust_max_shift

    self.debug("Process vector t")
    self._process_vector_t(piopexec, samples, extended_hadamard)

    return extended_hadamard, max_shift, rust_max_shift

  def _fix_missing_vector_key(self, vec, piopexec):
    if isinstance(vec, NamedVector) and vec.key() not in piopexec.vec_to_poly_dict:
      """
      This is possible because some named vectors
      might be locally evaluatable, never submitted
      by the prover or the indexer
      """
      if not vec.local_evaluate:
        raise Exception("Some non-local vector is not in the dict: %s"
                        % vec.dumps())
      piopexec.vec_to_poly_dict[vec.key()] = vec.to_named_vector_poly()

  def _increment_h_omega_sum(self, piopexec, h_omega_sum_check, h_omega_sum, omega, a, b, size):
    h_omega_sum_check.append(h_omega_sum).plus_assign(
        rust_eval_vector_expression_i(omega,
                                      rust_mul(a.dumpr_at_index(sym_i, piopexec.coeff_manager),
                                               b.dumpr_at_index(sym_i, piopexec.coeff_manager)),
                                      rust(size))
    ).end()

  def _increment_vec_sum(self, piopexec, vecsum, a, b):
    piopexec.prover_rust_add_expression_vector_to_vector_i(vecsum,
                                                           rust_mul(a.dumpr_at_index(sym_i, piopexec.coeff_manager), b.dumpr_at_index(sym_i, piopexec.coeff_manager)))

  def _increment_h_check_by_naive_atimesb(self, piopexec, hcheck_vec, a, b, size, omega):
    atimesb_vec_naive = get_named_vector("abnaive")
    piopexec.prover_rust_define_vector_poly_mul_no_dict(
        atimesb_vec_naive,
        rust_expression_vector_i(a.dumpr_at_index(
            sym_i, piopexec.coeff_manager), size),
        rust_expression_vector_i(b.dumpr_at_index(
            sym_i, piopexec.coeff_manager), size),
        omega)
    piopexec.prover_rust_add_vector_to_vector(hcheck_vec, atimesb_vec_naive)
    return atimesb_vec_naive

  def _computes_atimesb_vec(self, piopexec, atimesb, omega, a, b, size):
    atimesb_computes_rust, atimesb_vector_combination = \
        atimesb.generate_vector_combination(omega, piopexec.coeff_manager)
    piopexec.prover_computes_rust(atimesb_computes_rust)

    atimesb_vec = get_named_vector("atimesb")
    piopexec.prover_computes_rust("// The vector pair here is %s and %s\n" %
                                  (a.dumps(), b.dumps()))
    piopexec.prover_rust_define_expression_vector_i(atimesb_vec,
                                                    atimesb_vector_combination.dumpr_at_index(
                                                        sym_i - size + 1, piopexec.coeff_manager),
                                                    2 * size - 1)

    return atimesb_vec

  def _process_h(self, piopexec, extended_hadamard):
    omega = piopexec.verifier_generate_and_send_rand("omega")
    n = piopexec.reference_to_voexec.vector_size
    rust_n = piopexec.reference_to_voexec.rust_vector_size
    max_shift = piopexec.max_shift
    rust_max_shift = piopexec.rust_max_shift

    hx = get_named_polynomial("h")

    if self.debug_mode:
      h_omega_sum = Symbol(get_name('h_osum'))
      h_omega_sum_check = rust_builder_define_mut(
          h_omega_sum, rust_zero()).end()
      vecsum = get_named_vector("sum")
      piopexec.prover_rust_define_mut(
          vecsum,
          rust_vec_size(rust_zero(), rust_n + rust_max_shift + self.q))
      hcheck_vec = get_named_vector("hcheck")
      piopexec.prover_rust_define_mut(
          hcheck_vec,
          rust_vec_size(rust_zero(), (rust_n + rust_max_shift + self.q) * 2 - 1))

    for vec in extended_hadamard.dump_named_vectors():
      self._fix_missing_vector_key(vec, piopexec)

    if self.debug_mode:
      for i, side in enumerate(extended_hadamard.items):
        a = VectorCombination._from(side.a)
        b = VectorCombination._from(side.b)
        atimesb = convolution(a, b, omega)
        size = rust_n + rust_max_shift + self.q
        self._increment_h_omega_sum(piopexec,
                                    h_omega_sum_check, h_omega_sum, omega, a, b, size)
        self._increment_vec_sum(piopexec, vecsum, a, b)
        piopexec.prover_rust_check_vector_eq(
            self._computes_atimesb_vec(piopexec, atimesb, omega, a, b, size),
            rust_zero_pad(self._increment_h_check_by_naive_atimesb(
                piopexec, hcheck_vec, a, b, size, omega
            ), 2 * size - 1),
            "The %d'th convolution is incorrect" % (i+1))

    h = get_named_vector("h")
    hxcomputes_rust, h_vec_combination = \
        extended_hadamard.generate_hx_vector_combination(
            omega, piopexec.coeff_manager)
    piopexec.process_redefine_coeffs()
    piopexec.prover_computes(
        LaTeXBuilder()
        .start_math().append(hx).assign().end_math().space("the sum of:").eol()
        .append(extended_hadamard.dump_product_items(omega, piopexec.vec_to_poly_dict)),
        hxcomputes_rust)

    h_degree, h_inverse_degree = n + max_shift + self.q, n + max_shift + self.q
    rust_h_degree = rust_n + rust_max_shift + self.q
    rust_h_inverse_degree = rust_n + rust_max_shift + self.q

    if self.debug_mode:
      h_omega_sum_check.append(rust_assert_eq(
          h_omega_sum, rust_zero())).end()
      piopexec.prover_computes_rust(h_omega_sum_check)
      piopexec.prover_rust_check_vector_eq(
          vecsum, rust_vec_size(rust_zero(), rust_n + max_shift + self.q),
          "sum of hadamards not zero")
      piopexec.prover_rust_define_expression_vector_i(
          h,
          h_vec_combination.dumpr_at_index(
              sym_i - rust_h_inverse_degree + 1, piopexec.coeff_manager),
          rust_h_degree + rust_h_inverse_degree - 1)
      piopexec.prover_rust_check_vector_eq(h, hcheck_vec, "h is not expected")

    return h, hx, h_vec_combination, h_degree, h_inverse_degree, \
        rust_h_degree, rust_h_inverse_degree, omega

  def _split_h(self, piopexec, h, hx, h_vec_combination, extended_hadamard,
               h_degree, h_inverse_degree, rust_h_degree, rust_h_inverse_degree):
    h1 = get_named_vector("h")
    h2 = get_named_vector("h")

    piopexec.prover_rust_define_expression_vector_i(
        h1,
        h_vec_combination.dumpr_at_index(
            sym_i - rust_h_inverse_degree + 1, piopexec.coeff_manager, collect_symbols=extended_hadamard.alpha),
        rust_h_inverse_degree - 1)
    piopexec.prover_rust_define_expression_vector_i(
        h2,
        h_vec_combination.dumpr_at_index(
            sym_i + 1, piopexec.coeff_manager, collect_symbols=extended_hadamard.alpha),
        rust_h_degree - 1)

    if self.debug_mode:
      piopexec.prover_rust_check_vector_eq(
          h,
          rust_vector_concat(h1, rust_vec(rust_zero()), h2),
          "h != h1 || 0 || h2")
      piopexec.prover_rust_assert_eq(
          h_vec_combination.dumpr_at_index(1, piopexec.coeff_manager), rust_zero())

    h1x = h1.to_named_vector_poly()
    h2x = h2.to_named_vector_poly()
    piopexec.prover_computes_latex(Math(h1x).assign(hx).dot(X ** self.degree_bound)
                                   .append("\\bmod").append(X ** self.degree_bound))
    piopexec.prover_computes_latex(Math(h2x).assign("\\frac{%s}{X}" % hx.dumps_var(X))
                                   .minus("X^{%s}\\cdot %s" % (tex(-self.degree_bound-1),
                                                               h1x.dumps_var(X))))

    piopexec.prover_send_polynomial(h1x, self.degree_bound)
    piopexec.prover_send_polynomial(h2x, h_degree - 1, rust_h_degree - 1)

    return h1, h2, h1x, h2x

  def _homomorphic_check(self, piopexec, extended_hadamard,
                         h, h1, h2, h1x, h2x, omega,
                         h_inverse_degree, rust_h_inverse_degree,
                         h_degree, rust_max_shift):
    z = piopexec.verifier_generate_and_send_rand("z")
    z0 = omega/z
    rust_n = piopexec.reference_to_voexec.rust_vector_size
    rust_max_shift = piopexec.rust_max_shift

    self.debug("Collect named vectors inside left operands")
    left_named_vectors = extended_hadamard.named_vecs_in_left_operands()

    self.debug("Make evaluation queries")
    query_results = {}
    for key, vec in left_named_vectors.items():
      y = Symbol(get_name("y"))
      query_results[key] = y
      piopexec.eval_query_for_possibly_local_poly(
          y, z0, piopexec.vec_to_poly_dict[key], vec, rust_n + self.q)

    self.debug("Compute gx")
    self._combine_polynomials_in_right_operands(
        piopexec, extended_hadamard, z, z0, query_results,
        h, h1, h2, h1x, h2x, h_inverse_degree, rust_h_inverse_degree,
        rust_n + rust_max_shift + self.q)

  def _add_to_naive_g(self, piopexec, vec_or_value, coeff=None):
    value = vec_or_value.dumpr_at_index(sym_i, piopexec.coeff_manager)
    value = value if coeff is None else rust_mul(value, coeff)
    piopexec.prover_rust_add_expression_vector_to_vector_i(
        piopexec.naive_g, value)

  def _populate_coeff_builder_by_hadamard_query(
          self, piopexec, side, coeff_builders, z0, z, query_results, size):
    """
    assume side.a = f_i(X), side.b = g_i(X)
    then this query branch contributes a f_i(omega/z) * g_i(X) to the final polynomial g(X)
    to compute f_i(omega/z), split f_i(X) into linear combination of named polynomials
    where the coefficients are structured polynomials, i.e.,
    f_i(omega/z) = s_1(omega/z) p_1(omega/z) + ... + s_k(omega/z) p_k(omega/z) + s_0(omega/z)
    """
    a = VectorCombination._from(side.a)
    # now multiplier should equal f_i(omega/z). if zero, then ignore this term
    multiplier = simplify(sum([
        value.to_poly_expr(z0) * (1 if key == "one" else query_results[key])
        for key, vec, value in a.key_keyed_coeffs()]))

    # check that multiplier = f_i(omega/z)
    if self.debug_mode:
      piopexec.prover_rust_assert_eq(
          multiplier if multiplier != 0 else rust_zero(),
          rust_eval_vector_expression_i(
              z0, a.dumpr_at_index(sym_i, piopexec.coeff_manager),
              size))

    if multiplier == 0:
      return
    b = VectorCombination._from(side.b) * multiplier

    # The naive way to compute f_i(omega/z) g_i(X), is to directly dump g_i(X)
    # coefficients on [1..n+max_shift+q], multiplied by the multiplier
    if self.debug_mode:
      self._add_to_naive_g(piopexec, b)

    # Now decompose g_i(X), i.e., the right side of this Extended Hadamard query
    # multiply every coefficient by the multiplier f_i(omega/z)
    # then evaluate the coefficient at z
    for key, vec, value in b.key_keyed_coeffs():
      rust_value = simplify(value.to_poly_expr_rust(z))
      value = simplify(value.to_poly_expr(z))
      if value == 0 or rust_value == 0:
        raise Exception("value should not be zero")

      poly = "one" if key == "one" else piopexec.vec_to_poly_dict[vec.key()]
      value = tex(value)

      if isinstance(vec, NamedVector) and vec.local_evaluate:
        # In case it is locally evaluatable polynomial, this term should be
        # regarded as part of the constant, instead of a polynomial. Let the verifier
        # locally evaluate this polynomial at z
        key, value, poly = "one", "%s\\cdot %s" % (
            value, poly.dumps_var(z)), "one"
        rust_value = rust_value * vec.dump_symbol_hint_computation(z)

      # If this polynomial (or constant) has not been handled before, initialize
      # it with empty list and a new symbol for the coefficient
      # We temporarily use list here, because the format depends on whether
      # this list size is > 1
      if key not in coeff_builders:
        coeff_builders[key] = CombinationCoeffBuilder(
            poly, Symbol(get_name("c")), [], [])

      coeff_builder = coeff_builders[key]
      coeff_builder.latex_builder.append(value)
      coeff_builder.rust_builder.append(rust_value)

  def _check_hz(self, piopexec, z0, z, extended_hadamard, size, h,
                rust_h_inverse_degree):
    # Check that h(z) = sum_i f_i(omega/z) g_i(z) z^{n+maxshift+q}
    piopexec.prover_rust_assert_eq(
        extended_hadamard.dump_hz_rust(z0, z, size, piopexec.coeff_manager),
        rust_mul(rust_eval_vector_as_poly(h, z),
                 z**(-(rust_h_inverse_degree-1))))

  def _combine_polynomials_in_right_operands(
          self, piopexec, extended_hadamard, z, z0,
          query_results, h, h1, h2, h1x, h2x, h_inverse_degree,
          rust_h_inverse_degree, size):

    if self.debug_mode:
      naive_g = get_named_vector("naive_g")
      # Pass this variable to the zkSNARK, because g has not been computed, cannot
      # make the comparison in the PIOP level.
      piopexec.naive_g = naive_g
      piopexec.prover_rust_define_vec_mut(naive_g,
                                          rust_vec_size(rust_zero(), self.degree_bound))

    # map: key -> (poly, Symbol(coeff), latex_builder, rust_builder)
    coeff_builders = {}
    # 1. The part contributed by the extended hadamard query
    for i, side in enumerate(extended_hadamard.items):
      self._populate_coeff_builder_by_hadamard_query(
          piopexec, side, coeff_builders, z0, z, query_results, size)

    # 2. The part contributed by h1(X) and h2(X)
    # h1(X) is committed aligned to the right boundary of the universal parameters
    # so we should additionally multiply a power of z to it when computing g(X)
    coeff_builders[h1x.key()] = CombinationCoeffBuilder(
        h1x, Symbol(get_name("c")),
        [- z ** (-self.degree_bound)], [- z ** (-self.degree_bound)],
        self.degree_bound - (rust_h_inverse_degree - 1))

    coeff_builders[h2x.key()] = CombinationCoeffBuilder(
        h2x, Symbol(get_name("c")), [- z], [- z], 0)

    if self.debug_mode:
      self._add_to_naive_g(piopexec,
                           h1.shift(self.degree_bound -
                                    (rust_h_inverse_degree - 1)),
                           -z**(-self.degree_bound))
      self._add_to_naive_g(piopexec, h2, -z)
      self._check_hz(piopexec, z0, z, extended_hadamard,
                     size, h, rust_h_inverse_degree)

    # Transform the lists into latex and rust builders
    for key, coeff_builder in coeff_builders.items():
      coeff_builder.transform_lists_to_builders(extended_hadamard.alpha)

    gx = get_named_polynomial("g")
    piopexec.combine_polynomial(gx, coeff_builders, self.degree_bound)
    piopexec.eval_check(0, z, gx)

  def execute(self, piopexec):
    voexec = piopexec.reference_to_voexec
    self.q = Integer(1)
    self.Ftoq = UnevaluatedExpr(F ** self.q)

    samples = rust_sample_randomizers()
    piopexec.prover_computes_rust(RustBuilder(samples).end())

    self.debug("Executing VO protocol")
    self.vo.execute_with_prestored_args(voexec)
    piopexec.prover_inputs = voexec.prover_inputs
    piopexec.verifier_inputs = voexec.verifier_inputs
    piopexec.coeff_manager = voexec.coeff_manager

    self.debug("Process interactions")
    self._process_interactions(piopexec, samples)

    """
    Must process the coefficient manager AFTER processing interactions,
    because now the dependent variables in the hadamard queries are defined
    """
    piopexec.process_redefine_coeffs()

    self.debug("Prepare extended hadamard")
    extended_hadamard, max_shift, rust_max_shift = \
        self._process_extended_hadamards(piopexec, samples)

    self.debug("Process polynomial h")
    h, hx, h_vec_combination, h_degree, h_inverse_degree, \
        rust_h_degree, rust_h_inverse_degree, omega = \
        self._process_h(piopexec, extended_hadamard)
    piopexec.max_degree = h_degree - 1

    """
    Split h into two halves
    """
    self.debug("Compute h1 and h2")
    h1, h2, h1x, h2x = self._split_h(
        piopexec, h, hx, h_vec_combination, extended_hadamard,
        h_degree, h_inverse_degree, rust_h_degree, rust_h_inverse_degree)

    """
    Here we assume that the underlying polynomial commitment scheme is
    homomorphic. In that case, the prover only needs to open the polynomials
    involved in all the left operands of the Hadamard queries and the verifier
    can later merge the commitments of polynomials involved in right operands
    linearly.
    """
    self.debug("Verifier's turn")
    self._homomorphic_check(piopexec, extended_hadamard, h, h1, h2, h1x, h2x, omega,
                            h_inverse_degree, rust_h_inverse_degree,
                            h_degree, rust_max_shift)
