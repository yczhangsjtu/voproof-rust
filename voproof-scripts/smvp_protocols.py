from sympy import Symbol, latex, sympify, Integer, simplify
from sympy.abc import alpha, beta, gamma
from compiler.vo_protocol import VOProtocol, VOProtocolExecution
from compiler.symbol.vector import get_named_vector, PowerVector, UnitVector
from compiler.symbol.names import reset_name_counters, get_name
from compiler.symbol.matrix import Matrix
from compiler.symbol.util import rust_pk, rust_vk
from compiler.builder.latex import Math, AccumulationVector, ExpressionVector, \
    LaTeXBuilder, ProductAccumulationDivideVector, add_paren_if_not_atom, tex
from compiler.builder.rust import *


class SparseMVP(VOProtocol):
  def __init__(self):
    super(SparseMVP, self).__init__("SparseMVP")

  def preprocess(self, voexec, H, K, ell, M):
    n = voexec.vector_size
    u = get_named_vector("u").as_preprocessed()
    w = get_named_vector("w").as_preprocessed()
    v = get_named_vector("v").as_preprocessed()
    y = get_named_vector("y").as_preprocessed()
    voexec.pp_rust_define_matrix_vectors(u, w, v, M, "gamma")
    voexec.pp_rust_define_hadamard_vector(y, u, w)

    voexec.preprocess_vector(u, ell)
    voexec.preprocess_vector(w, ell)
    voexec.preprocess_vector(v, ell)
    voexec.preprocess_vector(y, ell)
    
    return {
        "u": u,
        "w": w,
        "v": v,
        "y": y,
        "H": H,
        "K": K,
        "ell": ell,
        "M": M,
    }

  def execute(self, voexec, pp_info, a):
    n = voexec.vector_size
    H, K, ell, M, w = pp_info["H"], pp_info["K"], pp_info["ell"], pp_info["M"], pp_info["w"]
    mu = Symbol(get_name("mu"))
    if voexec.rust_vector_size is None:
      voexec.rust_vector_size = voexec.verifier_redefine_symbol_rust(n, "n")
    rust_n = voexec.rust_vector_size
    rust_ell = voexec.verifier_redefine_symbol_rust(ell, "ell")
    voexec.verifier_rust_define_generator()
    voexec.verifier_send_randomness(mu)
    r = get_named_vector("r")
    r._do_not_randomize = True  # r depends only on the random number
    voexec.prover_rust_define_expression_vector_inverse_i(
            r,
            rust_minus(mu, PowerVector(gamma, H).dumpr_at_index(
                sym_i, voexec.coeff_manager)),
            H)
    c = get_named_vector("c")
    c._do_not_randomize = True  # c depends only on the random number and public matrix
    voexec.prover_rust_define_left_sparse_mvp_vector(
        c, rust_pk(M), r, H, K)
    s = get_named_vector("s")
    s._do_not_randomize = True  # s depends only on r and c
    voexec.prover_rust_define_concat_neg_vector(s, r, c)

    voexec.prover_submit_vector(s, H + K)
    voexec.hadamard_query(
        mu * PowerVector(1, H) - PowerVector(gamma, H),
        s,
        PowerVector(1, H),
        PowerVector(1, H))
    voexec.inner_product_query(a, s)

    nu = Symbol(get_name("nu"))
    voexec.verifier_send_randomness(nu)

    h = get_named_vector("h")
    h._do_not_randomize = True  # h depends only on random numbers
    rnu = get_named_vector("rnu")
    rnu._do_not_randomize = True  # r_nu depends only on random numbers
    voexec.prover_rust_define_expression_vector_inverse_i(
        rnu,
        rust_minus(nu, PowerVector(gamma, K).dumpr_at_index(
            sym_i, voexec.coeff_manager)),
        K)
    voexec.prover_rust_define_concat_uwinverse_vector(
        h, rnu, mu, rust_pk(pp_info["u"]), nu, rust_pk(pp_info["w"]))
    voexec.prover_submit_vector(h, ell + K, rust_ell + K)

    voexec.hadamard_query(
        nu * PowerVector(1, K) - PowerVector(gamma, K),
        h,
        PowerVector(1, K),
        PowerVector(1, K),
    )

    voexec.hadamard_query(
        PowerVector(1, n-H-K, rust_n-H-K).shift(H+K),
        s,
    )

    voexec.hadamard_query(
        PowerVector(1, n-K-ell, rust_n-K-rust_ell)
        .shift(ell+K, rust_ell+K),
        h,
    )

    voexec.hadamard_query(
        h,
        (mu * nu * PowerVector(1, ell, rust_ell) - mu * pp_info["w"] -
         nu * pp_info["u"] + pp_info["y"]).shift(K),
        PowerVector(1, ell, rust_ell).shift(K),
        PowerVector(1, ell, rust_ell).shift(K),
    )

    voexec.inner_product_query(- h.shift(H), s, h, pp_info["v"].shift(K))


class SparseMVPProverEfficient(VOProtocol):
  def __init__(self):
    super().__init__("SparseMVP")

  def preprocess(self, voexec: VOProtocolExecution, H, K, ell, M):
    u = get_named_vector("u").as_preprocessed()
    w = get_named_vector("w").as_preprocessed()
    v = get_named_vector("v").as_preprocessed()
    y = get_named_vector("y").as_preprocessed()
    voexec.pp_rust_define_matrix_vectors(u, w, v, M, "gamma")
    voexec.pp_rust_define_hadamard_vector(y, u, w)

    voexec.preprocess_vector(u, ell)
    voexec.preprocess_vector(w, ell)
    voexec.preprocess_vector(v, ell)
    voexec.preprocess_vector(y, ell)
    return {
        "u": u,
        "v": v,
        "w": w,
        "y": y,
        "H": H,
        "K": K,
        "ell": ell,
        "M": M,
    }

  def execute(self, voexec, pp_info, a, b):
    n, H, K, ell, M = voexec.vector_size, pp_info["H"], pp_info["K"], pp_info["ell"], pp_info["M"]

    mu = Symbol(get_name("mu"))
    if voexec.rust_vector_size is None:
      voexec.rust_vector_size = voexec.verifier_redefine_symbol_rust(n, "n")
    rust_n = voexec.rust_vector_size
    rust_ell = voexec.verifier_redefine_symbol_rust(ell, "ell")
    voexec.verifier_rust_define_generator()
    voexec.verifier_send_randomness(mu)
    rmu = get_named_vector("r")
    rmu._do_not_randomize = True  # r depends only on the random number
    voexec.prover_rust_define_expression_vector_inverse_i(
            rmu,
            rust_minus(mu, PowerVector(gamma, H).dumpr_at_index(
                sym_i, voexec.coeff_manager)),
            H)
    c = get_named_vector("c")
    c._do_not_randomize = True  # c depends only on the random number and public matrix
    voexec.prover_rust_define_left_sparse_mvp_vector(
        c, rust_pk(M), rmu, H, K)

    voexec.prover_submit_vector(rmu, H)
    voexec.prover_submit_vector(c, K)
    voexec.hadamard_query(
        mu * PowerVector(1, H) - PowerVector(gamma, H),
        rmu,
        PowerVector(1, H),
        PowerVector(1, H))
    voexec.inner_product_query(c, a, b, rmu)

    nu = Symbol(get_name("nu"))
    voexec.verifier_send_randomness(nu)

    rnu = get_named_vector("rnu")
    rnu._do_not_randomize = True  # r_nu depends only on random numbers
    voexec.prover_rust_define_expression_vector_inverse_i(
        rnu,
        rust_minus(nu, PowerVector(gamma, K).dumpr_at_index(
            sym_i, voexec.coeff_manager)),
        K)
    t = get_named_vector("t")
    t._do_not_randomize = True
    voexec.prover_rust_define_uwinverse_vector(
        t, mu, rust_pk(pp_info["u"]), nu, rust_pk(pp_info["w"]))
    voexec.prover_submit_vector(rnu, K, K)
    voexec.prover_submit_vector(t, ell, rust_ell)

    voexec.hadamard_query(
        nu * PowerVector(1, K) - PowerVector(gamma, K),
        rnu,
        PowerVector(1, K),
        PowerVector(1, K),
    )
#
    voexec.hadamard_query(
        PowerVector(1, n-H, rust_n-H).shift(H),
        rmu,
    )

    voexec.hadamard_query(
        PowerVector(1, n-K, rust_n-K).shift(K),
        rnu,
    )

    voexec.hadamard_query(
        PowerVector(1, n-K, rust_n-K).shift(K),
        c,
    )

    voexec.hadamard_query(
        PowerVector(1, n-ell, rust_n-rust_ell)
        .shift(ell, rust_ell),
        t,
    )

    voexec.hadamard_query(
        t,
        (mu * nu * PowerVector(1, ell, rust_ell) - mu * pp_info["w"] -
         nu * pp_info["u"] + pp_info["y"]),
        PowerVector(1, ell, rust_ell),
        PowerVector(1, ell, rust_ell),
    )

    voexec.inner_product_query(c, rnu, t, pp_info["v"])
#

class R1CS(VOProtocol):
  def __init__(self):
    super(R1CS, self).__init__("R1CS")

  def preprocess(self, voexec, H, K, sa, sb, sc):
    M = Matrix("M").as_preprocessed()
    voexec.pp_rust_concat_matrix_vertically(
        M, H,
        "cs.arows", "cs.brows", "cs.crows",
        "cs.acols", "cs.bcols", "cs.ccols",
        "cs.avals", "cs.bvals", "cs.cvals")

    voexec.preprocess_output_pk(M)

    smvp_info = SparseMVP().preprocess(voexec, H * 3, K, sa + sb + sc, M)
    voexec.r1cs_H = H
    voexec.r1cs_K = K
    voexec.sa = sa
    voexec.sb = sb
    voexec.sc = sc
    return {
        "M": M,
        "H": H,
        "K": K,
        "sa": sa,
        "sb": sb,
        "sc": sc,
        "smvp_info": smvp_info,
    }

  def execute(self, voexec, pp_info, x, w, ell):
    H, K, sa, sb, sc, n = pp_info["H"], pp_info["K"], \
        pp_info["sa"], pp_info["sb"], pp_info["sc"], voexec.vector_size
    M = pp_info["M"]

    voexec.verifier_rust_define_vec(x, "x.instance.clone()")
    voexec.prover_rust_define_vec(w, "w.witness.clone()")
    voexec.verifier_rust_init_size(H, "nrows")
    voexec.verifier_rust_init_size(K, "ncols")
    voexec.verifier_rust_init_size(sa, "adensity")
    voexec.verifier_rust_init_size(sb, "bdensity")
    voexec.verifier_rust_init_size(sc, "cdensity")
    voexec.verifier_rust_init_size(ell, "input_size")
    voexec.try_verifier_redefine_vector_size_rust("n", n)
    rust_n = voexec.rust_vector_size

    u = get_named_vector("u")
    voexec.prover_rust_define_sparse_mvp_concat_vector(
        u,
        rust_pk(M),
        rust_concat_and_one(x, w),
        H * 3, K
    )
    
    voexec.prover_submit_vector(u, 3 * H + K)
    voexec.run_subprotocol(SparseMVP(), pp_info["smvp_info"], u)
    voexec.hadamard_query(
        u.shift(n-H, rust_n-H),
        u.shift(n-H*2, rust_n-H*2),
        PowerVector(1, H).shift(n-H, rust_n-H),
        u.shift(n-H*3, rust_n-H*3),
    )
    voexec.hadamard_query(
        PowerVector(1, ell+1).shift(H*3),
        u - x.shift(H*3+1) - UnitVector(H*3+1),
    )

class R1CSProverEfficient(VOProtocol):
  def __init__(self):
    super(R1CSProverEfficient, self).__init__("R1CS")

  def preprocess(self, voexec, H, K, sa, sb, sc):
    M = Matrix("M").as_preprocessed()

    voexec.pp_rust_concat_matrix_vertically(
        M, H,
        "cs.arows", "cs.crows", "cs.brows",
        "cs.acols", "cs.ccols", "cs.bcols",
        "cs.avals", "cs.cvals", "cs.bvals")

    voexec.preprocess_output_pk(M)

    smvp_info = SparseMVP().preprocess(voexec, H * 3, K, sa + sb + sc, M)
    return {
        "M": M,
        "H": H,
        "K": K,
        "sa": sa,
        "sb": sb,
        "sc": sc,
        "smvp_info": smvp_info,
    }

  def execute(self, voexec: VOProtocolExecution, pp_info, x, w, ell):
    H, K, sa, sb, sc, n = pp_info["H"], pp_info["K"], \
        pp_info["sa"], pp_info["sb"], pp_info["sc"], voexec.vector_size
    M = pp_info["M"]

    voexec.verifier_rust_define_vec(x, "x.instance.clone()")
    voexec.prover_rust_define_vec(w, "w.witness.clone()")
    voexec.try_verifier_redefine_vector_size_rust("n", n)
    rust_n = voexec.rust_vector_size

    y = get_named_vector("y")
    voexec.prover_rust_define_sparse_mvp_vector(
        y, rust_pk(M), rust_concat_and_one(x, w), H * 3, K)
    
    voexec.prover_submit_vector(y, 3 * H)
    voexec.prover_submit_vector(w, K - ell - 1)
    voexec.run_subprotocol(SparseMVPProverEfficient(),
                           pp_info["smvp_info"],
                           UnitVector(1) +
                           x.shift(1) + w.shift(ell + 1),
                           y)
    voexec.hadamard_query(PowerVector(1, n-H*3, rust_n-H*3).shift(H*3), y)
    voexec.hadamard_query(y.shift(H*2), y,
                          PowerVector(1, H).shift(H*2), y.shift(H))


class HPR(VOProtocol):
  def __init__(self):
    super(HPR, self).__init__("HPR")

  def preprocess(self, voexec, H, K, sa, sb, sc, sd):
    M = Matrix("M").as_preprocessed()

    voexec.pp_rust_concat_matrix_horizontally(
        M, K,
        "cs.arows", "cs.brows", "cs.crows",
        "cs.acols", "cs.bcols", "cs.ccols",
        "cs.avals", "cs.bvals", "cs.cvals",
        "cs.drows", "cs.dvals"
    )

    voexec.preprocess_output_pk(M)

    smvp_info = SparseMVP().preprocess(voexec, H, K * 3 + 1, sa + sb + sc + sd, M)
    return {
        "M": M,
        "H": H,
        "K": K,
        "sa": sa,
        "sb": sb,
        "sc": sc,
        "sd": sd,
        "smvp_info": smvp_info,
    }

  def execute(self, voexec, pp_info, x, w1, w2, w3):
    H, K, n = pp_info["H"], pp_info["K"], voexec.vector_size
    
    voexec.verifier_rust_define_vec(x, "x.instance.clone()")
    voexec.prover_rust_define_vec(w1, "w.witness.0.clone()")
    voexec.prover_rust_define_vec(w2, "w.witness.1.clone()")
    voexec.prover_rust_define_vec(w3, "w.witness.2.clone()")

    voexec.try_verifier_redefine_vector_size_rust("n", n)
    rust_n = voexec.rust_vector_size

    w = get_named_vector("w")
    voexec.prover_rust_define_concat_vector(w, w1, w2, w3)
    voexec.prover_submit_vector(w, 3 * K)
    voexec.run_subprotocol(SparseMVP(),
                           pp_info["smvp_info"],
                           x + w.shift(H + 1) +
                           UnitVector(H + 1))
    voexec.hadamard_query(
        w.shift(n-K, rust_n-K),
        w.shift(n-K*2, rust_n-K*2),
        PowerVector(1, K).shift(n-K, rust_n-K),
        w.shift(n-K*3, rust_n-K*3))
