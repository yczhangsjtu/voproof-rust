from sympy import Symbol, latex, sympify, Integer, simplify
from sympy.abc import alpha, beta, gamma  # , X, D, S
from compiler.vo_protocol import VOProtocol, VOProtocolExecution
from compiler.symbol.util import rust_pk
from compiler.symbol.vector import get_named_vector, PowerVector, UnitVector
from compiler.symbol.names import reset_name_counters, get_name
from compiler.builder.latex import Math
from compiler.builder.rust import *

sym_i = Symbol("i")


class ProductEq(VOProtocol):
  def __init__(self):
    super(ProductEq, self).__init__("ProductEq")

  def execute(self, voexec, pp_info, u, v, ell):
    n = voexec.vector_size
    voexec.try_verifier_redefine_vector_size_rust("n", n)
    rust_n = voexec.rust_vector_size

    r = get_named_vector("r")
    voexec.prover_rust_define_accumulate_vector_mul(
        r,
        rust_mul(u.dumpr_at_index(sym_i, voexec.coeff_manager),
                 rust_inverse(v.dumpr_at_index(sym_i, voexec.coeff_manager))),
        ell)

    voexec.prover_submit_vector(r, ell)
    voexec.hadamard_query(
        r.shift(n - ell + 1, rust_n - ell + 1) +
        UnitVector(n - ell + 1, rust_n - ell + 1),
        u.shift(n - ell, rust_n - ell),
        r.shift(n - ell, rust_n - ell),
        v.shift(n - ell, rust_n - ell),
    )
    voexec.hadamard_query(
        r - UnitVector(ell),
        UnitVector(ell),
    )

class Permute(VOProtocol):
  def __init__(self):
    super(Permute, self).__init__("Permute")

  def execute(self, voexec, pp_info, u, v, ell):
    zeta = Symbol(get_name("zeta"))
    voexec.verifier_send_randomness(zeta)
    voexec.run_subprotocol(ProductEq(),
                           {},
                           u + zeta * PowerVector(1, ell),
                           v + zeta * PowerVector(1, ell),
                           ell)


class CopyCheck(VOProtocol):
  def __init__(self):
    super(CopyCheck, self).__init__("CopyCheck")

  def preprocess(self, voexec: VOProtocolExecution, ell):
    vsigma = voexec.preprocess_named_vector_as_pk("sigma", ell)
    voexec.pp_rust_define_permutation_vector_from_wires(
        vsigma, "cs.wires", ell)
    
    return {
      "ell": ell,
      "vsigma": vsigma,
    }

  def execute(self, voexec: VOProtocolExecution, pp_info, v):
    ell = pp_info["ell"]
    zeta = Symbol(get_name("zeta"))
    voexec.verifier_send_randomness(zeta)
    voexec.run_subprotocol(Permute(),
                           {},
                           v + zeta * PowerVector(gamma, ell),
                           v + zeta * pp_info["vsigma"], ell)

class POV(VOProtocol):
  def __init__(self):
    super(POV, self).__init__("POV")

  def preprocess(self, voexec: VOProtocolExecution, d, Cc, Ca, Cm):
    C = Cc + Ca + Cm

    cc_info = CopyCheck().preprocess(voexec, 3 * C)

    voexec.preprocess_vector(d, Cc)

    """
    The vector d will never be shifted outside the n-window
    """
    d._do_not_count_shifts = True
    
    return {
      "d": d,
      "Ca": Ca,
      "Cm": Cm,
      "Cc": Cc,
      "C": C,
      "d": d,
      "cc_info": cc_info,
    }

  def execute(self, voexec: VOProtocolExecution, pp_info, x, a, b, c):

    C, Cc, Ca, Cm, d, n = pp_info["C"], pp_info["Cc"], \
      pp_info["Ca"], pp_info["Cm"], pp_info["d"], voexec.vector_size

    # The expression of n is so complex. Put it in a variable.
    voexec.try_verifier_redefine_vector_size_rust("n", n)
    rust_n = voexec.rust_vector_size

    w = get_named_vector("w")
    voexec.prover_rust_define_concat_vector(w, a, b, c)
    voexec.prover_submit_vector(w, 3 * C)

    t = get_named_vector("t").can_local_evaluate(
      lambda z: RustMacro(
        "eval_sparse_zero_one_vector"
      ).append([z, "x.instance.0"])
    )
    voexec.prover_rust_define_sparse_zero_one_vector(t, "x.instance.0", 3 * C)

    voexec.hadamard_query(
        w.shift(n-Cm, rust_n-Cm),
        w.shift(n-Cm-C, rust_n-Cm-C),
        PowerVector(1, Cm).shift(n-Cm, rust_n-Cm),
        w.shift(n-Cm-2*C, rust_n-Cm-2*C),
    )
    voexec.hadamard_query(
        PowerVector(1, Ca).shift(2*C+Cm),
        w.shift(C*2) + w.shift(C) - w
    )
    voexec.hadamard_query(
        PowerVector(1, Cc).shift(2*C+Cm+Ca),
        w - d.shift(2*C+Cm+Ca)
    )
    voexec.hadamard_query(t, w - x)
    voexec.run_subprotocol(CopyCheck(), pp_info["cc_info"], w)


class POVProverEfficient(VOProtocol):
  def __init__(self):
    super(POVProverEfficient, self).__init__("POV")

  def preprocess(self, voexec, d, Cc, Ca, Cm):
    C = Cc + Ca + Cm
    cc_info = CopyCheck().preprocess(voexec, 3 * C)

    voexec.preprocess_vector(d, Cc)

    """
    The vector d will never be shifted outside the n-window
    """
    d._do_not_count_shifts = True
    
    return {
      "Ca": Ca,
      "Cm": Cm,
      "Cc": Cc,
      "C": C,
      "d": d,
      "cc_info": cc_info,
    }

  def execute(self, voexec, pp_info, x, a, b, c):

    C, Cc, Ca, Cm, d, n = pp_info["C"], pp_info["Cc"], \
      pp_info["Ca"], pp_info["Cm"], pp_info["d"], voexec.vector_size

    # The expression of n is so complex. Put it in a variable.
    voexec.try_verifier_redefine_vector_size_rust("n", n)

    u = get_named_vector("u")
    v = get_named_vector("v")
    voexec.prover_rust_define_concat_subvec(u, a, 0, C, b, 0, Cm)
    voexec.prover_rust_define_concat_subvec(v, b, Cm, C, c, 0, Cm+Ca)
    voexec.prover_submit_vector(u, C)
    voexec.prover_submit_vector(v, C)

    t = get_named_vector("t").can_local_evaluate(
      lambda z: RustMacro(
        "eval_sparse_zero_one_vector"
      ).append([z, "x.instance.0"])
    )
    voexec.prover_rust_define_sparse_zero_one_vector(t, "x.instance.0", 3 * C)

    voexec.hadamard_query(
        u.shift(C),
        u,
        PowerVector(1, Cm).shift(C),
        v.shift(Cm)
    )
    voexec.hadamard_query(
        PowerVector(1, Ca).shift(C),
        u.shift(Ca+Cc) + v.shift(C) - v
    )
    voexec.hadamard_query(t, u + v.shift(C+Cm) - x)
    voexec.run_subprotocol(CopyCheck(),
                           pp_info["cc_info"],
                           u + v.shift(C+Cm) + d.shift(3*C-Cc))
