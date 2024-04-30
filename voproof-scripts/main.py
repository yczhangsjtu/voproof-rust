from sympy import Symbol, latex, sympify, Integer, simplify, Max
from os.path import basename
from sympy.abc import alpha, beta, gamma, X, D, S
from compiler import compile, set_debug_mode
from compiler.vo_protocol import VOProtocol, VOProtocolExecution
from compiler.piop import PIOPExecution
from compiler.vo2piop import PIOPFromVOProtocol
from compiler.zksnark import ZKSNARKFromPIOPExecKZG
from compiler.symbol.vector import get_named_vector, UnitVector
from compiler.symbol.names import reset_name_counters, get_name
from compiler.builder.rust import RustBuilder, rust, RustMacro
from smvp_protocols import R1CS, R1CSProverEfficient, HPR, HPRProverEfficient
from pov_protocols import POV, POVProverEfficient
import sys

def set_r1cs_parameters():
  H = Symbol(get_name("H"), positive=True)
  K = Symbol(get_name("K"), positive=True)
  Sa = Symbol(get_name("S_a"), positive=True)
  Sb = Symbol(get_name("S_b"), positive=True)
  Sc = Symbol(get_name("S_c"), positive=True)
  ell = Symbol(get_name("ell"), positive=True)
  return H, K, Sa, Sb, Sc, ell


def analyzeR1CS():
  H, K, Sa, Sb, Sc, ell = set_r1cs_parameters()
  hints = [(H, K), (Sa, K + 1), (Sa, H + 1),
           (Sb, K + 1), (Sb, H + 1),
           (Sc, K + 1), (Sc, H + 1),
           (Sa + Sb + Sc, 3 * K + 3),
           (Sa + Sb + Sc, 3 * H + 3),
           (Sa + Sb + Sc + K, 4 * H + 3),
           (H, ell + 1)]
  size_map = [(H, "nrows"), (K, "ncols"),
              (Sa, "adensity"), (Sb, "bdensity"), (Sc, "cdensity"),
              (ell, "input_size")]
  x = get_named_vector("x").can_local_evaluate(lambda z: RustMacro("eval_vector_expression").append([
      z, Symbol("i"), x.dumpr_at_index(Symbol("i"), None), ell
  ])).does_not_contribute_to_max_shift()
  ppargs = (H, K, Sa, Sb, Sc)
  execargs = (x, get_named_vector("w"), ell)
  compile(R1CS(),
          ppargs,
          execargs,
          hints,
          size_map,
          set_r1cs_parameters,
          "voproof_r1cs")


def analyzeR1CSProverEfficient():
  H, K, Sa, Sb, Sc, ell = set_r1cs_parameters()
  hints = [(H, K), (Sa, K + 1), (Sa, H + 1),
           (Sb, K + 1), (Sb, H + 1),
           (Sc, K + 1), (Sc, H + 1),
           (Sa + Sb + Sc, 3 * K + 3),
           (Sa + Sb + Sc, 3 * H + 3),
           (Sa + Sb + Sc + K, 4 * H + 3),
           (H, ell + 1)]
  size_map = [(H, "nrows"), (K, "ncols"),
              (Sa, "adensity"), (Sb, "bdensity"), (Sc, "cdensity"),
              (ell, "input_size")]
  x = get_named_vector("x").can_local_evaluate(lambda z: RustMacro("eval_vector_expression").append([
      z, Symbol("i"), x.dumpr_at_index(Symbol("i"), None), ell
  ])).does_not_contribute_to_max_shift()
  ppargs = (H, K, Sa, Sb, Sc)
  execargs = (x, get_named_vector("w"), ell)
  compile(R1CSProverEfficient(),
          ppargs,
          execargs,
          hints,
          size_map,
          set_r1cs_parameters,
          "voproof_r1cs_prover_efficient")


def set_hpr_parameters():
  H = Symbol(get_name("H"), positive=True)
  K = Symbol(get_name("K"), positive=True)
  Sa = Symbol(get_name("S_a"), positive=True)
  Sb = Symbol(get_name("S_b"), positive=True)
  Sc = Symbol(get_name("S_c"), positive=True)
  Sd = Symbol(get_name("S_d"), positive=True)
  return H, K, Sa, Sb, Sc, Sd


def analyzeHPR():
  H, K, Sa, Sb, Sc, Sd = set_hpr_parameters()

  hints = [(Sa, H + 1), (Sa, K + 1), (Sb, H + 1), (Sb, K + 1),
           (Sc, H + 1), (Sc, K + 1), (H, Sd)]
  size_map = [(H, "nrows"), (K, "ncols"), (Sa, "adensity"), (Sb, "bdensity"),
              (Sc, "cdensity"), (Sd, "ddensity")]
  x = get_named_vector("x").can_local_evaluate(lambda z: RustMacro(
      "eval_vector_as_poly").append([x, z]))
  ppargs = (H, K, Sa, Sb, Sc, Sd)
  execargs = (x, get_named_vector("w"), get_named_vector(
      "w"), get_named_vector("w"))
  compile(HPR(),
          ppargs,
          execargs,
          hints,
          size_map,
          set_hpr_parameters,
          "voproof_hpr")

def set_pov_parameters():
  C = Symbol(get_name("C"), positive=True)
  Ca = Symbol(get_name("C_a"), positive=True)
  Cm = Symbol(get_name("C_m"), positive=True)
  Cc = Symbol(get_name("C_c"), positive=True)
  return C, Ca, Cm, Cc


def analyzePOV():
  C, Ca, Cm, Cc = set_pov_parameters()

  hints = [(C, Ca + Cm + 1), (C, 1), (Ca, 1), (Cm, 1)]
  size_map = [(Ca, "nadd"), (Cm, "nmul"), (Cc, "nconsts"), (C, "n")]
  x = get_named_vector("x").can_local_evaluate(lambda z: RustMacro(
      "eval_sparse_vector").append([z, "x.instance.0", "x.instance.1"]))
  x._rust_to_bytes_replacement = "x.instance.0, x.instance.1"
  d = get_named_vector("d").as_preprocessed()
  ppargs = (d, C - Ca - Cm, Ca, Cm)
  execargs = (x, get_named_vector("a"),
              get_named_vector("b"), get_named_vector("c"))
  compile(POV(),
          ppargs,
          execargs,
          hints,
          size_map,
          set_pov_parameters,
          "voproof_pov")


def analyzePOVProverEfficient():
  C, Ca, Cm, Cc = set_pov_parameters()

  hints = [(C, Ca + Cm + 1), (C, 1), (Ca, 1), (Cm, 1)]
  size_map = [(Ca, "nadd"), (Cm, "nmul"), (Cc, "nconsts"), (C, "n")]
  x = get_named_vector("x").can_local_evaluate(lambda z:
    RustMacro("eval_sparse_vector")
    .append([z, "x.instance.0", "x.instance.1"]))
  x._rust_to_bytes_replacement = "x.instance.0, x.instance.1"
  d = get_named_vector("d").as_preprocessed()
  ppargs = (d, C - Ca - Cm, Ca, Cm)
  execargs = (x, get_named_vector("a"),
              get_named_vector("b"), get_named_vector("c"))
  compile(POVProverEfficient(),
          ppargs,
          execargs,
          hints,
          size_map,
          set_pov_parameters,
          "voproof_pov_prover_efficient")


if __name__ == '__main__':
  if "debug" in sys.argv:
    set_debug_mode()
    
  if "r1cs" in sys.argv:
    if "pe" in sys.argv:
      analyzeR1CSProverEfficient()
    else:
      analyzeR1CS()
  
  if "hpr" in sys.argv:
    analyzeHPR()
  
  if "pov" in sys.argv:
    if "pe" in sys.argv:
      analyzePOVProverEfficient()
    else:
      analyzePOV()
