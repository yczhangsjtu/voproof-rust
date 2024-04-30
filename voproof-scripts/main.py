from sympy import Symbol
from compiler import compile, set_debug_mode
from compiler.symbol.vector import get_named_vector
from compiler.symbol.names import get_name
from compiler.builder.rust import RustMacro
from smvp_protocols import R1CS, R1CSProverEfficient, HPR
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
  compile(R1CS()
          .with_preprocess_args(H, K, Sa, Sb, Sc)
          .with_execute_args(x, get_named_vector("w"), ell),
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
  compile(R1CSProverEfficient()
          .with_preprocess_args(H, K, Sa, Sb, Sc)
          .with_execute_args(x, get_named_vector("w"), ell),
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
  compile(HPR()
          .with_preprocess_args(H, K, Sa, Sb, Sc, Sd)
          .with_execute_args(x, get_named_vector("w"), get_named_vector(
      "w"), get_named_vector("w")),
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
  compile(POV()
          .with_preprocess_args(d, C - Ca - Cm, Ca, Cm)
          .with_execute_args(x, get_named_vector("a"),
              get_named_vector("b"), get_named_vector("c")),
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
  compile(POVProverEfficient()
          .with_preprocess_args(d, C - Ca - Cm, Ca, Cm)
          .with_execute_args(x, get_named_vector("a"),
              get_named_vector("b"), get_named_vector("c")),
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
