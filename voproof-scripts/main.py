from sympy import Symbol
from compiler import compile, set_debug_mode, generate_size_symbols
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
  symbols = generate_size_symbols(nrows="H", ncols="K",
                                  adensity="S_a", bdensity="S_b",
                                  cdensity="S_c", input_size="ell")
  H, K, Sa, Sb, Sc, ell = symbols["nrows"], symbols["ncols"], \
                          symbols["adensity"], symbols["bdensity"], \
                          symbols["cdensity"], symbols["input_size"]
  x = get_named_vector("x").can_local_evaluate_dense().does_not_contribute_to_max_shift()
  w = get_named_vector("w")
  compile(R1CS()
          .with_preprocess_args(H, K, Sa, Sb, Sc)
          .with_execute_args(x, w, ell)
          .size_hint_larger_than(H, K)
          .size_hint_larger_than(Sa, K + 1)
          .size_hint_larger_than(Sa, H + 1)
          .size_hint_larger_than(Sb, K + 1)
          .size_hint_larger_than(Sb, H + 1)
          .size_hint_larger_than(Sc, K + 1)
          .size_hint_larger_than(Sc, H + 1)
          .size_hint_larger_than(Sa + Sb + Sc, 3 * K + 3)
          .size_hint_larger_than(Sa + Sb + Sc, 3 * H + 3)
          .size_hint_larger_than(Sa + Sb + Sc + K, 4 * H + 3)
          .size_hint_larger_than(H, ell + 1)
          .with_instances(x)
          .with_witnesses(w),
          symbols,
          "voproof_r1cs")


def analyzeR1CSProverEfficient():
  symbols = generate_size_symbols(nrows="H", ncols="K",
                                  adensity="S_a", bdensity="S_b",
                                  cdensity="S_c", input_size="ell")
  H, K, Sa, Sb, Sc, ell = symbols["nrows"], symbols["ncols"], \
                          symbols["adensity"], symbols["bdensity"], \
                          symbols["cdensity"], symbols["input_size"]
  x = get_named_vector("x").can_local_evaluate_dense().does_not_contribute_to_max_shift()
  w = get_named_vector("w")
  compile(R1CSProverEfficient()
          .with_preprocess_args(H, K, Sa, Sb, Sc)
          .with_execute_args(x, w, ell)
          .size_hint_larger_than(H, K)
          .size_hint_larger_than(Sa, K + 1)
          .size_hint_larger_than(Sa, H + 1)
          .size_hint_larger_than(Sb, K + 1)
          .size_hint_larger_than(Sb, H + 1)
          .size_hint_larger_than(Sc, K + 1)
          .size_hint_larger_than(Sc, H + 1)
          .size_hint_larger_than(Sa + Sb + Sc, 3 * K + 3)
          .size_hint_larger_than(Sa + Sb + Sc, 3 * H + 3)
          .size_hint_larger_than(Sa + Sb + Sc + K, 4 * H + 3)
          .size_hint_larger_than(H, ell + 1)
          .with_instances(x)
          .with_witnesses(w),
          symbols,
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
  symbols = generate_size_symbols(nrows="H", ncols="K",
                                  adensity="S_a", bdensity="S_b",
                                  cdensity="S_c", ddensity="S_d")
  H, K, Sa, Sb, Sc, Sd = symbols["nrows"], symbols["ncols"], \
                         symbols["adensity"], symbols["bdensity"], \
                         symbols["cdensity"], symbols["ddensity"]

  x = get_named_vector("x").can_local_evaluate_dense()
  w1 = get_named_vector("w")
  w2 = get_named_vector("w")
  w3 = get_named_vector("w")
  compile(HPR()
          .with_preprocess_args(H, K, Sa, Sb, Sc, Sd)
          .with_execute_args(x, w1, w2, w3)
          .size_hint_larger_than(Sa, H + 1)
          .size_hint_larger_than(Sa, K + 1)
          .size_hint_larger_than(Sb, H + 1)
          .size_hint_larger_than(Sb, K + 1)
          .size_hint_larger_than(Sc, H + 1)
          .size_hint_larger_than(Sc, K + 1)
          .size_hint_larger_than(H, Sd)
          .with_instances(x)
          .with_witnesses(w1, w2, w3),
          symbols,
          "voproof_hpr")

def set_pov_parameters():
  C = Symbol(get_name("C"), positive=True)
  Ca = Symbol(get_name("C_a"), positive=True)
  Cm = Symbol(get_name("C_m"), positive=True)
  Cc = Symbol(get_name("C_c"), positive=True)
  return C, Ca, Cm, Cc


def analyzePOV():
  symbols = generate_size_symbols(n="C_total",
                                  nadd="C_a",
                                  nmul="C_m",
                                  nconsts="C_c")
  C, Ca, Cm = symbols["n"], symbols["nadd"], symbols["nmul"]
  
  x = get_named_vector("x").as_sparse_instance()
  d = get_named_vector("d").as_preprocessed()
  a = get_named_vector("a")
  b = get_named_vector("b")
  c = get_named_vector("c")
  compile(POV()
          .with_preprocess_args(d, C - Ca - Cm, Ca, Cm)
          .with_execute_args(x, a, b, c)
          .size_hint_larger_than(C, Ca + Cm + 1)
          .size_hint_larger_than(C, 1)
          .size_hint_larger_than(Ca, 1)
          .size_hint_larger_than(Cm, 1)
          .before_pp_rust_define(d, "cs.consts.clone()")
          .before_prover_rust_define_sparse_vector(x, "x.instance.0", "x.instance.1", 3 * C)
          .before_prover_rust_define_vec(a, "w.witness.0.clone()")
          .before_prover_rust_define_vec(b, "w.witness.1.clone()")
          .before_prover_rust_define_vec(c, "w.witness.2.clone()")
          .with_instances(x)
          .with_witnesses(a, b, c),
          symbols,
          "voproof_pov")


def analyzePOVProverEfficient():
  symbols = generate_size_symbols(n="C_total",
                                  nadd="C_a",
                                  nmul="C_m",
                                  nconsts="C_c")
  C, Ca, Cm = symbols["n"], symbols["nadd"], symbols["nmul"]
  
  x = get_named_vector("x").as_sparse_instance()
  d = get_named_vector("d").as_preprocessed()
  a = get_named_vector("a")
  b = get_named_vector("b")
  c = get_named_vector("c")
  compile(POVProverEfficient()
          .with_preprocess_args(d, C - Ca - Cm, Ca, Cm)
          .with_execute_args(x, a, b, c)
          .size_hint_larger_than(C, Ca + Cm + 1)
          .size_hint_larger_than(C, 1)
          .size_hint_larger_than(Ca, 1)
          .size_hint_larger_than(Cm, 1)
          .before_pp_rust_define(d, "cs.consts.clone()")
          .before_prover_rust_define_sparse_vector(x, "x.instance.0", "x.instance.1", 3 * C)
          .before_prover_rust_define_vec(a, "w.witness.0.clone()")
          .before_prover_rust_define_vec(b, "w.witness.1.clone()")
          .before_prover_rust_define_vec(c, "w.witness.2.clone()")
          .with_instances(x)
          .with_witnesses(a, b, c),
          symbols,
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
