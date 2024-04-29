from sympy import Symbol, latex, sympify, Integer, simplify, Max
from os.path import basename
from sympy.abc import alpha, beta, gamma, X, D, S
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

ell = Symbol("ell", positive=True)
m = Symbol("m", positive=True)
# n = Symbol("n", positive=True)
H = Symbol("H", positive=True)
K = Symbol("K", positive=True)
s = Symbol("s", positive=True)

Cc = Symbol("C_c", positive=True)
Ca = Symbol("C_a", positive=True)
Cm = Symbol("C_m", positive=True)
Sa = Symbol("S_a", positive=True)
Sb = Symbol("S_b", positive=True)
Sc = Symbol("S_c", positive=True)

k = Symbol("k", positive=True)


def dump_performance(piopexec, zkSNARK, name):
  voexec = piopexec.reference_to_voexec
  print("%s preprocessed polynomials: %d" %
        (name, len(piopexec.indexer_polynomials)))
  print("%s online polynomials: %d" % (name, len(piopexec.prover_polynomials)))
  n_distinct = len(piopexec.distinct_points)
  print("%s distinct points: %d" % (name, n_distinct))
  n_evals = len(piopexec.eval_queries) + len(piopexec.eval_checks)
  print("%s eval queries: %d" % (name, n_evals))
  print("%s max degree: %s" % (name, latex(piopexec.max_degree)))
  print("%s minimal n: %s" % (name, latex(voexec.vector_size_bound)))
  n_field_elements = len(
      [p for p in zkSNARK.proof if latex(p).startswith("y")])
  print("%s proof size: %d G + %d F" %
        (name, len(zkSNARK.proof) - n_field_elements, n_field_elements))
  c_g_exps = sum([len(poly_combine.coeff_builders)
                 for poly_combine in piopexec.poly_combines])
  v_g_exps = n_evals + 2 * n_distinct - 2 + c_g_exps
  print("%s verifier G-exps: %d" % (name, v_g_exps))
  p_g_exps = c_g_exps + piopexec.max_degree * 4 + voexec.vector_size_sum
  print("%s prover G-exps: %s" % (name, latex(p_g_exps)))
  print()


def get_minimal_vector_size(protocol, ppargs, execargs, simplify_hints):
  voexec = VOProtocolExecution(Symbol("N"))
  voexec._simplify_max_hints = simplify_hints
  protocol.preprocess(voexec, *ppargs)
  protocol.execute(voexec, *execargs)
  reset_name_counters()
  return voexec.vector_size_bound


def analyzeProtocol(protocol, ppargs, execargs, simplify_hints, size_map, set_parameters,
                    filename=None):
  name = protocol.__class__.__name__
  csname = protocol.name
  n = get_minimal_vector_size(protocol, ppargs, execargs, simplify_hints)
  set_parameters()

  debug("Start analyzing %s..." % name)
  piop = PIOPFromVOProtocol(protocol, n, D)
  piop.debug_mode = debug_mode
  piop.debug_check_hadamard_side = debug_check_hadamard_side
  debug("Start preprocessing...")
  piopexec = PIOPExecution()

  piop.preprocess(piopexec, *ppargs)
  piopexec.reference_to_voexec._simplify_max_hints = simplify_hints
  debug("Start executing...")
  piop.execute(piopexec, *execargs)
  piopexec.max_degree = piopexec.reference_to_voexec.simplify_max(
      piopexec.max_degree)

  size_init = rust(piopexec.max_degree)
  for size, value in size_map:
    size_init = size_init.replace(rust(size), "(size.{} as i64)".format(value))

  debug("Start compiling to zkSNARK...")
  zkSNARK = ZKSNARKFromPIOPExecKZG(piopexec)
  debug()
  dump_performance(piopexec, zkSNARK, name)

  if filename is not None:
    with open("../voproof/src/snarks/template.rs") as template:
      temp = template.readlines()
    mark_content_map = [("__NAME__", name),
                        ("__CSNAME__", csname),
                        ("/*{size}*/",
                         "(%s) as usize" % size_init),
                        ("/*{VerifierKey}*/", zkSNARK.dump_vk_definition()),
                        ("/*{index verifier key}*/",
                         zkSNARK.dump_vk_construction()),
                        ("/*{ProverKey}*/", zkSNARK.dump_pk_definition()),
                        ("/*{Proof}*/", zkSNARK.dump_proof_definition()),
                        ("/*{index prover key}*/",
                         zkSNARK.dump_pk_construction()),
                        ("/*{proof}*/", zkSNARK.dump_proof_construction()),
                        ("/*{index}*/", zkSNARK.dump_indexer_rust()),
                        ("/*{prove}*/", zkSNARK.dump_prover_rust()),
                        ("/*{verify}*/", zkSNARK.dump_verifier_rust()),
                        ]

    for i in range(len(temp)):
      for mark, content in mark_content_map:
        if mark in temp[i]:
          temp[i] = temp[i].replace(mark, content)
    temp = "".join(temp)

    with open("../voproof/src/snarks/%s.rs" % filename, "w") as f:
      print("///! This file is generated by "
            "https://github.com/yczhangsjtu/voproof-scripts/%s"
            % basename(__file__), file=f)
      print(temp, file=f)

  reset_name_counters()


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
  x = get_named_vector("x")
  x.local_evaluate = True
  x._do_not_count_shifts = True
  x.hint_computation = lambda z: RustMacro("eval_vector_expression").append([
      z, Symbol("i"), x.dumpr_at_index(Symbol("i"), None), ell
  ])
  ppargs = (H, K, Sa, Sb, Sc)
  execargs = (x, get_named_vector("w"), ell)
  analyzeProtocol(R1CS(), ppargs, execargs, hints, size_map, set_r1cs_parameters,
                  filename="voproof_r1cs")


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
  x = get_named_vector("x")
  x.local_evaluate = True
  x._do_not_count_shifts = True
  x.hint_computation = lambda z: RustMacro("eval_vector_expression").append([
      z, Symbol("i"), x.dumpr_at_index(Symbol("i"), None), ell
  ])
  ppargs = (H, K, Sa, Sb, Sc)
  execargs = (x, get_named_vector("w"), ell)
  analyzeProtocol(R1CSProverEfficient(), ppargs, execargs,
                  hints, size_map, set_r1cs_parameters,
                  filename=None if dry_run else "voproof_r1cs_prover_efficient")


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
  x = get_named_vector("x")
  x.local_evaluate = True
  x.hint_computation = lambda z: RustMacro(
      "eval_vector_as_poly").append([x, z])
  ppargs = (H, K, Sa, Sb, Sc, Sd)
  execargs = (x, get_named_vector("w"), get_named_vector(
      "w"), get_named_vector("w"))
  analyzeProtocol(HPR(), ppargs, execargs, hints, size_map, set_hpr_parameters,
                  filename=None if dry_run else "voproof_hpr")


def analyzeHPRProverEfficient():
  H, K, S, ell, Sp = set_hpr_parameters()

  hints = [(S, H + 1), (S, K + 1), (H, Sp),
           (K, ell), (H, ell), (S, ell + 1), (H, K)]
  size_map = [(H, "nrows"), (K, "ncols"), (S, "density"), (Sp, "d_density")]
  x = get_named_vector("x")
  x.local_evaluate = True
  ppargs = (H, K, S*3+Sp)
  execargs = (x, get_named_vector("w"), get_named_vector(
      "w"), get_named_vector("w"), ell)
  analyzeProtocol(HPRProverEfficient(), ppargs, execargs,
                  hints, size_map, set_hpr_parameters, filename=None if dry_run else "voproof_hpr_prover_efficient")


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
  x = get_named_vector("x")
  x.local_evaluate = True
  x.hint_computation = lambda z: RustMacro(
      "eval_sparse_vector").append([z, "x.instance.0", "x.instance.1"])
  x._rust_to_bytes_replacement = "x.instance.0, x.instance.1"
  d = get_named_vector("d")
  d._is_preprocessed = True
  ppargs = (d, C - Ca - Cm, Ca, Cm)
  execargs = (x, get_named_vector("a"),
              get_named_vector("b"), get_named_vector("c"))
  analyzeProtocol(POV(), ppargs, execargs, hints, size_map, set_pov_parameters,
                  filename=None if dry_run else "voproof_pov")


def analyzePOVProverEfficient():
  C, Ca, Cm, Cc = set_pov_parameters()

  hints = [(C, Ca + Cm + 1), (C, 1), (Ca, 1), (Cm, 1)]
  size_map = [(Ca, "nadd"), (Cm, "nmul"), (Cc, "nconsts"), (C, "n")]
  x = get_named_vector("x")
  x.local_evaluate = True
  x.hint_computation = lambda z: RustMacro(
      "eval_sparse_vector").append([z, "x.instance.0", "x.instance.1"])
  x._rust_to_bytes_replacement = "x.instance.0, x.instance.1"
  d = get_named_vector("d")
  d._is_preprocessed = True
  ppargs = (d, C - Ca - Cm, Ca, Cm)
  execargs = (x, get_named_vector("a"),
              get_named_vector("b"), get_named_vector("c"))
  analyzeProtocol(POVProverEfficient(), ppargs, execargs,
                  hints, size_map, set_pov_parameters, filename=None if dry_run else "voproof_pov_prover_efficient")


debug_mode = False
debug_check_hadamard_side = False
dry_run = True


def debug(info=""):
  if debug_mode:
    print(info)


if __name__ == '__main__':
  if "debug" in sys.argv:
    debug_mode = True
  analyzeR1CSProverEfficient()
  # analyzeHPRProverEfficient()
  analyzePOVProverEfficient()
  analyzeR1CS()
  analyzeHPR()
  analyzePOV()
