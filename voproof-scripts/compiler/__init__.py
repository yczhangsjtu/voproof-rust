from sympy import Symbol, latex, sympify, Integer, simplify, Max
from os.path import basename
from sympy.abc import alpha, beta, gamma, X, D, S
from .vo_protocol import VOProtocol, VOProtocolExecution
from .piop import PIOPExecution
from .vo2piop import PIOPFromVOProtocol
from .pc_protocol import ProverComputes, VerifierComputes
from .zksnark import ZKSNARKFromPIOPExecKZG
from .symbol.vector import get_named_vector, UnitVector
from .symbol.names import reset_name_counters, get_name
from .builder.rust import RustBuilder, rust, RustMacro

debug_mode = False
debug_check_hadamard_side = False
dry_run = False

def set_debug_mode():
    global debug_mode
    debug_mode = True

def debug(info=""):
  if debug_mode:
    print(info)

def set_dry_run():
  global dry_run
  dry_run = True

def generate_size_symbols(**kwargs):
  symbols = {}
  for key, value in kwargs.items():
    symbols[key] = Symbol(get_name(value), positive=True)
  return symbols
  
def get_minimal_vector_size(protocol, ppargs, execargs, simplify_hints):
  voexec = VOProtocolExecution(Symbol("N"))
  voexec._simplify_max_hints = simplify_hints
  protocol.preprocess(voexec, *ppargs)
  protocol.execute(voexec, *execargs)
  reset_name_counters()
  return voexec.vector_size_bound

def dump_performance(piopexec, zkSNARK, name):
  voexec = piopexec.reference_to_voexec
  if piopexec.indexer_polynomials is not None:
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

def compile(protocol: VOProtocol,
            symbols,
            filename=None):
  name = protocol.__class__.__name__
  csname = protocol.name
  n = protocol.get_minimal_vector_size()
  # Reinvoke this procedure here to make the name counter correct
  for symbol in symbols.values():
      get_name(symbol.name)

  debug("Start analyzing %s..." % name)
  piop = PIOPFromVOProtocol(protocol, n, D)
  piop.debug_mode = debug_mode
  piop.debug_check_hadamard_side = debug_check_hadamard_side
  debug("Start preprocessing...")
  piopexec = PIOPExecution()
  for rust_name, symbol in symbols.items():
    piopexec.pp_rust_init_size(symbol, rust_name)
  piopexec.pp_rust_define_generator()
  for pp in protocol._before_exec.preprocessings:
    piopexec.preprocess(pp.latex_builder, pp.rust_builder)

  pp_info = piop.preprocess(piopexec)
  debug("Start executing...")
  
  for rust_name, symbol in symbols.items():
    piopexec.verifier_rust_init_size(symbol, rust_name)
  piopexec.verifier_rust_define_generator()
  
  for interaction in protocol._before_exec.interactions:
    if isinstance(interaction, ProverComputes):
      piopexec.prover_computes(
            interaction.latex_builder, interaction.rust_builder)
    elif isinstance(interaction, VerifierComputes):
      piopexec.verifier_computes(
            interaction.latex_builder, interaction.rust_builder)
  
  piop.execute(piopexec, pp_info)
  piopexec.max_degree = piopexec.reference_to_voexec.simplify_max(
      piopexec.max_degree)

  size_init = rust(piopexec.max_degree)
  for var_name, size in symbols.items():
    size_init = size_init.replace(rust(size), "(size.{} as i64)".format(var_name))

  debug("Start compiling to zkSNARK...")
  zkSNARK = ZKSNARKFromPIOPExecKZG(piopexec)
  debug()
  dump_performance(piopexec, zkSNARK, name)

  if not dry_run and filename is not None:
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
            "https://github.com/yczhangsjtu/voproof-rust/voproof-scripts/%s"
            % basename(__file__), file=f)
      print(temp, file=f)

  reset_name_counters()