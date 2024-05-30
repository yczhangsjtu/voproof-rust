from sympy import Symbol
from compiler import compile, generate_size_symbols, set_debug_mode
from compiler.vo_protocol import VOProtocol, VOProtocolExecution
from compiler.symbol.vector import get_named_vector, PowerVector, UnitVector
from compiler.symbol.names import get_name
from compiler.builder.rust import rust
from pov_protocols import Lookup

class RangeCheck(VOProtocol):
    def __init__(self):
        super(RangeCheck, self).__init__("RangeCheck")
    
    def preprocess(self, voexec: VOProtocolExecution, n, range):
        voexec.pp_rust_init_size(n, "lookup_size")
        voexec.pp_rust_init_size(range, "range")

        t = get_named_vector("t")
        voexec.pp_rust_define_vec(t,
f"""(0..{rust(range)}).map(|x| to_field::<E::ScalarField>(x as u64))
                      .collect::<Vec<_>>()
""")
        voexec.preprocess_vector(t, n)

        return {
            "t": t,
            "n": n,
            "range": range
        }
    
    def execute(self, voexec: VOProtocolExecution, pp_info):
        t, n, range = pp_info["t"], pp_info["n"], pp_info["range"]
        voexec.verifier_rust_init_size(range, "range")
        voexec.verifier_rust_init_size(n, "lookup_size")

        w = get_named_vector("w")
        voexec.prover_rust_define_vec(w, "w.witness.clone()")
        voexec.prover_submit_vector(w, n)
        voexec.run_subprotocol(Lookup(), pp_info, w, t, n, range)

if __name__ == "__main__":
    set_debug_mode()
    symbols = generate_size_symbols(lookup_size = "nsize", range = "range")
    n, range = symbols["lookup_size"], symbols["range"]
    compile(RangeCheck().with_preprocess_args(n, range).with_execute_args(),
            symbols, "range_check")