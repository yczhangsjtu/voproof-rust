from sympy import Symbol
from compiler import compile, generate_size_symbols, set_debug_mode
from compiler.vo_protocol import VOProtocol, VOProtocolExecution
from compiler.symbol.vector import get_named_vector, PowerVector, UnitVector
from compiler.symbol.names import get_name
from compiler.builder.rust import rust

class Fibonacci(VOProtocol):
    def __init__(self):
        super(Fibonacci, self).__init__("Fibonacci")
    
    def preprocess(self, voexec: VOProtocolExecution, n):
        voexec.pp_rust_init_size(n, "n")

        t = get_named_vector("t")
        voexec.pp_rust_define_vec(t, "cs.t.clone()")
        voexec.preprocess_vector(t, n)

        return {
            "t": t
        }
    
    def execute(self, voexec: VOProtocolExecution, pp_info, n):
        t = pp_info["t"]
        voexec.verifier_rust_init_size(n, "n")

        a, b, c = Symbol(get_name("a")), Symbol(get_name("b")), Symbol(get_name("c"))
        voexec.verifier_rust_define(a, "x.a")
        voexec.verifier_rust_define(b, "x.b")
        voexec.verifier_rust_define(c, "x.c")

        w = get_named_vector("w")
        voexec.prover_rust_define_vec(w, "w.witness.clone()")
        voexec.prover_submit_vector(w, n)

        r = get_named_vector("r")
        voexec.prover_rust_define_vec(r,
f"""
[zero!()].iter()
         .chain({rust(w)}.iter())
         .take({n} as usize)
         .zip(pk.{rust(t)}.iter())
         .map(|(&a,&b)|a*b)
         .collect::<Vec<_>>()
""")
        voexec.prover_submit_vector(r, n)

        voexec.hadamard_query(
            w - a * UnitVector(1) - b * t,
            UnitVector(1)
        )
        voexec.hadamard_query(
            r,
            PowerVector(1, n),
            w.shift(1),
            t
        )
        voexec.hadamard_query(
            w - b * UnitVector(2) - r,
            UnitVector(2)
        )
        voexec.hadamard_query(
            w - c * UnitVector(n),
            UnitVector(n)
        )
        voexec.hadamard_query(
            w - w.shift(2) - r,
            PowerVector(1, n) - UnitVector(1) - UnitVector(2)
        )

if __name__ == "__main__":
    set_debug_mode()
    symbols = generate_size_symbols(n = "n")
    n = symbols["n"]
    compile(Fibonacci().with_preprocess_args(n).with_execute_args(n),
            symbols, "fibonacci")