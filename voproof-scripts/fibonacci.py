from sympy import Symbol
from compiler import compile, generate_size_symbols, set_debug_mode
from compiler.vo_protocol import VOProtocol, VOProtocolExecution
from compiler.symbol.vector import get_named_vector, PowerVector, UnitVector
from compiler.symbol.names import get_name
from compiler.builder.rust import rust

class Fibonacci(VOProtocol):
    def __init__(self):
        super(Fibonacci, self).__init__("Fibonacci")
    
    def preprocess(self, voexec):
        return {}
    
    def execute(self, voexec: VOProtocolExecution, pp_info, n):
        voexec.verifier_rust_init_size(n, "n")

        a, b, c, a_plus_2b = Symbol(get_name("a")), Symbol(get_name("b")), Symbol(get_name("c")), Symbol(get_name("aplus2b"))
        voexec.verifier_rust_define(a, "x.a")
        voexec.verifier_rust_define(b, "x.b")
        voexec.verifier_rust_define(c, "x.c")
        voexec.verifier_rust_define(a_plus_2b, rust(a + 2 * b, to_field=True))

        w = get_named_vector("w")
        voexec.prover_rust_define_vec(w, "w.witness.clone()")
        voexec.prover_submit_vector(w, n)

        voexec.hadamard_query(
            w,
            UnitVector(1) + UnitVector(2) + UnitVector(n),
            UnitVector(1) * (a + b) + UnitVector(2) * a_plus_2b + UnitVector(n) * c,
            PowerVector(1, n),
        )
        voexec.hadamard_query(
            w.shift(1) + w.shift(2) - w,
            PowerVector(1, n) - UnitVector(1) - UnitVector(2)
        )

if __name__ == "__main__":
    symbols = generate_size_symbols(n = "n")
    n = symbols["n"]
    compile(Fibonacci().with_preprocess_args().with_execute_args(n),
            symbols, "fibonacci")