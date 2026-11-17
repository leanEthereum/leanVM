# Fibonacci in the exponent: cell fib[g^k] holds GEN ** F_k, and the field
# product adds exponents: one MUL per Fibonacci step. The evolving state is
# carried through a HeapBuf (a mul_range body cannot capture a StackBuf).
# public_input: GEN ** 89, GEN ** 89
from snark_lib import *


def main():
    fib = HeapBuf(12)
    fib[1] = GEN ** 0  # F_0 = 0
    fib[GEN] = GEN     # F_1 = 1
    for i in mul_range(1, GEN ** 10):
        fib[i * GEN * GEN] = fib[i] * fib[i * GEN]
    out = fib[GEN ** 11]
    assert out == GEN ** 89  # F_11 = 89
    assert log(out) < log(GEN ** 128)
    p = GEN ** 0
    p[1] = out
    p[GEN] = out
    return
