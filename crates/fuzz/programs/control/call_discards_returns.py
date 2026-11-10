# expect: ok
# public_input: GEN ** 2, 0
# The doc's `f(p, q)  # statement: returns discarded`: a call statement that ignores a function's return value. The
# callee's side effect (a publish) must still happen.
from snark_lib import *


def g(x):
    p = GEN ** 0
    p[1] = x * GEN
    return x * GEN


def main():
    g(GEN)
    return
