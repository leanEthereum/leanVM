# expect: ok
# public_input: GEN, 0
# A non-main function with no trailing return (the doc asks for one), followed by a function whose body stores 77
# into a public cell: if the compiler let `f` fall through into `h`, that store would conflict.
from snark_lib import *


def f(x):
    hb = HeapBuf(1)
    hb[1] = x


def h(x):
    q = GEN ** 0
    q[GEN] = 77
    return x * GEN


def main():
    f(GEN)
    p = GEN ** 0
    p[1] = GEN
    return
