# expect: ok
# public_input: GEN ** 20, 0
# Twenty small functions chained, each calling the next: many frames and return addresses, and each step multiplies
# by g, so a dropped or doubled call changes the exponent.
from snark_lib import *


def f0(x):
    return f1(x * GEN)


def f1(x):
    return f2(x * GEN)


def f2(x):
    return f3(x * GEN)


def f3(x):
    return f4(x * GEN)


def f4(x):
    return f5(x * GEN)


def f5(x):
    return f6(x * GEN)


def f6(x):
    return f7(x * GEN)


def f7(x):
    return f8(x * GEN)


def f8(x):
    return f9(x * GEN)


def f9(x):
    return f10(x * GEN)


def f10(x):
    return f11(x * GEN)


def f11(x):
    return f12(x * GEN)


def f12(x):
    return f13(x * GEN)


def f13(x):
    return f14(x * GEN)


def f14(x):
    return f15(x * GEN)


def f15(x):
    return f16(x * GEN)


def f16(x):
    return f17(x * GEN)


def f17(x):
    return f18(x * GEN)


def f18(x):
    return f19(x * GEN)


def f19(x):
    return x * GEN


def main():
    v = f0(1)
    p = GEN ** 0
    p[1] = v
    return
