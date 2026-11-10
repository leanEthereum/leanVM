# expect: exec-fail cannot back-solve MUL through a zero operand
# Divides by a constant zero: the quotient's back-solve has no solution, so the run must fail with the documented
# fault rather than produce an unconstrained quotient.
from snark_lib import *


def main():
    z = 0
    q = 5 / z
    p = GEN ** 0
    p[1] = q
    return
