# expect: exec-fail cannot back-solve MUL through a zero operand
# witness d: 0
# Divides by a hinted zero: the prover cannot pick a quotient q with q * 0 = 5, so the run must fail.
from snark_lib import *


def main():
    d = hint_witness("d")
    q = 5 / d
    p = GEN ** 0
    p[1] = q
    return
