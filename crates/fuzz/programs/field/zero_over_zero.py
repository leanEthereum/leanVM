# expect: exec-fail cannot back-solve MUL through a zero operand
# witness d: 0
# 0 / 0: every quotient satisfies q * 0 = 0, so an accepted run would let the prover pick any value. The run must
# refuse rather than leave the quotient as a free, prover-chosen word.
from snark_lib import *


def main():
    d = hint_witness("d")
    q = d / d
    p = GEN ** 0
    p[1] = q
    return
