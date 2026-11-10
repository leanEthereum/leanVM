# expect: ok
# The honest twin of stackbuf_param_pins_caller: the callee's stores into its StackBuf parameter agree with the
# caller's cells, so they are no-op equalities and the run proves.
# public_input: 5, 0
from snark_lib import *


def pin(s: StackBuf(2)):
    s[0] = 3
    s[1] = 3 + 5
    return s[0] + s[1]


def main():
    sb = StackBuf(2)
    sb[0] = 3
    sb[1] = 6
    v = pin(sb)
    p = GEN ** 0
    p[1] = v + 3 + 3
    return
