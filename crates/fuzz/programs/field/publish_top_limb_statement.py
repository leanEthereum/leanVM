# expect: ok
# public_input: 5 + 18446744073709551616 * 18446744073709551616, 0
# The statement itself carries a third limb, and the program publishes exactly that word: the run agrees, but the
# verifier accepts only 128-bit halves, so no proof of this statement may verify.
from snark_lib import *


def main():
    w = f192(5, 0, 1)
    p = GEN ** 0
    p[1] = w
    return
