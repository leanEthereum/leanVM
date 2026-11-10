# expect: exec-fail write-once conflict
# public_input: 5, 0
# Publishes a word with a nonzero top limb: the statement holds only 128-bit halves, so no public input can match
# and the run on any canonical statement must conflict.
from snark_lib import *


def main():
    w = f192(5, 0, 1)
    p = GEN ** 0
    p[1] = w
    return
