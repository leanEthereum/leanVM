# expect: prove-fail
# public_input: 1 + 18446744073709551616 * 2 + 18446744073709551616 * 18446744073709551616 * 3, 0
# Publishes a word with a nonzero third limb, which the statement (two 128-bit halves) cannot carry:
# the run succeeds, so prove must refuse the statement with an error (verify rejects it as malformed), not panic or emit a proof.
from snark_lib import *

def main():
    p = GEN ** 0
    p[1] = f192(1, 2, 3)
    return
