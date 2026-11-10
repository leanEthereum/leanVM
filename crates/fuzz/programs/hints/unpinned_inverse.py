# expect: ok
# public_input: 1234567, GEN ** 3
# witness inv: 1234567
# An adversarial program that takes an "inverse" as advice and forgets to check it: the prover publishes any value it
# likes. It proves, which is the documented contract (hints are unconstrained); the corpus keeps it as the shape to avoid.
from snark_lib import *


def main():
    x = GEN ** 3
    inv = hint_witness("inv")
    p = GEN ** 0
    p[1] = inv
    p[GEN] = x
    return
