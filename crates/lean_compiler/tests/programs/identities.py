# Field identities, checked entirely in-program: no `# public_input:`
# annotation, so the harness runs it with the empty public input (two zero
# field elements) and nothing is published.
from snark_lib import *


def main():
    x = GEN * GEN
    assert x == GEN ** 2
    assert log(x) < 3
    y = x + x  # + is XOR: anything plus itself vanishes
    assert y == 0
    return
