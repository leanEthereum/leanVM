# expect: ok
# public_input: GEN ** 9, 12345
# A nonzero statement the program never reads: nothing in the trace pins it, only the Fiat-Shamir seed and the
# memory boundary, so a proof for it must not verify for any other statement.
from snark_lib import *

def main():
    x = GEN ** 3
    assert x * x == GEN ** 6
    return
