# expect: ok
# public_input: 0, 0
# witness tail: 5
# witness tail: 5 + 18446744073709551616 * 7
# zkDSL.md's caveat, pinned: with len=72 the last cell holds 8 message bytes, and the circuit does not force its
# other bytes to zero. Two hinted cells that spell the same 72-byte message hash differently, so a program that
# takes such a digest as the hash of its message must range-check that cell itself.
from snark_lib import *


def main():
    x = hint_witness("tail")
    y = hint_witness("tail")
    a = StackBuf(2)
    keccak_cells([1, 2, 3, 4, x], a, len=72)
    b = StackBuf(2)
    keccak_cells([1, 2, 3, 4, y], b, len=72)
    assert a[0] != b[0]
    return
