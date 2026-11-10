# expect: exec-fail not a canonical 128-bit embedding
# public_input: 249476539135558438300489897602002181457, 340233288338733781473457601526632628743
# witness leaf: 42 + 18446744073709551616 * 18446744073709551616, 0
# witness idx: GEN ** 5
# witness path: 41, 0, 30112959954910110987579855913681429795, 229162582536819677791483308909800850886, 211070990735335939509902970862849515302, 276600738596907668386687603208579115584
# The leaf 42 with a third limb added: KECCAK must refuse a word outside the 128-bit embedding rather than hash its low limbs.
from snark_lib import *

# Depth-3 Merkle membership: the statement is the root, the program fixes the leaf value 42, the prover hints the
# leaf, its index and the siblings bottom-up. Order bits come from the index, pinned boolean and recomposed.


@inline
def pick(bit, a, b):
    r = a + bit * (a + b)
    return r


def main():
    leaf = StackBuf(2)
    hint_witness(leaf, "leaf")
    idx = hint_witness("idx")
    assert log(idx) < 8
    bits = StackBuf(3)
    hint_decompose_bits_exponent(bits, idx, 3)
    acc = 1
    for k in unroll(0, 3):
        assert bits[k] * bits[k] == bits[k]
        acc = acc * (1 + bits[k] * (GEN ** (2 ** k) + 1))
    assert acc == idx
    path = StackBuf(6)
    hint_witness(path, "path")
    n0 = leaf[0]
    n1 = leaf[1]
    for k in unroll(0, 3):
        b = bits[k]
        s0 = path[2 * k]
        s1 = path[2 * k + 1]
        nxt = StackBuf(2)
        keccak([pick(b, n0, s0), pick(b, n1, s1)], [pick(b, s0, n0), pick(b, s1, n1)], nxt)
        n0 = nxt[0]
        n1 = nxt[1]
    assert leaf[0] == 42
    assert leaf[1] == 0
    p = GEN ** 0
    p[1] = n0
    p[GEN] = n1
    return
