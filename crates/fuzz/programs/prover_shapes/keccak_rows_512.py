# expect: ok
# public_input: 0, 0
# Exactly 512 KECCAK rows, one chain of permutations: around the GKR reduction's block and the table's floor.
from snark_lib import *

def main():
    h = StackBuf(2)
    h[0] = 1
    h[1] = 2
    for i in unroll(0, 512):
        nxt = StackBuf(2)
        keccak(h, h, nxt)
        h = nxt
    assert h[0] != h[1]
    return
