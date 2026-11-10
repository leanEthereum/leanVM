# expect: ok
# public_input: 0, 0
# keccak_cells over a list comprehension of scattered cells must hash exactly what the gathered run hashes,
# with and without a partial len, across the 8.5-cell block boundary.
from snark_lib import *

def main():
    w = StackBuf(40)
    for k in unroll(0, 40):
        w[k] = const(k * 1000 + 1)
    run = StackBuf(20)
    for k in unroll(0, 20):
        run[k] = w[2 * k]
    a = StackBuf(2)
    keccak_cells([w[2 * k] for k in unroll(0, 20)], a)
    b = StackBuf(2)
    keccak_cells(run, b)
    assert a[0] == b[0]
    assert a[1] == b[1]
    c = StackBuf(2)
    keccak_cells([w[2 * k] for k in unroll(0, 20)], c, len=320)
    assert c[0] == a[0]
    d = StackBuf(2)
    keccak_cells(run[0:9], d)
    assert d[0] != a[0]
    return
