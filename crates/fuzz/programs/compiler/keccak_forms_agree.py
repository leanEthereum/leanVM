# expect: ok
# public_input: 0, 0
# Every keccak form must hash the same bytes the same way: keccak against keccak_cells at 64 and 48 bytes, the
# pad_tail form against a plain 80-byte keccak_cells, and a 19-cell hash split as a block pair plus a continued state.
# A padding or block-parity miscompile in any one form breaks an equality here.
from snark_lib import *


def main():
    w = StackBuf(19)
    for k in unroll(0, 19):
        w[k] = const(k * 4099 + 17)
    a = StackBuf(2)
    keccak(w[0:2], w[2:4], a)
    b = StackBuf(2)
    keccak_cells(w[0:4], b)
    assert a[0] == b[0]
    assert a[1] == b[1]
    c = StackBuf(2)
    keccak(w[0:2], [w[2], 0], c, len=48)
    d = StackBuf(2)
    keccak_cells(w[0:3], d, len=48)
    assert c[0] == d[0]
    assert c[1] == d[1]
    kids = StackBuf(5)
    kids[0] = w[4]
    f = StackBuf(2)
    keccak(w[0:2], w[2:4], f, tail=kids[0:4], len=80, pad_tail=1)
    g = StackBuf(2)
    keccak_cells(w[0:5], g)
    assert f[0] == g[0]
    assert f[1] == g[1]
    st = StackBuf(13)
    keccak_cells(w[0:17], st, final=0)
    h = StackBuf(2)
    keccak_cells([w[17], w[18]], h, state=st)
    i = StackBuf(2)
    keccak_cells(w, i)
    assert h[0] == i[0]
    assert h[1] == i[1]
    return
