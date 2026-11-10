# expect: ok
# public_input: GEN ** 38, GEN ** 38
# witness s: GEN ** 37
# 64 Const specializations behind one dispatch, fused (plain callee) and expanded (@inline callee), each unrolling
# k real MULs: the selected arm must be exactly the one the range-checked scrutinee names.
from snark_lib import *

def power(x, k: Const):
    acc = x
    for j in unroll(0, k):
        acc = acc * x
    return acc

@inline
def power_inline(x, k: Const):
    acc = x
    for j in unroll(0, k):
        acc = acc * x
    return acc

def main():
    hb = HeapBuf(1)
    hb[1] = GEN
    x = hb[1]
    s = hint_witness("s")
    assert log(s) < 64
    r = match(log(s), range(0, 64), lambda k: power(x, k))
    q = match(log(s), range(0, 64), lambda k: power_inline(x, k))
    p = GEN ** 0
    p[1] = r
    p[GEN] = q
    return
