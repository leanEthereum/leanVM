# A miniature WOTS-style chain walk bundling the DSL's moving parts: a
# runtime digit is range-checked (dispatch soundness), then match
# dispatches it to a Const-specialized walker whose hash chain is unrolled
# over heap slices (a 256-bit SHA3 digest occupies two canonical cells);
# the walker also builds g^{2n} at runtime (unrolled MULs) to read its final
# pair back through g-power indexing. The recomputation at the end lands on an
# already-written StackBuf pair, so write-once turns the hash into a digest
# assertion; the dead `if` branch holds an impossible assert that must never
# execute. Published: the two 128-bit digest cells of H^2(5, 7).
# public_input: 208822183413446500621413149391147122921, 118328345503752981047975230716482008923
from snark_lib import *


def main():
    buf = HeapBuf(16)
    buf[1] = 5
    buf[GEN] = 7
    d = GEN ** 2  # the runtime digit
    assert log(d) < 4  # bound the scrutinee before dispatching on it
    t0, t1 = match(log(d), range(0, 4), lambda i: walk(buf, i))
    if d != GEN ** 2:
        assert 1 == 0  # dead branch: never executes
    v = StackBuf(2)
    v[0] = t0
    v[1] = t1
    sha3(buf[2:4], buf[2:4], v)  # recompute H(value1, value1): asserts v[0:2] == (t0, t1)
    p = GEN ** 0
    p[1] = t0
    p[GEN] = t1
    return


def walk(buf, n: Const):
    p = 1
    for i in unroll(0, n):
        sha3(buf[i * 2:i * 2 + 2], buf[i * 2:i * 2 + 2], buf[i * 2 + 2:i * 2 + 4])
        p = p * GEN * GEN
    return buf[p], buf[p * GEN]
