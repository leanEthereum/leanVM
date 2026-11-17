# Deep nesting across frames: a mul_range loop whose helper body range-checks the
# counter, dispatches on it, calls a recursive function from one arm (five frames
# deep, with its base-case `return` inside an `if` branch), and carries a runtime
# branch in the SAME frame as the dispatch, so self_fp and the hoisted caches are
# shared between the two. The branch is TAKEN, so the published values come from
# its fall-through path and a lowering that ignored the condition would show up
# here; `conditionals.py` covers the other polarity.
# geom(1) = 1 + g + g² + g³ + g⁴ = 31. Published: (31 + 5, 9) = (26, 9).
# public_input: 26, 9
from snark_lib import *

TAIL = [0, 5, 9]


def main():
    acc = HeapBuf(6)
    for i in mul_range(1, GEN ** 3):
        assert log(i) < 3
        v = match(log(i), range(0, 1), lambda j: geom(1), range(1, 3), lambda j: TAIL[j])
        # TAKEN on every iteration, so the published values ride the fall-through
        # path: an `if` whose condition is never true rides the jump instead and
        # stops detecting a lowering that ignores the condition.
        if i == i * GEN ** 0:
            acc[i] = v
        else:
            acc[i] = 0
    p = GEN ** 0
    p[1] = acc[1] + acc[GEN]
    p[GEN] = acc[GEN ** 2]
    return


def geom(x):
    if x == GEN ** 4:
        return x  # early return from inside the branch
    y = geom(x * GEN)
    return x + y
