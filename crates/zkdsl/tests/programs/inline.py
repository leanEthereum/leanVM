# `@inline` functions expand at each call site. A returned name, pointer or
# constant binds as a `let` would, with no cell of its own, and a field-constant
# argument stays a constant in the body. A call with a
# destination, a store or a `match` arm, writes it. With x = GEN ** 2 the
# advanced pointer is GEN ** 3 and arm 2 picks 10. Published: (GEN ** 3, 10).
# public_input: GEN ** 3, 10
# witness x: GEN ** 2
from snark_lib import *


@inline
def advance(cur, k):
    return cur * GEN * k


@inline
def word(a, b, j: Const):
    w = a
    if const(j == 2):
        w = b
    return w


def main():
    x = hint_witness("x")
    assert log(x) < 3
    y = advance(x, 1)
    s = StackBuf(1)
    s[0] = word(y, 5, 0)
    r = match(log(x), range(0, 3), lambda j: word(s[0], 10, j))
    p = GEN ** 0
    p[1] = s[0]
    p[GEN] = r
    return
