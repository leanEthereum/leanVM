# expect: ok
# public_input: 43, 32
# Two consecutive matches in one frame whose @inline arms each bind a local: arms of one match share their locals,
# but a second match must not reuse the first's cells, or its different value conflicts with the first's.
from snark_lib import *


@inline
def arm(v, k: Const):
    t = v * GEN ** k
    u = t + k
    return u


def main():
    x = GEN ** 2
    y = GEN ** 3
    a = match(log(x), range(0, 4), lambda k: arm(5, k))
    b = match(log(y), range(0, 4), lambda k: arm(5, k))
    p = GEN ** 0
    p[1] = b + 0
    p[GEN] = a + b + 29
    return
