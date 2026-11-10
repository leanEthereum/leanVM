# expect: compile-error not a heap cell
# A match's targets are frame cells its arms write: a heap cell is not one, and the compiler must say so instead of
# misreading the single target as a multi-value one.
from snark_lib import *


def f(k: Const):
    return k


def main():
    x = GEN
    hb = HeapBuf(2)
    hb[1] = match(log(x), range(0, 2), lambda j: f(j))
    return
