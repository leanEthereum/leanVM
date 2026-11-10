# expect: ok
# public_input: 12, 0
# witness i: GEN ** 2
# The honest membership proof through a range-checked addr() index: completeness of the checked twin.
from snark_lib import *

def is_member(v):
    table = StackBuf(4)
    table[0] = 10
    table[1] = 11
    table[2] = 12
    table[3] = 13
    t = addr(table)
    i = hint_witness("i")
    assert log(i) < 4
    assert t[i] == v
    return

def main():
    p = GEN ** 0
    is_member(p[1])
    return
