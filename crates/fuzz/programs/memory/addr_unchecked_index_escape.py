# expect: ok
# public_input: 99, 0
# witness i: GEN ** 4
# The documented addr() hazard, as an attacker uses it: a membership check through a hinted index with no range
# check accepts 99 as a member of [10, 11, 12, 13] by reaching the next frame cell. A program bug, pinned so a layout
# change that moves the escape is noticed; addr_checked_index is the fixed twin.
from snark_lib import *

def is_member(v):
    table = StackBuf(4)
    table[0] = 10
    table[1] = 11
    table[2] = 12
    table[3] = 13
    other = StackBuf(1)
    other[0] = 99
    t = addr(table)
    i = hint_witness("i")
    assert t[i] == v
    return

def main():
    p = GEN ** 0
    is_member(p[1])
    return
