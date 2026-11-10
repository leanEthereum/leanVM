# expect: exec-fail failed range check
# public_input: 99, 0
# witness i: GEN ** 4
# addr_unchecked_index_escape with the range check the doc asks for: the same escaping index must now fail.
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
    assert log(i) < 4
    assert t[i] == v
    return

def main():
    p = GEN ** 0
    is_member(p[1])
    return
