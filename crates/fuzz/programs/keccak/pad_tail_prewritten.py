# expect: exec-fail write-once conflict
# pad_tail=1 with the tail cells the compiler sets already written by the program: the padding store must collide
# with the program's value rather than hash the program's word as if it were padding.
from snark_lib import *


def main():
    kids = StackBuf(5)
    kids[0] = 1
    kids[1] = 2
    kids[2] = 3
    out = StackBuf(2)
    keccak([4, 5], [6, kids[0]], out, tail=kids[1:5], len=80, pad_tail=1)
    return
