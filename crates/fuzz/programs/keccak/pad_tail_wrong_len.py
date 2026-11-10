# expect: compile-error
# pad_tail=1 with a len that ends inside a tail cell: the doc says the compiler refuses any len that does not end one
# of the tail's cells.
from snark_lib import *


def main():
    kids = StackBuf(5)
    kids[0] = 1
    kids[1] = 2
    out = StackBuf(2)
    keccak([4, 5], [6, kids[0]], out, tail=kids[1:5], len=81, pad_tail=1)
    return
