# expect: compile-error this keccak operand spans exactly 2 cells
# A KECCAK operand of three cells cannot be a 2-cell input.
from snark_lib import *

def main():
    s = StackBuf(3)
    s[0] = 1
    s[1] = 2
    s[2] = 3
    out = StackBuf(2)
    keccak(s[0:3], s[0:2], out)
    return
