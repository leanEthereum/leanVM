# expect: exec-fail write-once conflict
# public_input: 0, 0
# The caller tries to change a cell of a returned callee frame: write-once must refuse, or a callee's checked result
# could be swapped after the check.
from snark_lib import *

def make():
    s = StackBuf(2)
    s[0] = 1
    s[1] = 2
    return addr(s)

def main():
    q = make()
    q[GEN] = 3
    return
