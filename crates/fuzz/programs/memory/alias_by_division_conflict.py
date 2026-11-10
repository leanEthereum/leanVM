# expect: exec-fail write-once conflict
# public_input: 0, 0
# The conflicting twin of alias_by_division_agree: b already holds 8, so the aliasing store of 9 must fail.
from snark_lib import *

def main():
    a = HeapBuf(4)
    b = HeapBuf(4)
    b[1] = 8
    d = b / a
    a[d] = 9
    return
