# expect: exec-fail write-once conflict
# public_input: 0, 0
# witness n: 1
# A hinted size g^0 is zero cells, so two such buffers share one pointer and the second store contradicts the first:
# runtime sizes are the program's to bound, and write-once is what catches the alias.
from snark_lib import *

def main():
    n = hint_witness("n")
    a = HeapBuf(n)
    b = HeapBuf(n)
    a[1] = 5
    b[1] = 6
    return
