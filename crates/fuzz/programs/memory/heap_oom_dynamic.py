# expect: exec-fail reaches past
# public_input: 0, 0
# witness n: GEN ** 268435455
# A hinted runtime size of 2^28 - 1 cells: the size check must happen before any table or memory grows.
from snark_lib import *

def main():
    n = hint_witness("n")
    a = HeapBuf(n)
    a[1] = 1
    return
