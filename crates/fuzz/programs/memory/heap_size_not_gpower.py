# expect: exec-fail HeapBuf size
# public_input: 0, 0
# witness n: 5
# A runtime HeapBuf size that is no g-power has no cell count: it must be refused, not rounded.
from snark_lib import *

def main():
    n = hint_witness("n")
    a = HeapBuf(n)
    a[1] = 1
    return
