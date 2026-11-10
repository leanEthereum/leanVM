# expect: ok
# public_input: GEN ** 13, 21
# witness ptr: 1
# Publishes through pointers that reach cell 0 only at runtime (a division and a hinted pointer), not the literal GEN ** 0.
from snark_lib import *

def main():
    q = HeapBuf(2)
    one = q / q
    one[1] = GEN ** 13
    h = hint_witness("ptr")
    h[GEN] = 21
    return
