# expect: exec-fail write-once conflict
# public_input: 0, 0
# witness ptr: GEN ** 2
# An adversarial hinted pointer pre-writes a main frame cell that a later local will hold: the later SET must
# conflict rather than the pre-written value silently win.
from snark_lib import *

def main():
    h = hint_witness("ptr")
    h[1] = 42
    a = GEN ** 3
    b = GEN ** 4
    c = GEN ** 5
    out = HeapBuf(1)
    out[1] = a * b * c
    return
