# expect: exec-fail wild pointer
# public_input: 0, 0
# Dereferencing the zero word: 0 is no g-power, so it addresses no cell.
from snark_lib import *

def main():
    hb = HeapBuf(1)
    hb[1] = 0
    z = hb[1]
    x = z[1]
    hb[1] = x
    return
