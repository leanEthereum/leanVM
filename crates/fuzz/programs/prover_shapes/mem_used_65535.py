# expect: ok
# public_input: 0, 0
# A HeapBuf whose last cell makes exactly 65535 memory cells used: memory at the 2^16 floor (MIN_LOG_MEM) edge.
from snark_lib import *

def main():
    hb = HeapBuf(65529)
    hb[GEN ** 65528] = 1
    return
