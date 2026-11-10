# expect: ok
# public_input: 10, 0
# The legal twin of use_before_store: loaded before the store, used only after it, so the load sees the value.
from snark_lib import *

def main():
    hb = HeapBuf(1)
    x = hb[1]
    hb[1] = 5
    p = GEN ** 0
    p[1] = x * GEN
    return
