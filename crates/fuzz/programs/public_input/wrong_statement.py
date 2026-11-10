# expect: exec-fail write-once conflict
# public_input: 6, 0
# The program publishes 5 but the statement says 6: the run must fail on the publishing store.
from snark_lib import *

def main():
    p = GEN ** 0
    v = HeapBuf(1)
    v[1] = 5
    p[1] = v[1] * 1
    return
