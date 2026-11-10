# expect: compile-error heap index 4 out of bounds for `buf`
# The bound check must follow a shifted alias: row = buf * GEN ** 3 has one cell left.
from snark_lib import *

def main():
    buf = HeapBuf(4)
    row = buf * GEN ** 3
    row[GEN] = 1
    return
