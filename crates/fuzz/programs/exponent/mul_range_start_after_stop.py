# expect: compile-error must not exceed stop
# A compile-time mul_range whose start is past its stop: the walk never reaches the bound. The compiler must
# reject it rather than emit a loop that only the step limit ends.
from snark_lib import *


def main():
    out = HeapBuf(1)
    for i in mul_range(GEN ** 5, GEN ** 3):
        out[1] = 1
    return
