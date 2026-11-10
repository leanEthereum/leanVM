# expect: compile-error
# `-` has no field meaning, so a runtime subtraction must be a compile error and not quietly become XOR.
from snark_lib import *


def main():
    a = GEN ** 3
    b = a - GEN
    p = GEN ** 0
    p[1] = b
    return
