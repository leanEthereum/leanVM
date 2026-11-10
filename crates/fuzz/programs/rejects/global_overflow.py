# expect: compile-error global constant `BIG`
# Integer arithmetic in a global constant must not wrap modulo 2^128.
from snark_lib import *

BIG = 340282366920938463463374607431768211455 * 2

def main():
    x = BIG
    return
