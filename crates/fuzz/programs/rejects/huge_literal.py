# expect: compile-error 340282366920938463463374607431768211456
# An integer literal past 128 bits must be refused rather than truncated to its low bits.
from snark_lib import *

def main():
    x = 340282366920938463463374607431768211456
    p = GEN ** 0
    p[1] = x
    return
