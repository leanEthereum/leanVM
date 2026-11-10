# expect: compile-error unroll(a, b) needs a <= b, got (5, 2)
# unroll(5, 2) has a negative count: it must not wrap to a huge unroll.
from snark_lib import *

def main():
    x = GEN
    for i in unroll(5, 2):
        x = x * GEN
    p = GEN ** 0
    p[1] = x
    return
