# expect: exec-fail loop bound is not a g-power
# public_input: 5, 0
# The statement is used as a loop bound without its range check, and 5 is no g-power: the walk can never reach it,
# so the run must fail rather than loop forever.
from snark_lib import *

def main():
    p = GEN ** 0
    n = p[1]
    for i in mul_range(1, n):
        x = i * GEN
    return
