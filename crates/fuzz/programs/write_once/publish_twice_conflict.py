# expect: exec-fail write-once conflict
# public_input: 5, 0
# Publishes two different words into the first public-input cell: the statement can hold only one, so the second
# store must fail rather than silently keep either.
from snark_lib import *


def main():
    p = GEN ** 0
    p[1] = 5
    q = GEN ** 0
    q[1] = 7
    return
