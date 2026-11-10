# expect: compile-error only the whole right-hand side of an assignment
# A match whose results nothing binds: its arms write their results into the targets of an assignment, so a bare
# statement has nowhere to put them, and the compiler must say what to write instead.
from snark_lib import *


def f(k: Const):
    return k


def main():
    x = GEN
    match(log(x), range(0, 2), lambda j: f(j))
    return
