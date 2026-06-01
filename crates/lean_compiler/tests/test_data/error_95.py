from snark_lib import *

# Error: const array used as the target of a function-call assignment.
# `foo()` returns the value already stored (A[0] == 1) so write-once memory would *allow*
# the write — the rejection must come from the const-array rule, not from a value conflict.
A = [1, 2, 3]


def main():
    A[0] = foo()
    return


def foo():
    return 1
