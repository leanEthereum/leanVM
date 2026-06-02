from snark_lib import *

# Error: assignment into a const array (compile-time-immutable data).
# Writes the value already stored (A[0] == 1) so write-once memory would *allow* it —
# the rejection must come from the const-array rule, not from a value conflict.
A = [1, 2, 3]


def main():
    A[0] = 1
    return
