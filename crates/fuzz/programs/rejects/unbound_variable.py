# expect: compile-error unbound variable `never_bound`
# An unbound name must not silently read some cell: it would be a prover-chosen value.
from snark_lib import *

def main():
    p = GEN ** 0
    p[1] = never_bound + 1
    return
