# expect: compile-error N_PLACEHOLDER
# An unfilled placeholder must not become a silent variable.
from snark_lib import *

N = N_PLACEHOLDER

def main():
    sb = StackBuf(N)
    return
