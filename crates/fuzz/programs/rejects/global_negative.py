# expect: compile-error `3 - 5` overflows
# A global constant that goes negative must be an error, not a field value.
from snark_lib import *

NEG = 3 - 5

def main():
    sb = StackBuf(4)
    sb[0] = NEG
    return
