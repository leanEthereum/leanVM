# expect: compile-error len= 80 is past the 64 bytes
# A KECCAK message longer than its cells (len past 64 bytes without tail) must be refused.
from snark_lib import *

def main():
    out = StackBuf(2)
    keccak([1, 2], [3, 4], out, len=80)
    return
