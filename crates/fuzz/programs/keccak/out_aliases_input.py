# expect: exec-fail write-once conflict
# The out run is the input run (`keccak(h, h, h)`) with h already written: the digest overwrites its own message, so
# write-once must make it an assertion that h is a fixed point of the hash, which fails.
from snark_lib import *


def main():
    h = StackBuf(2)
    h[0] = 1
    h[1] = 2
    keccak(h, h, h)
    return
