# expect: exec-fail write-once conflict
# The out run is the input run with h never written: the hash reads cells only its own output writes. Either the read
# froze h at zero, so the hash's write must conflict; a proof of a self-referential digest would be a bug.
from snark_lib import *


def main():
    h = StackBuf(2)
    keccak(h, h, h)
    return
