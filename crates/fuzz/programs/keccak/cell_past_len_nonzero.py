# expect: compile-error
# A cell wholly past `len` holding a program value: the doc says it must be a literal zero or the compiler rejects
# it, since the hash would otherwise absorb bytes outside the message.
from snark_lib import *


def main():
    a = GEN ** 5
    out = StackBuf(2)
    keccak([1, 2], [a, 0], out, len=32)
    return
