# expect: exec-fail write-once conflict
# A callee stores into a StackBuf parameter that arrives already written: per the doc this is an equality assertion
# against the caller's value, so storing a different value must fail rather than overwrite a private copy.
from snark_lib import *


def pin(s: StackBuf(2)):
    s[0] = 3
    s[1] = 5
    return


def main():
    sb = StackBuf(2)
    sb[0] = 3
    sb[1] = 4
    pin(sb)
    return
