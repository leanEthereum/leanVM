# expect: exec-fail not a small g-power
# The skipped-branch twin with x = g^8: if the bound cell were the branch's unwritten one, the check after the join
# could be back-solved to accept anything. It must still reject.
from snark_lib import *


def f(x, c):
    if c == 1:
        assert log(x) < 8
    assert log(x) < 8
    return x


def main():
    a = f(GEN ** 8, 0)
    return
