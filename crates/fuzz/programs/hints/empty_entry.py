# expect: exec-fail holds 0 values, the destination 1
# witness e:
# An empty entry popped by the one-value form: the value must not default to zero.
from snark_lib import *


def main():
    v = hint_witness("e")
    assert v == 0
    return
