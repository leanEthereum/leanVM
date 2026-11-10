# expect: exec-fail write-once conflict
# witness inv: 1234567
# The same advice, pinned with `assert inv * x == 1`: the lie the previous program got away with must now fail.
from snark_lib import *


def main():
    x = GEN ** 3
    inv = hint_witness("inv")
    assert inv * x == 1
    return
