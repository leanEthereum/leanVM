# expect: ok
# A compile-time mul_range whose start equals its stop must compile to nothing: an impossible assert in its body
# never runs. A loop that ran once would fail.
from snark_lib import *


def main():
    for i in mul_range(GEN ** 3, GEN ** 3):
        assert 1 == 0
    for j in mul_range(1, 1):
        assert 1 == 0
    return
