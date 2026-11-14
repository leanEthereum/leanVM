# expect: exec-fail not a g-power below 2^28
# witness n: GEN ** 536870912
# witness x: GEN ** 3
# A runtime bound past every addressable cell (2^28) with the required precheck omitted: the claim log x < log n
# is true, but the complement g^(k-1-e) lies past every address, so the gadget cannot be satisfied. The precheck is
# what keeps an honest claim provable; the run must refuse, never accept by wrapping.
from snark_lib import *


def main():
    n = hint_witness("n")
    x = hint_witness("x")
    assert log(x) < log(n)
    return
