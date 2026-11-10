# expect: exec-fail not a K-valued word
# public_input: 18446744073709551616, 3
# The program demands both statement words lie in GF(2^64): a statement using the second limb must fail it.
from snark_lib import *

def main():
    p = GEN ** 0
    assert_in_k(p[1], p[GEN])
    return
