# expect: ok
# public_input: 103317623244284004116543927255586714017, 46742100452828831147838302652756821896
# pad_tail=1: an 80-byte message whose last two cells sit in a 5-cell StackBuf with only two written; the compiler
# sets the rest to the padding. Must equal keccak_cells of the same five words, and the independent digest.
from snark_lib import *


def main():
    kids = StackBuf(5)
    kids[0] = 69322883731209150433532654067435404913
    kids[1] = 6604172965078421236305709412977954369
    pp = 261482337992134289948088258508929830401
    a0 = 197429186571722343884394214761379389137
    at = 133376035151310397839219255251752955553
    out = StackBuf(2)
    keccak([pp, a0], [at, kids[0]], out, tail=kids[1:5], len=80, pad_tail=1)
    ref = StackBuf(2)
    keccak_cells([pp, a0, at, kids[0], kids[1]], ref)
    assert out[0] == ref[0]
    assert out[1] == ref[1]
    p = GEN ** 0
    p[1] = out[0]
    p[GEN] = out[1]
    return
