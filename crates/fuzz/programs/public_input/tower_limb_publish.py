# expect: ok
# public_input: 18446744073709551616, 18446744073709551616 * 5 + 3
# Statement words using their second 64-bit limb (the tower element y): legal 128-bit halves that must round-trip.
from snark_lib import *

def main():
    p = GEN ** 0
    p[1] = 18446744073709551616
    p[GEN] = 3 + 5 * 18446744073709551616
    return
