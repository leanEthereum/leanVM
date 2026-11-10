# expect: ok
# Rebinds a list literal through its own old cells (`s = [s[1], s[0]]`) three times: the elements must be lowered
# before the name rebinds, or the swap reads the half-written new run.
# public_input: 7, 9
from snark_lib import *


def main():
    s = [7, 9]
    s = [s[1], s[0]]
    s = [s[1], s[0]]
    s = [s[1], s[0]]
    s = [s[1], s[0]]
    p = GEN ** 0
    p[1] = s[0]
    p[GEN] = s[1]
    return
