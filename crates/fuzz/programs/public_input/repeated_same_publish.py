# expect: ok
# public_input: 5, 5
# The same value published three times, from two pointers: a second identical write is a no-op.
from snark_lib import *

def main():
    p = GEN ** 0
    p[1] = 5
    p[1] = 5
    q = GEN * GEN ** 0
    q[1] = 5
    p[GEN] = p[1]
    return
