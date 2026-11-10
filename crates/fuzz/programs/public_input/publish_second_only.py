# expect: ok
# public_input: 77, GEN ** 11
# Publishes cell 1 only, through the g-offset form p[GEN].
from snark_lib import *

def main():
    p = GEN ** 0
    p[GEN] = GEN ** 5 * GEN ** 6
    return
