# expect: ok
# public_input: 5, GEN
# Locals named len and keccak (not functions): plain bindings, which must not reach the builtins.
from snark_lib import *

def main():
    len = 5
    keccak = GEN
    p = GEN ** 0
    p[1] = len
    p[GEN] = keccak
    return
