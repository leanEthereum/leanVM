# expect: exec-fail wild pointer
# public_input: 12345, 0
# The statement is dereferenced as a pointer: a word that is no small g-power must fault, not read some cell.
from snark_lib import *

def main():
    p = GEN ** 0
    q = p[1]
    x = q[1]
    p[GEN] = x
    return
