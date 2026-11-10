# expect: ok
# public_input: 0, 0
# Exactly 1024 SET rows and nothing but one JUMP besides: the SET table at a power-of-two edge, four tables empty.
from snark_lib import *

def main():
    sb = StackBuf(1022)
    for i in unroll(0, 1022):
        sb[i] = const(i * 7 + 3)
    return
