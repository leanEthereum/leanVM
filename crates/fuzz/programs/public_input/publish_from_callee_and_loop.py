# expect: ok
# public_input: GEN ** 20, GEN ** 3
# Publishes cell 0 from a callee frame and cell 1 from inside a loop frame on one iteration only:
# the absolute address g^0 must mean the public input whatever the frame pointer is.
from snark_lib import *

def publish(v):
    p = GEN ** 0
    p[1] = v
    return

def main():
    publish(GEN ** 20)
    for i in mul_range(1, GEN ** 5):
        if i == GEN ** 3:
            p = GEN ** 0
            p[GEN] = i
    return
