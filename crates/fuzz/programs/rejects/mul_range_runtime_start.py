# expect: compile-error a range bound must be a power of GEN
# A runtime mul_range start is not supported: the frames could not be reserved.
from snark_lib import *

def main():
    s = hint_witness("s")
    for i in mul_range(s, GEN ** 4):
        x = i
    return
