# expect: compile-error expected an expression
# GEN ** -1 is a negative exponent: it must be refused rather than wrap to some huge power.
from snark_lib import *

def main():
    x = GEN ** -1
    return
