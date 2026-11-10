# expect: exec-fail write-once conflict
# Writes absolute memory cells 2 and 3 through the g^0 pointer, which are main's own frame cells: a program can
# reach any cell this way, and the store into a cell the program already gave another value must conflict.
from snark_lib import *


def main():
    a = GEN ** 5
    p = GEN ** 0
    p[GEN ** 2] = 77
    p[GEN ** 3] = 78
    return
