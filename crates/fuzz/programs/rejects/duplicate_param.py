# expect: compile-error parameter `x` is declared twice
# Two parameters with one name: the second would shadow the first's cell.
from snark_lib import *

def f(x, x):
    return x

def main():
    r = f(GEN, GEN ** 2)
    p = GEN ** 0
    p[1] = r
    return
