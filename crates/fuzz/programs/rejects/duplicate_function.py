# expect: compile-error function `f` is defined twice
# Two functions with one name: which one a call reaches must not be silently chosen.
from snark_lib import *

def f(x):
    return x

def f(x):
    return x * GEN

def main():
    r = f(GEN)
    p = GEN ** 0
    p[1] = r
    return
