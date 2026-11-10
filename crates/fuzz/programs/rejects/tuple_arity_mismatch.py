# expect: compile-error `f` returns 2 values, call binds 3
# Binding three names to a two-value return would read a slot nobody writes.
from snark_lib import *

def f(a):
    return a, a * GEN

def main():
    x, y, z = f(GEN)
    p = GEN ** 0
    p[1] = z
    return
