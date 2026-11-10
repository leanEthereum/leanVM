# expect: compile-error `f` takes 2 arguments, got 1
# A call with too few arguments would read the callee's parameter cell unwritten.
from snark_lib import *

def f(a, b):
    return a * b

def main():
    r = f(GEN)
    return
