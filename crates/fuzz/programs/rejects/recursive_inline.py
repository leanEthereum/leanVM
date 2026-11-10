# expect: compile-error recursive @inline expansion is not supported
# Direct recursive inline expansion never terminates: the compiler must reject it.
from snark_lib import *

@inline
def f(x):
    y = f(x * GEN)
    return y

def main():
    r = f(GEN)
    return
