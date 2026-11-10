# expect: compile-error may not reuse one
# A global constant name reused as a parameter is reserved and must be refused.
from snark_lib import *

K = 3

def f(K):
    return K

def main():
    r = f(GEN)
    return
