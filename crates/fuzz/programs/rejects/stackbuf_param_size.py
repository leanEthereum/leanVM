# expect: compile-error is a StackBuf(2), got a StackBuf(3)
# Passing a StackBuf(3) as a StackBuf(2) parameter would hand the callee the wrong run.
from snark_lib import *

def f(s: StackBuf(2)):
    return s[0] + s[1]

def main():
    t = StackBuf(3)
    t[0] = 1
    t[1] = 2
    t[2] = 3
    r = f(t)
    return
