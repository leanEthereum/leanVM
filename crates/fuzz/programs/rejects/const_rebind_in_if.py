# expect: compile-error cannot be rebound inside an `if`
# Rebinding a Const parameter inside an if may outlive the block, so substitution cannot tell: rejected.
from snark_lib import *

def f(k: Const):
    if const(k == 1):
        k = 5
    return k

def main():
    r = f(1)
    return
