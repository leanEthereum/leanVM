# expect: compile-error is a builtin
# A user function named like a builtin would be dead code that still looked live: refused.
from snark_lib import *

def assert_gpow(x):
    assert x == 5
    return

def main():
    assert_gpow(GEN)
    return
