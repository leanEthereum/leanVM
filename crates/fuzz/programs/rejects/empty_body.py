# expect: compile-error expected an indented block
# A function whose body is empty must be refused, not lowered to fall through into the next function.
from snark_lib import *

def f(x):

def main():
    r = f(GEN)
    return
