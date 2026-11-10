# expect: compile-error main cannot be `@inline`
# @inline main would expand into nothing: the entry point needs a frame and a halt.
from snark_lib import *

@inline
def main():
    x = GEN
    return
