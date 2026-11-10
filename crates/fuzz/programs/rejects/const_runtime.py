# expect: compile-error asks for a compile-time integer
# const(...) of a runtime value must say so rather than fall back to a runtime computation.
from snark_lib import *

def main():
    h = hint_witness("h")
    x = const(h + 1)
    return
