# expect: compile-error a `<` assert compares logs
# Field elements have no order: a bare < must not be read as some range check.
from snark_lib import *

def main():
    x = GEN ** 3
    assert x < GEN ** 5
    return
