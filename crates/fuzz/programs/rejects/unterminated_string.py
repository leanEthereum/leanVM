# expect: compile-error cannot parse expression
# An unterminated string literal in a hint name: the parser must not slice past the end.
from snark_lib import *

def main():
    h = hint_witness("oops)
    return
