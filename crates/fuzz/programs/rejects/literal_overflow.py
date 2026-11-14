# expect: compile-error unbound variable
# A literal at or past 2^128 parses as an identifier and is refused unbound: no machine word spells it.
from snark_lib import *

def main():
    x = 340282366920938463463374607431768211456
    return
