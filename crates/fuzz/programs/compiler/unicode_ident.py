# expect: ok
# public_input: GEN, 0
# A non-ASCII identifier: a char boundary slice would panic in a byte-indexed lexer.
from snark_lib import *

def main():
    é = GEN
    p = GEN ** 0
    p[1] = é
    return
