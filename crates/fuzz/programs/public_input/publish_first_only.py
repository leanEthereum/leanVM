# expect: ok
# public_input: GEN ** 7, 99
# Publishes cell 0 only: cell 1 is a free statement word the program never constrains, which must still be bound.
from snark_lib import *

def main():
    p = GEN ** 0
    p[1] = GEN ** 3 * GEN ** 4
    return
