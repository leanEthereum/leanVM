# expect: compile-error a < b
# A match with an empty range has no arms: the table would be empty and every scrutinee wild.
from snark_lib import *

def main():
    x = GEN
    r = match(log(x), range(0, 0), lambda j: j)
    return
