# expect: compile-error expected a range starting at 2, got 3
# A gap in the arms would leave a jump-table slot pointing anywhere.
from snark_lib import *

def main():
    x = GEN
    r = match(log(x), range(0, 2), lambda j: j, range(3, 5), lambda j: j)
    return
