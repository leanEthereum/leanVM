# expect: compile-error expected a range starting at 0, got 1
# Arms must start at 0: a table starting at 1 would make log(x) = 0 jump to a stale slot.
from snark_lib import *

def main():
    x = GEN
    r = match(log(x), range(1, 4), lambda j: j)
    return
