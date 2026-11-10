# expect: compile-error
# A plain `if 3 + 1 == 4` reads true as integers and false as field elements: the doc says the compiler must reject
# it rather than fold it either way.
from snark_lib import *


def main():
    r = HeapBuf(1)
    if 3 + 1 == 4:
        r[1] = 1
    else:
        r[1] = 2
    return
