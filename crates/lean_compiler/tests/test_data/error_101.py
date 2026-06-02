from snark_lib import *

# Error: the enclosing Mut `c` is reassigned inside an `if` nested in a `range`
# loop — detection must look inside nested blocks, not just the loop's top level.


def main():
    c: Mut = 0
    for i in range(0, 5):
        if i == 2:
            c = c + 1
    assert c == 1
    return
