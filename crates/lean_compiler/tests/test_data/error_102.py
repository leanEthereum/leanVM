from snark_lib import *

# Error: `counter` (enclosing Mut) is reassigned inside a nested `range` loop.


def main():
    counter: Mut = 0
    for i in range(0, 3):
        for j in range(0, 2):
            counter = counter + 1
    assert counter == 6
    return
