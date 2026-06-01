from snark_lib import *

# Error: `total` (a Mut from the enclosing scope) is reassigned inside a `range`
# loop. Loop-carried mutables are not supported; use an explicit buffer instead.


def main():
    total: Mut = 0
    for i in range(0, 5):
        total = total + i
    assert total == 10
    return
