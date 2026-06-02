from snark_lib import *

# Error: a Mut carried across a `parallel_range` loop is rejected, same as `range`.


def main():
    acc: Mut = 0
    for i in parallel_range(0, 4):
        acc = acc + i
    assert acc == 6
    return
