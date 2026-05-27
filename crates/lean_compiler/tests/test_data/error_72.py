# Error: two imports define the same function name; the collision must be rejected
# rather than silently letting the later import overwrite the earlier one.
from misc.dup_a import *
from misc.dup_b import *


def main():
    x = dup_helper()
    print(x)
    return
