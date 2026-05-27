from snark_lib import *


def main():
    result = increment_twice(5)
    assert result == 7
    return


def increment_twice(x):
    y: Mut = x
    y = y + 1
    y = y + 1
    return y
