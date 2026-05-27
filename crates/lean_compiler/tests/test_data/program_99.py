from snark_lib import *


def main():
    result = accumulate(5)
    assert result == 8
    return


def accumulate(x):
    acc: Mut = x
    for i in unroll(0, 3):
        acc = acc + i
    return acc
