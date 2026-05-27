from snark_lib import *


def main():
    x = func()
    return


def func():
    a: Imm
    if 0 == 0:
        a = aux()
    return a


@inline
def aux():
    return 1
