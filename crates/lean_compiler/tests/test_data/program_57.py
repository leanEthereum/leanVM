from snark_lib import *


def main():
    x: Mut = 1
    x = step1(x)
    x = step2(x)
    x = step3(x)
    assert x == 47
    return


def step1(n):
    m: Mut = n
    m = m * 2
    m = m + 1
    return m


def step2(n):
    m: Mut = n
    m = m * 3
    m = m + 2
    return m


def step3(n):
    m: Mut = n
    m = m * 4
    m = m + 3
    return m
