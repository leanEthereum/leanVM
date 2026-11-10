# expect: compile-error
# `assert 5 != 5` is false at compile time and must be rejected while compiling.
from snark_lib import *


def main():
    assert 5 != 5
    return
