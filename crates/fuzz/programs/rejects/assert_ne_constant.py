# expect: compile-error compile-time-equal literal 5
# assert 5 != 5 is false at compile time, so a program containing it can never be proven.
from snark_lib import *

def main():
    assert 5 != 5
    return
