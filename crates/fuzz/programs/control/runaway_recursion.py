# expect: exec-fail step limit
# fuzz: slow
# Recursion with no base case: the run must end with a clean fault (the step limit), never hang or abort the process.
from snark_lib import *


def forever(x):
    y = forever(x * GEN)
    return y


def main():
    z = forever(1)
    return
