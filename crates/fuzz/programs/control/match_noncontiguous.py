# expect: compile-error
# Match arms that skip an integer leave a hole in the dense jump table: the compiler must refuse them.
from snark_lib import *


def main():
    x = GEN
    r = match(log(x), range(0, 2), lambda k: k, range(3, 5), lambda k: k)
    return
