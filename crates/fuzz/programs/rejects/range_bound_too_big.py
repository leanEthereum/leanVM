# expect: compile-error exceeds 2^30
# A range-check bound above the largest memory size can name no cell.
from snark_lib import *

def main():
    x = GEN ** 5
    assert log(x) < 1073741825
    return
