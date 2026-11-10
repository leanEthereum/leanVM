# expect: compile-error exceeds 2^16
# A range-check bound above 2^16 is unsound at the minimum memory size.
from snark_lib import *

def main():
    x = GEN ** 5
    assert log(x) < 65537
    return
