# expect: compile-error Write `if const(...)`
# 3 + 1 is 4 as integers and 2 in the field: an if on it is ambiguous and must be rejected.
from snark_lib import *

def main():
    if 3 + 1 == 4:
        x = 1
    return
