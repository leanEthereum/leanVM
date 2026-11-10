# expect: compile-error index 2 out of bounds (StackBuf size 2)
# A compile-time StackBuf index past its size would address a neighbouring frame cell.
from snark_lib import *

def main():
    a = StackBuf(2)
    b = StackBuf(2)
    a[2] = 5
    return
