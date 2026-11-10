# expect: ok
# A zero-cell StackBuf: its address would alias the next run.
from snark_lib import *

def main():
    s = StackBuf(0)
    t = StackBuf(1)
    t[0] = 1
    return
