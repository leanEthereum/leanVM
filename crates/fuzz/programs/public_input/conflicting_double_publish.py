# expect: exec-fail write-once conflict
# public_input: 5, 0
# Two different values published into one statement word: write-once must refuse the second.
from snark_lib import *

def main():
    p = GEN ** 0
    p[1] = 5
    p[1] = 7
    return
