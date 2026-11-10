# expect: compile-error is a comparison, not a statement
# A statement without effect is almost always a forgotten assignment or assert.
from snark_lib import *

def main():
    x = GEN
    x == GEN
    return
