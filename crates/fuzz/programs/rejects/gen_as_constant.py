# expect: compile-error `GEN` is a builtin
# Redefining GEN would replace the generator everywhere it appears.
from snark_lib import *

GEN = 5

def main():
    return
