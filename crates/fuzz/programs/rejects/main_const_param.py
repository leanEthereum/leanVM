# expect: compile-error main cannot take Const parameters
# main with a Const parameter has no call site to specialize it from.
from snark_lib import *

def main(k: Const):
    x = GEN ** k
    return
