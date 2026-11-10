# expect: compile-error program needs a `main`
# No entry point: the compiler must refuse rather than pick a function or emit an empty program.
from snark_lib import *

def helper(a):
    return a * a
