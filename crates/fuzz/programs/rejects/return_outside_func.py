# expect: compile-error top level: expected `def`
# A top-level return or statement outside any def.
from snark_lib import *

return 5

def main():
    return
