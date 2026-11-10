# expect: compile-error `main` is the entry point
# main is the entry point: calling it would halt the machine early with a success.
from snark_lib import *

def f():
    main()
    return

def main():
    f()
    return
