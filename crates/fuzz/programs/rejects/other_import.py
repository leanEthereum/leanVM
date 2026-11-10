# expect: compile-error file imports are not supported
# Only snark_lib may be imported: anything else would be silently ignored.
from snark_lib import *

import os

def main():
    return
