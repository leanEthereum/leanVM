# expect: compile-error are compile-time only
# % has no field meaning, so a runtime value position must reject it.
from snark_lib import *

def main():
    h = hint_witness("h")
    y = h % 2
    return
