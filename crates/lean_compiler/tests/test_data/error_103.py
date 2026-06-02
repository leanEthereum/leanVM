from snark_lib import *

# Error: `ARR` is used as an array base but never defined (no constant, no
# assignment). The compiler must reject this cleanly, not panic in codegen
# ("Variable ARR not in scope" at get_offset).


def main():
    a = ARR[0]
    assert a == 10
    return
