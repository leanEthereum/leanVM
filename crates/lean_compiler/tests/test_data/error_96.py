from snark_lib import *

# Error: `match_range` over an empty range produces a match with no cases.
def main():
    p = 0
    r = match_range(p[0], range(0, 0), lambda i: i)
    return
