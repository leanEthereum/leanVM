from snark_lib import *

# Error: `unroll` loop with an enormous bound (would expand unboundedly).
def main():
    for i in unroll(0, 100000000000):
        x = i
    return
