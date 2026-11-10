# expect: compile-error `7 // 0` overflows a u128, goes negative or divides by zero
# Division by zero in a global constant.
from snark_lib import *

Z = 0
Q = 7 // Z

def main():
    x = Q
    return
