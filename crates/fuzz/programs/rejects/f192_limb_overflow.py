# expect: compile-error f192 needs three literal u64 limbs
# An f192 limb past 64 bits must be refused.
from snark_lib import *

def main():
    x = f192(18446744073709551616, 0, 0)
    return
