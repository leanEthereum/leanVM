from snark_lib import *


# Error: function parameters cannot be declared ': Mut'
def main():
    return


@inline
def double(x: Mut):
    x = x * 2
    return x
