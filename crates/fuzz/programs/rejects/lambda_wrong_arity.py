# expect: compile-error match needs `range(a, b), lambda i: …` pairs
# A match lambda of two parameters has no meaning.
from snark_lib import *

def main():
    x = GEN
    r = match(log(x), range(0, 2), lambda a, b: a)
    return
