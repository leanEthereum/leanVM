# expect: ok
# public_input: 0, 0
# A program that never touches cells 0 and 1: its proof must still bind the statement through the transcript,
# so the corpus check that a changed public input fails verification is the whole point here.
from snark_lib import *

def main():
    return
