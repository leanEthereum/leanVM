# expect: exec-fail no witness stream `ghost`
# Pops a stream the prover never supplied: the run must fail with a witness fault naming it, not read zeros.
from snark_lib import *


def main():
    v = hint_witness("ghost")
    assert v == 0
    return
