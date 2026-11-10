# expect: ok
# public_input: 0, 0
# witness u: 3, 5, 7, 9
# witness w: 141078893237221139010468596977609488517, 5, GEN ** 3, GEN ** 4
# A random-linear-combination batch check u_i * w_i == t_i whose challenge hashes only the public table, not the
# hints: the prover forges w0 and w1 so their errors cancel under the known r, and the check passes. A protocol flaw
# the corpus pins; batch_check_bound_forgery is the same forgery against a challenge that absorbs the hints.
from snark_lib import *


def main():
    u = StackBuf(4)
    hint_witness(u, "u")
    w = StackBuf(4)
    hint_witness(w, "w")
    d = StackBuf(2)
    keccak([6, 20], [56, 144], d)
    r = d[0]
    t = [6, 20, 56, 144]
    acc = 0
    rp = 1
    for i in unroll(0, 4):
        acc = acc + rp * (u[i] * w[i] + t[i])
        rp = rp * r
    assert acc == 0
    return
