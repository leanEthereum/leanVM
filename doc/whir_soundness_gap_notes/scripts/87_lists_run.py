#!/usr/bin/python3
# Referee 87: expand the vote patterns of note 83 into class patterns and rebuild the lists by encoding (87_lists.c).
import subprocess, sys, os
here = os.path.dirname(os.path.abspath(__file__))
def expand(votes):
    toks = []
    for blk in votes.replace("]", "").split("[")[1:]:
        for t in blk.split():
            if t.startswith("*"):
                toks += ["*"] * int(t[1:])
            elif t.startswith("x"):
                toks += [toks[-1]] * (int(t[1:]) - 1)
            else:
                toks.append(t)
    return toks
cases = [
    ("n=32, six members (Section 5)", 4, 6, "[2 *3] [0 13 5 4] [0125 x4] [01345 x4] [0234 x4] [0145 x4] [2345 x4] [123 x4]"),
    ("n=32, seven members (Section 5)", 4, 7, "[135 *3] [2 6 4 0] [023456 x4] [03456 x4] [0123 x4] [12346 x4] [145 x4] [01256 x4]"),
    ("n=64, twelve members, eleven at 40 (votes_c8_b8.txt, seed 5112)", 5, 12, "[7 *7] [6 5 2 08a 4 9 b 1] [0124689b x8] [0134578b x8] [012567a x8] [0234579ab x8] [135689ab x8] [2346789a x8]"),
    ("n=64, eleven members, ten at 40 (votes_c8_b8.txt, seed 5111)", 5, 11, "[7 *7] [0134568a x8] [123789a x8] [01235679 x8] [456789 x8] [0234678a x8] [0 1 a 3 4 26 8 9] [012459a x8]"),
]
for name, V, M, votes in cases:
    toks = expand(votes)
    assert len(toks) == 2 << V, (name, len(toks))
    for seed in (871, 872):
        out = subprocess.run([os.path.join(here, "87_bin", "87_lists"), str(V), str(M), str(seed)] + toks, capture_output=True, text=True).stdout
        print(name, "| seed", seed)
        print("   " + out.strip().replace("\n", "\n   "))
