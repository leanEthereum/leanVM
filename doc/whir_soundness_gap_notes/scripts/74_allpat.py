#!/usr/bin/env python3
"""Note 74: print patterns. usage: 74_allpat.py n members all | random count seed minweight"""
import sys, itertools, random
n, members, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
classes = ["."] + ["".join(map(str, c)) for s in range(2, members + 1) for c in itertools.combinations(range(members), s)]
if mode == "all":
    for p in itertools.product(classes, repeat=n):
        print(" ".join(p))
else:
    cnt, seed, minw = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    rnd = random.Random(seed)
    out = 0
    while out < cnt:
        p = [rnd.choice(classes) for _ in range(n)]
        if sum(len(c) - 1 for c in p if c != ".") >= minw:
            print(" ".join(p)); out += 1
