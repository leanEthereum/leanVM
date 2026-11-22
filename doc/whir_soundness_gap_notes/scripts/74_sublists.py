#!/usr/bin/env python3
"""Note 74, task 2: for each pattern on stdin (after ' | '), print its restrictions to every subset of `size` members
(classes intersected with the subset, relabelled 0.., classes of size < 2 dropped), one per line, in a fixed order.
usage: 74_sublists.py members size < patterns"""
import sys, itertools
members, size = int(sys.argv[1]), int(sys.argv[2])
subs = list(itertools.combinations(range(members), size))
for line in sys.stdin:
    pat = line.split("|")[-1].split()
    for T in subs:
        out = []
        for c in pat:
            keep = [str(T.index(int(ch))) for ch in c if ch != "." and int(ch) in T]
            out.append("".join(keep) if len(keep) >= 2 else ".")
        print(" ".join(out))
