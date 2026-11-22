#!/usr/bin/env python3
"""Note 78: note 69's 69_lift.py with the number of common zeros as a parameter (default 2^lo - 1; V2 up/dn keep 2^(lo-1) - 1).
Lift a pattern of a top code to the tree code with `lo` more bottom layers: every block class is repeated on the
2^lo leaves of the block, and 2^lo - 1 leaves (the zeros of the common lower factor B) get the full class.
The zeros are placed greedily to maximize the balanced agreement, then the weight.
usage: 78_lift.py members lo [nzeros] < file with lines '... best: <pattern>' or '<pattern>'   (prints one lifted pattern per line)"""
import sys

def balanced(cls, members):
    cnt = [0] * members
    free = 0
    for c in cls:
        if not c:
            free += 1
        for m in c:
            cnt[m] += 1
    for _ in range(free):
        cnt[cnt.index(min(cnt))] += 1
    return min(cnt)

def weight(cls):
    return sum(len(c) - 1 for c in cls if c)

def main():
    members, lo = int(sys.argv[1]), int(sys.argv[2])
    nz = int(sys.argv[3]) if len(sys.argv) > 3 else (1 << lo) - 1
    full = frozenset(range(members))
    for line in sys.stdin:
        if "kind=" in line or not line.strip():
            continue
        pat = line.split("best:")[-1].split("|")[-1].split()
        top = [frozenset() if c == "." else frozenset(int(ch) for ch in c) for c in pat]
        bs = 1 << lo
        cls = [c for c in top for _ in range(bs)]
        used = [0] * len(top)
        for _ in range(nz):
            best = None
            for b in range(len(top)):
                if used[b] == bs or top[b] == full:
                    continue
                trial = list(cls)
                trial[b * bs + used[b]] = full
                key = (balanced(trial, members), weight(trial), -used[b])
                if best is None or key > best[0]:
                    best = (key, b)
            b = best[1]
            cls[b * bs + used[b]] = full
            used[b] += 1
        sys.stderr.write(f"lifted: n={len(cls)} members={members} weight={weight(cls)} balanced={balanced(cls, members)}\n")
        print(" ".join("".join(map(str, sorted(c))) if c else "." for c in cls))

main()
