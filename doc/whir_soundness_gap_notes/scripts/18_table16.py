#!/usr/bin/env python3
"""Researcher 18. Collects the n = 16 results of 18_exhaust (and of note 12's 12_multiset16) into markdown tables.

usage: 18_table16.py <dir with the result files>
Files read (all optional): r16/e_rand_1_<k>_<T>.txt, d16/e_rand_2_.., d16/e_real64_.., d16/e_real10_.. (11, 12),
d16/p_rand_<k>_<T>_r<r>.txt and d16/p_real64_.. (phantom-degree profiles), ms_<k>_<T>.txt (12_multiset16 output).
"""
import math
import os
import re
import sys

n = 16
base = sys.argv[1]


def result(path):
    """(max, classes) from a RESULT line, or None."""
    try:
        for line in open(path):
            if line.startswith("RESULT"):
                if "unique decoding" in line:
                    return (1, None)
                m = re.search(r"max=(\d+)", line)
                c = re.search(r"classes=(\d+)", line)
                if m:
                    return (int(m.group(1)), int(c.group(1)) if c else None)
                m = re.search(r"no list of size >= (\d+)", line)
                if m:
                    return (max(1, int(m.group(1)) - 1), None)
    except OSError:
        pass
    return None


def multiset(k, T):
    best = None
    try:
        for line in open(os.path.join(base, "ms_%d_%d.txt" % (k, T))):
            m = re.search(r"largest list (\d+)", line)
            if m:
                best = max(best or 0, int(m.group(1)))
    except OSError:
        pass
    return best


def fmt(x):
    return "" if x is None else str(x[0] if isinstance(x, tuple) else x)


rows = []
for k in range(2, 14):
    for T in range(k + 1, 16):
        e, m, M = n - T, T - k, n - k
        if 2 * e - M - 1 < 0:
            continue  # unique decoding
        johnson = n * (T - k + 1) // (T * T - n * (k - 1)) if T * T > n * (k - 1) else None
        G = (M - 1) // m
        triv = (n - k + 1) // (T - k + 1)
        g1 = result(os.path.join(base, "r16", "e_rand_1_%d_%d.txt" % (k, T)))
        g2 = result(os.path.join(base, "d16", "e_rand_2_%d_%d.txt" % (k, T)))
        rl = result(os.path.join(base, "d16", "e_real64_%d_%d.txt" % (k, T)))
        small = [result(os.path.join(base, "d16", "e_real%d_%d_%d.txt" % (mm, k, T))) for mm in (10, 11, 12)]
        top = result(os.path.join(base, "d16", "p_rand_%d_%d_r0.txt" % (k, T)))
        if top is None:
            try:
                for line in open(os.path.join(base, "tops_rand1.log")):
                    if "k=%d T=%d " % (k, T) in line:
                        mm = re.search(r"max=(\d+)", line)
                        if mm:
                            top = (int(mm.group(1)), None)
                        elif "no list of size >= 1" in line:
                            top = (1, None)
            except OSError:
                pass
        prof = []
        for r in range(0, e):
            p = result(os.path.join(base, "d16", "p_rand_%d_%d_r%d.txt" % (k, T, r)))
            if not p:
                break
            prof.append(fmt(p))
        rprof = []
        for r in range(0, 3):
            p = result(os.path.join(base, "d16", "p_real64_%d_%d_r%d.txt" % (k, T, r)))
            rprof.append(fmt(p) if p else "-")
        rows.append((k, T, johnson, G, triv, top, multiset(k, T), g1, g2, rl, small, prof, rprof))

print("| $k$ | $T$ | $T/n$ | Johnson bound | generic points | trivial | strict tops | multiset tops | all words, generic (seed 1 / seed 2) | classes | all words, real shape $\\mathrm{GF}(2^{64})$ | real shape $\\mathrm{GF}(2^{10}), (2^{11}), (2^{12})$ |")
print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
for (k, T, johnson, G, triv, top, ms, g1, g2, rl, small, prof, rprof) in rows:
    if g1 is None and len(prof) == n - T:  # the profile reached the largest phantom degree: all words
        allw = prof[-1] + " (seed 1, by phantom degree)"
    else:
        allw = "not exhausted" if g1 is None else (fmt(g1) + (" / " + fmt(g2) if g2 else ""))
    print("| %d | %d | %.4f | %s | %d | %d | %s | %s | %s | %s | %s | %s |" % (
        k, T, T / n, "below" if johnson is None else str(johnson), G, triv, fmt(top), fmt(ms), allw,
        "" if g1 is None or g1[1] is None else str(g1[1]), fmt(rl), ", ".join(fmt(x) if x else "-" for x in small) if any(small) else ""))

print()
print("Phantom-degree profiles (largest list among words that are polynomials of degree at most T + r modulo codewords; - = not finished in the time limit):")
print()
print("| $k$ | $T$ | largest phantom degree $e - 1$ | generic, $r = 0, 1, 2, \\dots$ | all words, generic | real shape $\\mathrm{GF}(2^{64})$, $r = 0, 1, 2$ |")
print("| --- | --- | --- | --- | --- | --- |")
for (k, T, johnson, G, triv, top, ms, g1, g2, rl, small, prof, rprof) in rows:
    if len(prof) > 1 or any(x != "-" for x in rprof):
        allw = fmt(g1) if g1 else ("not exhausted" if len(prof) < n - T else prof[-1])
        print("| %d | %d | %d | %s | %s | %s |" % (k, T, n - T - 1, ", ".join(prof), allw, ", ".join(rprof) if any(x != "-" for x in rprof) else ""))
