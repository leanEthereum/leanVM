#!/usr/bin/env python3
"""Researcher 18. Independent check of the extremal words printed by 18_exhaust, with note 02's list oracle.

02_lists.c counts the codewords at each agreement by interpolating through k-subsets, with no code shared with
18_exhaust. For every result file, the recorded word of every printed class must have exactly `max` codewords at
agreement >= T.

usage: 18_verify16.py <02_lists binary> <result file> [<result file> ...]
"""
import re
import subprocess
import sys

MODLOW = {64: "1b", 10: "9", 11: "5", 12: "53"}
ok = bad = 0
for path in sys.argv[2:]:
    txt = open(path).read()
    m = re.search(r"RESULT k=(\d+) T=(\d+) dom=(\w+) max=(\d+)", txt)
    if not m:
        continue
    k, T, dom, best = int(m.group(1)), int(m.group(2)), m.group(3), int(m.group(4))
    fm = 64 if dom == "rand" else int(dom[4:])
    pm = re.search(r"^PTS(.*)$", txt, re.M)
    if not pm or "WORD" not in txt:
        print("skip (no word printed):", path)
        continue
    pts = pm.group(1)
    # the recorded word of each class is the first WORD line after "recorded word"
    words = []
    for block in txt.split("  class ")[1:]:
        rec = block.split("recorded word")[1]
        words.append(re.search(r"WORD(.*)", rec).group(1))
    if not words:
        continue
    inp = pts + "\n" + "\n".join(words) + "\n"
    out = subprocess.run([sys.argv[1], "profile", str(fm), MODLOW[fm], "16", str(k), str(T)], input=inp, capture_output=True, text=True).stdout
    sizes = [sum(int(x.split(":")[1]) for x in line.split()) for line in out.splitlines()]
    good = all(s == best for s in sizes) and len(sizes) == len(words)
    ok += good
    bad += not good
    print("%s k=%d T=%d %s: max %d, oracle on %d class words: %s %s" % ("ok " if good else "BAD", k, T, dom, best, len(words), sorted(set(sizes)), path if not good else ""))
print("files agreeing: %d, disagreeing: %d" % (ok, bad))
