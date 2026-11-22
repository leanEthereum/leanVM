"""Note 83: independent check by encoding of the voted lists printed by 83_votes (and of any pattern). The votes of block q
become the classes of the b leaves of block q of the tree code [N b, N b / 2] (wildcards: all members); the incidence
system of this pattern is solved for a fresh draw of the twiddles, a generic kernel point is encoded, and for every
member the number of leaves where it agrees with the word (the common value of the class of the leaf) is counted.
Usage: 83_verify.py file [min_agreement]   (lines of 83_votes output)"""
import sys, os, random, re, importlib.util
import numpy as np
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("lib83", os.path.join(here, "83_lib.py")); L83 = importlib.util.module_from_spec(spec); spec.loader.exec_module(L83)
def expand(line):
    m = re.search(r"top \[(\d+),(\d+)\] b=(\d+) .* M=(\d+) target=(\d+)", line); N, ku, b, M, target = map(int, m.groups())
    blocks = re.findall(r"\[([^\]]*)\]", line.split("votes:")[1]); assert len(blocks) == N
    cls = []
    for blk in blocks:
        leaves = []
        for tok in blk.split():
            if tok.startswith("*"): leaves += [(1 << M) - 1] * int(tok[1:])
            elif tok == ".": leaves.append(0)
            else: leaves.append(sum(1 << int(ch, 36) for ch in tok))
        assert len(leaves) == b; cls += leaves
    return N * b, M, target, cls
def check(n, t, cls, rnd):
    v = (n // 2).bit_length() - 1; k = n // 2; Lk = (t - 1) * k
    tw = L83.make_tw(v, rnd); G = L83.gen(tw, v)
    ker = L83.kernel(np.array(L83.rows_of(G, k, t, cls)), Lk)
    if len(ker) == 0: return 0, None, None
    pt = L83.random_point(ker, rnd); cw = L83.codewords(G, k, t, pt)
    distinct = len(set(map(tuple, cw.tolist())))
    agree = []
    for l in range(t):
        a = 0
        for x in range(n):
            mem = L83.bits(cls[x])
            if l in mem and all(cw[m][x] == cw[l][x] for m in mem): a += 1
        agree.append(a)
    return len(ker), distinct, agree
if __name__ == "__main__":
    rnd = random.Random(20261121)
    for line in open(sys.argv[1]):
        if "votes:" not in line: continue
        n, t, target, cls = expand(line)
        kd, distinct, agree = check(n, t, cls, rnd)
        ok = kd > 0 and distinct == t and min(agree) >= target
        print(f"n={n} members={t} target={target}: kernel {kd}, distinct codewords {distinct}, agreements {agree} ->", "LIST CONFIRMED" if ok else "not a list at the target")
