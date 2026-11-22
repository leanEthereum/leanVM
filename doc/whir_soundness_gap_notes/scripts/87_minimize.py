#!/usr/bin/python3
# Referee 87: greedy reduction of a three-member counterexample to (C') at (16,32): remove or shrink leaves while the
# saturated pattern still has min over binary Q inside Q* of B above the rank (87_cstar minq, exhaustive).
import subprocess, os, random, sys
here = os.path.dirname(os.path.abspath(__file__))
BIN = os.environ.get("CSTAR_BIN", os.path.join(here, "87_bin", "87_cstar"))
def run(tokens, seed=5):
    out = subprocess.run([BIN, "minq", "1", "4", "3", " ".join(tokens), str(seed)], capture_output=True, text=True).stdout
    sat = [l for l in out.split("\n") if l.strip().startswith("S  =")][0].split("=", 1)[1].split()
    sat = [{"01+02": "012"}.get(t, t) for t in sat]
    fails = "(C') FAILS for the saturated pattern" in out and "(exhaustive): (C') FAILS for the saturated" in out
    line = [l for l in out.split("\n") if l.startswith("saturation")][0]
    return fails, sat, line
start = sys.argv[1].split() if len(sys.argv) > 1 else "012 012 012 012 012 012 012 . 02 02 02 02 01 01 01 01 . . 01 . . . . . 012 . 012 . 12 12 12 012".split()
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
ok, cur, line = run(start)
assert ok, "start is not a counterexample"
changed = True
while changed:
    changed = False
    order = list(range(32)); random.shuffle(order)
    for x in order:
        if cur[x] == ".":
            continue
        options = ["."] + (["01", "02", "12"] if cur[x] == "012" else [])
        for o in options:
            trial = list(cur); trial[x] = o
            ok, sat, l2 = run(trial)
            if ok and sum(len(t) - 1 for t in sat if t != ".") < sum(len(t) - 1 for t in cur if t != "."):
                cur, line, changed = sat, l2, True
                break
print("reduced counterexample:", " ".join(cur))
print(line)
for seed in (11, 12, 13):
    print("seed", seed, run(cur, seed)[2], "fails" if run(cur, seed)[0] else "HOLDS")
