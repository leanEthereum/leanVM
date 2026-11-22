"""Turn 02_ct32 outputs (files with lines "T=.. v1(c1) v2(c2) ...") into per-rate markdown tables for n = 32.

usage: python3 02_tables.py label1=file1 label2=file2 ...
Entry for (rate k/n, agreement T): largest common-top class with degree < k (t = T - k) and with degree <= k
(t = T - k - 1). For T > 16 the class sizes are those of the complements (size 32 - T, same t).
"""
import sys, math
n = 32
tabs = {}
for arg in sys.argv[1:]:
    label, path = arg.split("=")
    tab = {}
    for line in open(path):
        if line.startswith("T="):
            f = line.split()
            T = int(f[0][2:])
            for t, e in enumerate(f[1:], 1):
                tab[(T, t)] = int(e.split("(")[0])
    tabs[label] = tab

def look(tab, T, t):
    if t == 0:
        return math.comb(n, T)
    Tc = T if T <= 16 else n - T
    if t >= Tc:
        return 1
    if t > 8:
        return 1 if tab.get((Tc, 8), 1) == 1 else None
    return tab.get((Tc, t))

for k in (16, 8, 4, 2):
    john = math.sqrt(n * (k - 1))
    print(f"\nRate {k}/{n}, n = 32 (Johnson bound applies for T > {john:.2f}):\n")
    print("| T | T/n | " + " | ".join(f"{l}, deg < k | {l}, deg <= k" for l in tabs) + " |")
    print("| --- | --- | " + " | ".join("--- | ---" for _ in tabs) + " |")
    for T in range(k + 1, n):
        row = []
        for l, tab in tabs.items():
            a, b = look(tab, T, T - k), look(tab, T, T - k - 1)
            row += [str(a) if a is not None else "?", str(b) if b is not None else "?"]
        if all(x == "1" for x in row) and T > john + 2:
            break
        print(f"| {T} | {T/n:.3f} | " + " | ".join(row) + " |")
