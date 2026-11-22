"""Note 64, item 5a: merge the per-mu lines of several runs of 64_item5_exhaustive and compare with the exact expectation.
Usage: python3 64_item5_merge.py out1.txt out2.txt ...   (the expectation column is read from the first file's table)"""
import re, sys, statistics as st
rows, exp, bound = [], {}, {}
for f in sys.argv[1:]:
    for l in open(f):
        if l.startswith("mu "):
            rows.append(l)
        elif re.match(r"^\d+ \|", l):
            c = [x.strip() for x in l.split("|")]
            exp[int(c[0])], bound[int(c[0])] = float(c[2]), float(c[4])
mx = [int(re.search(r"max (\d+)", l).group(1)) for l in rows]
print(f"{len(rows)} samples of mu; distribution of the maximum of u_2+2u_3 over all triples: " + ", ".join(f"{m}: {mx.count(m)}" for m in sorted(set(mx))))
print("C | mean count | std error | exact expectation | fraction of mu with max >= C | first-moment bound")
for C in range(8, 18):
    v = []
    for l in rows:
        m = re.search(r" %d:(\d+)" % C, l)
        v.append(int(m.group(1)) if m else 0)
    print(f"{C} | {st.mean(v):.4g} | {st.stdev(v)/len(v)**.5:.3g} | {exp[C]:.4g} | {sum(1 for m in mx if m >= C)/len(mx):.3f} | {bound[C]:.3g}")
