import shape, json
out = {}
for slow in ("none", "all"):
    for m in range(16, 31):
        for r in (1, 2, 3, 4):
            S = dict(c=32, w=24, n=24, p=19, tau=24, m=m, r=r, slow=slow)
            k = "%s %d %d" % (slow, m, r)
            out[k] = {"words": shape.vs(dict(S)), "rows": shape.vs_cyc(dict(S))}
            print(k, out[k], flush=True)
json.dump(out, open("grid.json", "w"))
print("GRID-DONE")
