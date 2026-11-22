"""Note 76: orbits of the lists printed by 76_n16 (lines 'LIST m (est e): hex masks of error supports') under the
automorphisms of the two trees on 16 leaves (order 2^15). Usage: 76_orbits.py size file..."""
import sys, numpy as np
def auts(lo, size):
    """all automorphisms of the complete binary tree on leaves lo..lo+size-1, as dicts leaf -> leaf"""
    if size == 1: return [{lo: lo}]
    h = size // 2; A = auts(lo, h); B = auts(lo + h, h); out = []
    for a in A:
        for b in B:
            d = dict(a); d.update(b); out.append(d)
            d2 = {x: y + h for x, y in a.items()}; d2.update({x: y - h for x, y in b.items()}); out.append(d2)
    return out
G = auts(0, 16)
perm = np.array([[g[x] for x in range(16)] for g in G], dtype=np.int64)          # (32768, 16)
tab = np.zeros((len(G), 2, 256), dtype=np.int64)
for byte in range(2):
    for val in range(256):
        acc = np.zeros(len(G), dtype=np.int64)
        for bit in range(8):
            if (val >> bit) & 1: acc |= (1 << perm[:, 8 * byte + bit])
        tab[:, byte, val] = acc
def canon(masks):
    m = np.array(masks, dtype=np.int64)
    img = tab[:, 0, m & 255] | tab[:, 1, m >> 8]                                   # (32768, len)
    img.sort(axis=1)
    key = np.zeros(len(G), dtype=object)
    best = min(map(tuple, img.tolist()))
    return best
def show(masks):
    cls = []
    for x in range(16):
        c = "".join(str(i) for i, m in enumerate(masks) if not (m >> x) & 1)
        cls.append(c if c else ".")
    return " | ".join(" ".join(cls[4 * q:4 * q + 4]) for q in range(4))
if __name__ == "__main__":
    size = int(sys.argv[1]); seen = {}; total = 0
    for fn in sys.argv[2:]:
        for line in open(fn):
            if not line.startswith("LIST %d " % size): continue
            masks = [int(h, 16) for h in line.split(":")[1].split()]
            total += 1; c = canon(masks); seen[c] = seen.get(c, 0) + 1
    print("lists of size", size, "read:", total, "orbits:", len(seen))
    for c, cnt in sorted(seen.items(), key=lambda kv: -kv[1]):
        sizes = sorted(16 - bin(m).count("1") for m in c)
        cover = sum(1 for x in range(16) if any(not (m >> x) & 1 for m in c))
        print(f"  found {cnt:5d} times; agreements {sizes}; leaves with a class {cover}; classes per leaf: {show(c)}")
