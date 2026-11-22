#!/usr/bin/env python3
"""Note 74, task 2: join the verdicts of the four-member orbits with those of their four three-member sub-lists.
usage: 74_sublists_join.py parents.txt sublists_classified.txt"""
import sys, collections
par = [l for l in open(sys.argv[1])]
sub = [l for l in open(sys.argv[2]) if not l.startswith('#')]
assert len(sub) == 4 * len(par)
stat = collections.Counter(); ex = {}
for i, p in enumerate(par):
    f = p.split(); kind = f[0]; dT = int(f[1][3:]); dU = int(f[2][3:])
    res = []
    for s in sub[4 * i:4 * i + 4]:
        g = s.split(); res.append((int(g[1][3:]) - int(g[2][3:]), g[0]))
    allsp = all(v == 'SPANNED' for d, v in res if d > 0)
    key = (kind, 'deficiency=%d' % (dT - dU), 'dU=%d' % dU, 'sub-list deficiencies', tuple(sorted(d for d, _ in res)), 'deficient sub-lists spanned by lifts' if allsp else 'NOT all spanned')
    stat[key] += 1; ex.setdefault(key, p.split('|')[1].strip())
for k, c in sorted(stat.items(), key=lambda kv: -kv[1]): print(c, k, 'e.g.', ex[k])
