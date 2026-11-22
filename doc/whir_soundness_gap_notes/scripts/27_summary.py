#!/usr/bin/env python3
# Researcher 27. Summarize the class histogram printed by 27_lists.
#   python3 27_summary.py out_k_T.txt [full]
# For every class: J = pair + 2 trip + dbl (the agreement count), excJ = J - 3 delta - 2 (excess over the count for
# independent points), the largest period group among the four triple functions, the cross-ratio and the three
# opposite ratios, the period group of the curve, and R = (excJ + 2) / (largest period).
import re, sys
from collections import defaultdict
rows = []
head = []
for line in open(sys.argv[1]):
    if line.startswith('FLAG'): continue
    m = re.match(r'\s*([\d.]+)\s+(\d+)\s+kap=(\d+) gamD=(\d+) \| delta=(\d+) gam=(\d+) I=(\d+) exc=(-?\d+) flag=(\d+) \| pts pair=(\d+) trip=(\d+) dbl=(\d+) \| PiXi=(\d+) \| triples (.*?) \| Phi \((\d+),(\d+),(\d+)\) \| opp (.*?) \| wdef=(-?\d+) summ=(\d+)\s+\[(.*)\]', line)
    if not m:
        if not line.startswith('    weighted'): head.append(line.rstrip())
        continue
    w = float(m.group(1)); delta = int(m.group(5)); gam = int(m.group(6)); pair, trip, dbl = int(m.group(10)), int(m.group(11)), int(m.group(12))
    pixi = int(m.group(13)); tr = [tuple(map(int, t.split(','))) for t in re.findall(r'\((.*?)\)', m.group(14))]
    phi = (int(m.group(15)), int(m.group(16)), int(m.group(17))); opp = [tuple(map(int, t.split(','))) for t in re.findall(r'\((.*?)\)', m.group(18))]
    J = pair + 2 * trip + dbl; excJ = J - 3 * delta - 2
    mx = max([t[2] for t in tr] + [phi[2]] + [o[1] for o in opp])
    mx7 = max([t[2] for t in tr] + [o[1] for o in opp])
    key = (delta, gam, J, excJ, pair, trip, dbl, pixi, tuple(tr), phi, tuple(opp), int(m.group(19)))
    rows.append((key, w, m.group(21), mx, mx7))
agg = defaultdict(lambda: [0.0, '', 0, 0])
for key, w, ex, mx, mx7 in rows:
    agg[key][0] += w; agg[key][1] = ex; agg[key][2] = mx; agg[key][3] = mx7
print('\n'.join(head))
tot = sum(v[0] for v in agg.values())
print('classes: %d, lists: %.0f' % (len(agg), tot))
worst = 0; worst7 = 0; violQ = 0.0; prim = defaultdict(float)
byexc = defaultdict(float); noper = defaultdict(float)
for key in sorted(agg):
    delta, gam, J, excJ, pair, trip, dbl, pixi, tr, phi, opp, wdef = key
    w, ex, mx, mx7 = agg[key]
    R = (excJ + 2) / mx; worst = max(worst, R); worst7 = max(worst7, (excJ + 2) / mx7)
    if excJ > mx + 3 * pixi - 2: violQ += w
    if pixi == 1: prim[excJ] += w
    byexc[excJ] += w
    if mx == 1: noper[excJ] += w
    if len(sys.argv) > 2:
        print('%11.0f  delta=%d gam=%d J=%d excJ=%d | pair=%d trip=%d dbl=%d | PiXi=%d maxPi=%d R=%.2f | xi %s | Phi %s | opp %s | wdef=%d  [%s]' % (w, delta, gam, J, excJ, pair, trip, dbl, pixi, mx, R, ' '.join('(%d,%d,%d)' % t for t in tr), '(%d,%d,%d)' % phi, ' '.join('(%d,%d)' % o for o in opp), wdef, ex))
print('lists by excJ:', dict(sorted(byexc.items())))
print('lists with no period of any of the eight functions, by excJ:', dict(sorted(noper.items())))
print('lists whose curve has no period, by excJ:', dict(sorted(prim.items())))
print('largest R = (excJ + 2) / max period: %.2f ; with the triple functions and opposite ratios only: %.2f' % (worst, worst7))
print('violations of Conjecture Q (excJ <= max period + 3 |Pi(Xi)| - 2), weighted: %.0f' % violQ)
