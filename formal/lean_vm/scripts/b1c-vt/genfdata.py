# usage: python3 -I genfdata.py  (from this directory, after dump.py)
# Prints the data of VtC/FData.lean for the forms window: `vtAirD` (each table's weight block:
# position, `x`) and `vtFTags` (the window's statements evaluation does not settle, besides the
# reads of `fp_w`: evaluations (0, k), permutations (1, j), weight blocks (3, t)), from vt_ir.txt.
import re, os, textwrap
here = os.path.dirname(os.path.abspath(__file__))
LO, HI, FPW, CUR = 2688, 6352, 13, 2625
ir = {}
for line in open(os.path.join(here, 'vt_ir.txt')):
    k, _, s = line.partition(': ')
    ir[int(k)] = s.strip()
def nums(s): return [int(x) for x in re.findall(r'\.n (\d+)', s)]
def auto(s):
    m = re.match(r'\.atom \(\.(\w+) ', s)
    if not m: return False
    op = m.group(1)
    if op in ('const', 'add', 'copy', 'hint'): return True
    if op == 'mul':
        d, x, y = nums(s)[:3]
        return x < d and y < d
    return False
air = []
for p in range(LO, HI):
    m = re.match(r'\.atom \(\.mul \(\.n 2516\) \(\.n (\d+)\) \(\.n (3[0-5])\)\)$', ir[p])
    if m: air.append((p, int(m.group(1)), int(m.group(2)) - 30))
assert [a[2] for a in air] == list(range(6))
evs = {}  # cursor read position -> k
for p in range(LO, HI):
    m = re.match(r'\.atom \(\.load \(\.n \d+\) \(\.n %d\) (\d+)\)$' % CUR, ir[p])
    if m: evs[p] = int(m.group(1))
tags, p = [], LO
airAt = {a[0]: a[2] for a in air}
while p < HI:
    s = ir[p]
    if p in airAt:
        tags.append((3, airAt[p])); p += 5; continue
    if p in evs:
        tags.append((0, evs[p])); p += 1; continue
    if s.startswith('.atom (.keccak'):
        tags.append((1, sum(1 for t in tags if t[0] == 1))); p += 1; continue
    if auto(s) or re.match(r'\.atom \(\.load \(\.n \d+\) \(\.n %d\) \d+\)$' % FPW, s):
        p += 1; continue
    if s.startswith('.atom (.assertInK') and tags and tags[-1][0] == 0:
        p += 1; continue  # part of the evaluation's rest (vtEvRest)
    raise SystemExit(f'unexpected {p}: {s}')
assert sorted(t[1] for t in tags if t[0] == 0) == list(range(159))
print('vtAirD :=', '[' + ', '.join(f'({a[0]}, {a[1]})' for a in air) + ']')
print('vtFTags :=')
print(textwrap.fill(', '.join(f'({a}, {b})' for a, b in tags), 96, initial_indent='    [', subsequent_indent='    ') + ']')
