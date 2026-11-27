"""Print the functions not yet total, grouped by parallel track, each with its callees not yet total.

Run from formal/rv64mc after `python3 campaign/scripts/callgraph.py . campaign/cg.json`:

    python3 campaign/scripts/plan.py notes/total-status.md

A function is READY when every callee is total; work READY functions first, in the order listed.
"""
import json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
cg = json.load(open(os.path.join(HERE, '..', 'cg.json')))
bymod = {f['mod']: f for f in cg}
byi = {f['idx']: f for f in cg}
status = sys.argv[1] if len(sys.argv) > 1 else 'notes/total-status.md'

total = set()
for line in open(status):
    c = line.split('|')
    if len(c) > 8 and c[2].strip().isdigit() and 'yes' in c[6]:
        total.add(int(c[2]))

# 225 is compiler_builtins' memmove entry, proved through Table/MemT6a.memmoveWrapT.
callees = {i: [bymod[c]['idx'] for c in byi[i]['callees'] if bymod[c]['idx'] != 225] for i in byi}

# Tracks, in the order each should be worked (callees before callers). See campaign/PARALLEL.md.
TRACKS = [
    ('T1 layout', [203, 207, 211, 209, 195, 189, 191, 188, 190, 187, 175, 45]),
    ('T2 transcript, WHIR, opening', [107, 85, 99, 88, 89, 74, 66]),
    ('T3 bus', [137, 146, 23, 161, 171, 130, 64, 54, 152, 48]),
    ('T4 multilinear, Keccak', [90, 59, 172, 32, 138, 139, 60]),
    ('T5 bytecode', [216, 218, 217, 215]),
    ('T6 top (sequential, last)', [42, 214, 7]),
]

listed = [i for _, fs in TRACKS for i in fs]
rem = {f['idx'] for f in cg if f['idx'] not in total}
missing = sorted(rem - set(listed))
left = sum(byi[i]['n'] for i in rem)
print(f'not total: {len(rem)} functions, {left} instructions')
for name, fs in TRACKS:
    todo = [i for i in fs if i in rem]
    print(f'\n{name}: {len(todo)} left, {sum(byi[i]["n"] for i in todo)} instructions')
    for i in todo:
        f = byi[i]
        wait = [c for c in callees[i] if c in rem]
        state = 'READY' if not wait else 'waits on ' + ', '.join(map(str, wait))
        print(f'  {i:4} h{f["h"]:<2} n={f["n"]:4} loops={f["loops"]}  {state:28} {f["key"][:90]}')
if missing:
    print('\nnot in any track (add them):', missing)
