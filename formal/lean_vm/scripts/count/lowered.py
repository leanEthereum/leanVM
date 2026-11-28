"""Parse the guest's DBG_LOWER dump into `fns.pkl`: functions, frames, code, allocation hints.

    python3 -I lowered.py LOWER.log fns.pkl

The dump: the guest compiled with `DBG_LOWER=1` and the compiler's debug print (`zkdsl_compiler`'s
`assemble`) printing each instruction's hints too (`{:?} {:?}`, `ins.op, ins.hints`), and
`DBG_PLACEHOLDERS=placeholders.txt` for the constants `shape.py` reads. Run the other scripts from the
directory holding `fns.pkl` and `placeholders.txt`; `grid.py` writes `grid.json`, the tables of
`LeanVM/Guest/Budget/Count.lean`."""
import re, sys, pickle, os
MOD = (1 << 64) | 0b11011
def gpow_table(n):
    t = {}; x = 1
    for e in range(n):
        t.setdefault(x, e)
        x <<= 1
        if x >> 64: x ^= MOD
    return t
FN = re.compile(r'^== fn (\S+) \(frame ([\d,]+)\) ==')
LINE = re.compile(r'^\s+[\d,]+: (.*?) (\[.*\])$')
def parse(path):
    fns = {}; cur = None
    for l in open(path, errors='replace'):
        m = FN.match(l)
        if m:
            name = m.group(1)
            if name in fns: cur = None; continue  # first compile only
            cur = {'name': name, 'frame': int(m.group(2).replace(',', '')), 'code': []}
            fns[name] = cur; continue
        if cur is None: continue
        m = LINE.match(l)
        if m: cur['code'].append((m.group(1), m.group(2)))
    return fns
HINT = re.compile(r'(AllocFrame|AllocArm|AllocBufferDyn|AllocBuffer|AllocLoopFrames) \{ (.*?) \}(?=, Alloc|, Resolved|, NextFrame|\]$)')
def hints(h):
    out = []
    for m in re.finditer(r'AllocLoopFrames \{ ptr: (\d+), callee: "([^"]+)", count: (Constant\((\d+)\)|Bound \{ cell: (\d+), start: (\d+) \}), tail: (\d+) \}', h):
        out.append(('loop', int(m.group(1)), m.group(2), int(m.group(4)) if m.group(4) else None, (int(m.group(5)), int(m.group(6))) if m.group(5) else None, int(m.group(7))))
    for m in re.finditer(r'AllocFrame \{ ptr: (\d+), callee: "([^"]+)" \}', h):
        out.append(('frame', int(m.group(1)), m.group(2)))
    for m in re.finditer(r'AllocArm \{ ptr: (\d+), sel: (\d+), callees: \[([^\]]*)\] \}', h):
        out.append(('arm', int(m.group(1)), int(m.group(2)), re.findall(r'"([^"]+)"', m.group(3))))
    for m in re.finditer(r'AllocBuffer \{ ptr: (\d+), size: (\d+) \}', h):
        out.append(('buf', int(m.group(1)), int(m.group(2))))
    for m in re.finditer(r'AllocBufferDyn \{ ptr: (\d+), size: (\d+) \}', h):
        out.append(('dyn', int(m.group(1)), int(m.group(2))))
    return out
if __name__ == '__main__':
    fns = parse(sys.argv[1])
    for f in fns.values():
        f['hints'] = [(i, hints(h)) for i, (op, h) in enumerate(f['code']) if h != '[]']
        f['keccak'] = any(op.startswith('Keccak') for op, _ in f['code'])
        consts = {}
        for op, _ in f['code']:
            m = re.match(r'Set \{ o: (\d+), k: Const\(E \{ c0: (\d+), c1: (\d+) \}\) \}', op)
            if m: consts.setdefault(int(m.group(1)), []).append((int(m.group(2)), int(m.group(3))))
        f['consts'] = consts
    pickle.dump(fns, open(sys.argv[2], 'wb'))
    print(len(fns), 'functions', sum(len(h) for f in fns.values() for _, h in f['hints']), 'hint sites')
