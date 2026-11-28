"""Attribute a DBG_MEM dump's allocations to the closure of a root function (by the lowered call graph)."""
import sys, pickle, re
import words2 as w
def closure(root):
    seen = set(); st = [root]
    while st:
        f = st.pop()
        if f in seen: continue
        seen.add(f)
        for i, hs in w.fns[f]['hints']:
            for h in hs:
                if h[0] in ('frame', 'loop'): st.append(h[2])
                elif h[0] == 'arm': st.extend(h[3])
    return seen
def load(path):
    ranges = []; pcs = {}; head = []
    for l in open(path):
        if l.startswith('#'): head.append(l.strip()); continue
        if l.startswith('F '):
            _, n, e, ln = l.split(); ranges.append((n, int(e), int(ln))); continue
        pc, steps, mem = map(int, l.split()); pcs[pc] = (steps, mem)
    return head, ranges, pcs
def per_fn(path):
    head, ranges, pcs = load(path)
    out = {}
    for n, e, ln in ranges:
        s = sum(pcs.get(pc, (0, 0))[0] for pc in range(e, e + ln))
        m = sum(pcs.get(pc, (0, 0))[1] for pc in range(e, e + ln))
        calls = pcs.get(e, (0, 0))[0]
        if s or m: out[n] = (calls, s, m)
    return head, out
if __name__ == '__main__':
    head, pf = per_fn(sys.argv[1])
    root = sys.argv[2] if len(sys.argv) > 2 else 'verify_sub'
    cl = closure(root)
    print(head)
    tm = sum(v[2] for n, v in pf.items() if n in cl); ts = sum(v[1] for n, v in pf.items() if n in cl)
    print(root, 'closure mem', tm, 'steps', ts, 'calls', pf.get(root))
    for n, v in sorted(pf.items(), key=lambda x: -x[1][2])[:int(sys.argv[3]) if len(sys.argv) > 3 else 15]:
        print(' ', n, v, 'in' if n in cl else 'OUT')
