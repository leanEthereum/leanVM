# usage: python3 -I genevals.py  — rewrites the data of Tables/Vt/EvalsT.lean (verify_tables' 153
# table evaluations, G:2644-2655: `fs_next` at the cursor, copied into `col_evals`; the
# permutations between them) from vt_ir.txt (dump.py).
import os, sys, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from symev import IR, VT_LEAN

CUR = 2647
N_EV, N_PERM = 153, 38
def main():
    ev = []; perm = []
    for p in sorted(IR):
        s = IR[p]
        m = re.match(r'\.atom \(\.load \(\.n (\d+)\) \(\.n %d\) (\d+)\)' % CUR, s)
        if m and int(m.group(2)) == len(ev) and p > 2684:
            b = int(m.group(1)); ev.append((p, b))
            assert IR[p + 3].startswith(f'.atom (.copy (.n {b + 3}) (.n {b}))'), (p, IR[p + 3])
        m = re.match(r'\.atom \(\.keccak \[\.n (\d+).*\] \[\.n (\d+),', s)
        if m and ev and len(perm) < N_PERM and p > ev[-1][0] and len(ev) == 4 * (len(perm) + 1):
            perm.append((p, int(m.group(2))))
    assert len(ev) == N_EV and len(perm) == N_PERM, (len(ev), len(perm))
    return ev, perm

def fmt(items, per):
    lines = []; cur = '  ['
    for i, x in enumerate(items):
        piece = x + (', ' if i + 1 < len(items) else ']')
        if len(cur) + len(piece) > 98: lines.append(cur.rstrip()); cur = '    '
        cur += piece
    lines.append(cur)
    return '\n'.join(lines)

if __name__ == '__main__':
    ev, perm = main()
    f = os.path.join(VT_LEAN, 'EvalsT.lean'); s = open(f).read()
    a = s.index('def vtEvalData'); b = s.index('\n\n', a)
    s = s[:a] + 'def vtEvalData : List (ℕ × ℕ) :=\n' + fmt([f'({p}, {b})' for p, b in ev], 6) + s[b:]
    a = s.index('def vtPermData'); b = s.index('\n\n', a)
    s = s[:a] + 'def vtPermData : List (ℕ × ℕ) :=\n' + fmt([f'({p}, {o})' for p, o in perm], 6) + s[b:]
    open(f, 'w').write(s)
    print(ev[:3], perm[:3])
