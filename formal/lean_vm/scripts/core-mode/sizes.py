"""Per function: core statements and atoms against compiled instructions (core-mode census)."""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import coreir


def count(body):
    a = s = 0
    for st in body:
        s += 1
        if st[0] == 'a':
            a += 1
        elif st[0] == 'ite':
            x, y = count(st[2]), count(st[3]); a += x[0] + y[0]; s += x[1] + y[1]
        elif st[0] == 'match':
            for arm in st[2]:
                x = count(arm); a += x[0]; s += x[1]
    return a, s


def main():
    d = coreir.load()
    rows = []
    for k, (params, body) in d['core'].items():
        a, s = count(body)
        c = d['comp'][k]['count']
        rows.append((k, a, s, c, d['core_text_lines'][k]))
    A = sum(r[1] for r in rows); S = sum(r[2] for r in rows); C = sum(r[3] for r in rows)
    print(f'functions {len(rows)}; core atoms {A}, statements {S}; compiled instructions {C}; ratio instr/stmt {C/S:.2f}')
    print('largest by compiled size: name, core stmts, instructions, ratio')
    for k, a, s, c, l in sorted(rows, key=lambda r: -r[3])[:15]:
        print(f'  {k:45s} {s:7d} {c:7d} {c/max(s,1):5.2f}')
    rs = sorted(c / max(s, 1) for _, _, s, c, _ in rows)
    print('ratio quartiles', [round(rs[int(q * (len(rs) - 1))], 2) for q in (0, .25, .5, .75, 1)])


if __name__ == '__main__':
    main()
