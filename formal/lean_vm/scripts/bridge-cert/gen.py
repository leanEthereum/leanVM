"""The hint bridge's prefix certificates (`LeanVM/Guest/Bridge/PrefixOk/*.lean`).

A compiled function is in the prefix class (`Bridge.prefixOk`, `LeanVM/Guest/Bridge/Defs.lean`) when
its body's flow hints are all among its leading atoms, the rest of its body has no witness hint, and its
ISA flow hints sit at offsets up to its first jump and compile those leading hints one for one. This
script mirrors that check over the generated data (`data.py`), finds the cells only hints touch (a value
the certificate places at cell `0` or `1`, read off the ISA hint it pairs with), and writes, per pack of
the bundles, each such function's cell map and the kernel's checks that its hint-only cells are fresh
and that it is in the class (`decide +kernel`). `--check` writes nothing and fails when a file is stale.

    python3 -I scripts/bridge-cert/gen.py [--check]
"""
import os, sys, glob, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import data

OUT = os.path.join(data.ROOT, 'Bridge', 'PrefixOk')
FLOW = {'witnessStack', 'witnessHeap', 'log2Ceil', 'bitDecompose', 'bitDecomposeExp', 'windowsExp',
        'digitDecomposeExp', 'fieldLimbs', 'inverse'}


def run_need(vs, b):
    return [(v, b + i) for i, v in enumerate(vs)]


def dest_need(d, bd, pos, n):
    if d[0] == 'stack' and bd[0] == 'stack' and len(d[1]) == n:
        return run_need(d[1], bd[1] + pos)
    if d[0] == 'heap' and bd[0] == 'heap' and d[2] == pos and d[3] == n:
        return [(d[1], bd[1])]
    return None


def need(c, h):
    """The cells `compiles` needs of the core hint `c`'s values for the ISA hint `h`, `(value, cell)`,
    or `None` when no cell map makes `h` compile `c`."""
    k, t = c[0], h[0]
    if k == 'witness' and c[2][0] == 'stack' and t == 'witnessStack':
        return run_need(c[2][1], h[2]) if c[1] == h[1] and len(c[2][1]) == h[3] else None
    if k == 'witness' and c[2][0] == 'heap' and t == 'witnessHeap':
        _, p, off, ln = c[2]
        return [(p, h[2])] if c[1] == h[1] and off == h[3] and ln == h[4] else None
    if k == 'bits' and t == 'bitDecompose':
        _, v, start, nbits, d = c
        if start != 0 or nbits != h[3]:
            return None
        dn = dest_need(d, h[2], 0, nbits)
        return None if dn is None else [(v, h[1])] + dn
    if k == 'bitsExp' and t == 'bitDecomposeExp':
        _, v, nbits, d = c
        if nbits != h[3] or nbits > 62:
            return None
        dn = dest_need(d, h[2], 0, nbits)
        return None if dn is None else [(v, h[1])] + dn
    if k == 'digitsExp' and t == 'digitDecomposeExp':
        _, v, nb, nd, db, st, sc, d = c
        if (nb, nd, db, st) != tuple(h[3:7]) or nb > 62 or (sc is None) != (h[7] is None):
            return None
        dn = dest_need(d, h[2], 0, nd)
        return None if dn is None else [(v, h[1])] + ([] if sc is None else [(sc, h[7])]) + dn
    if k == 'windowsExp' and t == 'windowsExp':
        _, v, st, w, n, d = c
        if (st, w, n) != tuple(h[4:7]):
            return None
        dn = dest_need(d, h[2], h[3], n)
        return None if dn is None else [(v, h[1])] + dn
    if k == 'log2Ceil' and t == 'log2Ceil':
        _, d, nbits, fl, dst = c
        if (nbits, fl) != (h[3], h[4]):
            return None
        dn = dest_need(d, h[1], 0, nbits)
        return None if dn is None else dn + [(dst, h[2])]
    if k == 'inverse' and t == 'inverse':
        return [(c[1], h[1]), (c[2], h[2])]
    if k == 'limbs' and t == 'fieldLimbs':
        return [(c[1], h[1])] + run_need(c[2], h[2]) if len(c[2]) == h[3] else None
    return None


def no_wit(block):
    for s in block:
        if s[0] == 'atom' and s[1] == 'hint' and s[2][0] == 'witness':
            return False
        if s[0] == 'ite' and not (no_wit(s[1]) and no_wit(s[2])):
            return False
        if s[0] == 'match' and not all(no_wit(a) for a in s[1]):
            return False
    return True


def has_flow(block):
    for s in block:
        if s[0] == 'atom' and s[1] == 'hint' and s[2][0] not in ('alloc', 'allocDyn'):
            return True
        if s[0] == 'ite' and (has_flow(s[1]) or has_flow(s[2])):
            return True
        if s[0] == 'match' and any(has_flow(a) for a in s[1]):
            return True
    return False


def prefix(body, B, A):
    """The hint-only cells of a function in the prefix class, `[(value, cell)]`, or `None`."""
    lead = []
    while len(lead) < len(body) and body[len(lead)][0] == 'atom':
        lead.append(body[len(lead)])
    if not no_wit(body[len(lead):]):
        return None
    pcs = [pc for pc, _ in A['hints']]
    if any(a >= b for a, b in zip(pcs, pcs[1:])) or any(pc < A['entry'] for pc in pcs):
        return None
    isa = [(pc - A['entry'], h) for pc, hl in A['hints'] for h in hl if h[0] in FLOW]
    fj = next((n for n, op in enumerate(B['code']) if op == '.jump'), len(B['code']))
    if any(o > fj for o, _ in isa):
        return None
    flow = [s[2] for s in lead if s[1] == 'hint' and s[2][0] not in ('alloc', 'allocDyn')]
    if len(flow) != len(isa):
        return None
    locs = B['locs']
    loc = lambda v: locs[v] if v < len(locs) else 0
    extra = {}
    for c, (_, h) in zip(flow, isa):
        n = need(c, h)
        if n is None:
            return None
        for v, cell in n:
            if loc(v) == cell and v not in extra:
                continue
            if loc(v) < 2 and extra.get(v, cell) == cell and cell >= 2 and cell not in locs and cell not in B['plumb']:
                extra[v] = cell
            else:
                return None
    return sorted(extra.items())


def core_module(key):
    if os.path.isdir(os.path.join(data.ROOT, 'Pack', key)):
        return f'LeanVM.Guest.Pack.«{key}».Core'
    return None


def render(pack, fns):
    imports = ['LeanVM.Guest.Bridge.Defs', 'LeanVM.Guest.Data.AdviceHints', f'LeanVM.Guest.Pack.«{pack}».Bundle']
    imports += sorted({core_module(f['key']) or f'LeanVM.Guest.Pack.«{f["core_pack"]}».Core' for f in fns})
    imports = sorted(set(imports))
    out = [f'/-\n  LeanVM.Guest.Bridge.PrefixOk.«{pack}»\n\n  Generated by `scripts/bridge-cert/gen.py`; do not edit.\n'
           f'  The kernel\'s checks that compiled functions of pack {pack[1:]} are in the hint bridge\'s prefix class.\n-/\n',
           'module\n']
    out.append(''.join(f'public import {m}\n' for m in imports))
    for f in fns:
        k = f['key']
        cells = '[' + ', '.join(f'({v}, {c})' for v, c in f['extra']) + ']'
        out.append(f'''namespace LeanVM.Guest.Fn.«{k}»

open LeanVM.Guest

@[expose] public section

/-- `{k}`: the cells only its hints touch, `(value, cell)`. -/
def bridgeCells : List (ℕ × ℕ) := {cells}

/-- `{k}`: its hints' cell map, its certificate's cells but for `bridgeCells`. -/
noncomputable def bridgeLoc : ℕ → ℕ := Bridge.locOf Fn.«{k}».cert.locs bridgeCells

end

public section

/-- `{k}`: its hint-only cells are fresh. -/
theorem bridgeCellsOk :
    Bridge.cellsFresh Fn.«{k}».cert.locs (Bridge.plumbCells Fn.«{k}».plumb) bridgeCells = true := by
  decide +kernel

/-- `{k}` is in the hint bridge's prefix class. -/
theorem bridgePrefixOk :
    Bridge.prefixOk bridgeLoc Fn.«{k}».core.body Fn.«{k}».code.code Data.adviceFn{f["j"]} = true := by
  decide +kernel

end

end LeanVM.Guest.Fn.«{k}»
''')
    return '\n'.join(out)


def main():
    check = '--check' in sys.argv[1:]
    texts = data.core_texts()
    core_pack = {}
    for p in sorted(glob.glob(data.ROOT + '/Pack/P[0-9]*/Core.lean')):
        for m in re.finditer(r'^namespace LeanVM\.Guest\.Fn\.«([^»]+)»$', open(p, encoding='utf-8').read(), re.M):
            core_pack[m.group(1)] = p.split('/')[-2]
    bundles = data.bundles()
    advice = data.advice()
    packs = {}
    nflow = 0
    for key in sorted(texts):
        B = bundles[key]
        A = advice[B['entry']]
        body = data.body_of(texts[key])
        if not (has_flow(body) or any(h[0] in FLOW for _, hl in A['hints'] for h in hl)):
            continue
        nflow += 1
        extra = prefix(body, B, A)
        if extra is None:
            continue
        packs.setdefault(B['pack'], []).append(dict(key=key, j=A['j'], extra=extra, core_pack=core_pack.get(key)))
    files = {os.path.join(OUT, f'{p}.lean'): render(p, fns) for p, fns in packs.items()}
    stale = []
    existing = set(glob.glob(os.path.join(OUT, '*.lean')))
    for path, text in sorted(files.items()):
        old = open(path, encoding='utf-8').read() if os.path.exists(path) else None
        if old != text:
            stale.append(path)
            if not check:
                os.makedirs(OUT, exist_ok=True)
                open(path, 'w', encoding='utf-8').write(text)
    for path in sorted(existing - set(files)):
        stale.append(path)
        if not check:
            os.remove(path)
    n = sum(len(v) for v in packs.values())
    print(f'bridge-cert: {n} of {nflow} functions with flow hints in the prefix class, '
          f'{sum(1 for v in packs.values() for f in v if f["extra"])} with hint-only cells, {len(files)} modules')
    if check and stale:
        for p in stale:
            print(f'stale: {os.path.relpath(p, data.LEAN_VM)}', file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
