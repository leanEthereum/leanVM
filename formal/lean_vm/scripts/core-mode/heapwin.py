"""The kernel's heap check of a long loop helper in windows (`CoreMode/HeapCWin.lean`): `heapOkC` over the whole body
of `main_loop2` (35 `match`es of 256 arms) runs past the build's memory cap in one `decide`.

The certificate is `emitc.py`'s (`GenC/<pack>/Data.lean`, its `hcert`; `emitc.KERNEL_SKIP` lists the functions it
leaves to this script). The body without the tail is cut between top-level statements, each window at most `--atoms`
atoms (counting the arms'); `heapc.py`'s pass (the check in Python, step for step) gives the state at each cut, written
as a literal (`mkCSt`, the tries by their entries). Per function, in `GenCW/<fn>/` (not under `GenC/`, whose files
`emitc.py` owns):

* `St.lean`: `sigW` (the callees' signatures, as `emitc.py` writes them) and the states `st0` .. `stN`;
* `W<i>.lean`: `win<i> : winOk Data.powTree sigW core hcert (((loopBody core).drop a).take (b - a)) st<i> st<i+1> =
  true` (one `decide +kernel`: no `ret`, no ghost value, the pass from one state to the next);
* `Ok.lean`: `head_ok`, `tail_ok` and `Fn.«fn».heap_okC : heapOkC Data.powTree sigOf core hcert = true` (the
  statement `emitc.py` writes for the other functions), by `heapOkC_of_wins`.

usage (from formal/lean_vm, `CORE_MODE_CACHE` set): python3 -I scripts/core-mode/heapwin.py [--fn NAME,..]
  [--atoms N] [--out DIR] [--check] [--mods FILE]
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
argv = list(sys.argv)
sys.argv = sys.argv[:1]
import infer as I
import heapc as C
import emitc as E

GUEST = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
FNS = ['main_loop2']
# atoms per window: the kernel's memory grows with the atoms a window's pass and ghost check go through; the default
# keeps a window of `main_loop2` within the 7.5 GB a module may take (measured: `m2-heap.md`)
ATOMS = 15000
DEPTH = 20                      # `Exec.indexDepth`: keys past it are dropped by `setF`
KEYMAX = 2 ** DEPTH - 1


def atoms(s):
    """Atoms of a statement, the arms' included."""
    k = s[0]
    if k == 'a':
        return 1
    if k == 'ite':
        return 1 + sum(map(atoms, s[2])) + sum(map(atoms, s[3]))
    if k == 'match':
        return 1 + sum(atoms(t) for arm in s[2] for t in arm)
    return 1


def states(k, H, sigOf):
    """The check's pass over a loop helper (`heapc.heapOkC`), the state after each top-level statement of its body
    without the tail: `[S0, S1, ..]`, `S_i` before statement `i`."""
    params, body = I.CORE[k]
    G = H.sig
    m = len(params)
    X_ = C.X(dict(I.POWS), H, sigOf, params)
    P = C.Pass(X_, sigOf, body)
    assert list(params) == list(range(m)), 'params'
    assert len(G.term) == 1 and G.term[0][0] == ('val', 0), ('not a loop helper', G.term)
    assert not (G.retM or G.postV or G.retEq), 'loop with retM/postV/retEq'
    assert body[-1] == ('ret', []) and body[-2][0] == 'callIf', 'loop shape'
    assert all(v < C.GB for v in C.values(params, body)), 'noGhost'
    st = C.St()
    for i in range(m):
        st.env[i] = C.baseC(i)
    ms = C.monos(st.env, params) + [C.baseC(C.GB + j) for j in range(G.ghosts)]
    pps, rs, prs = C.instPP(ms, G.preP), C.instAllR(ms, G.preR), C.instPRL(ms, G.prePR)
    assert None not in (pps, rs, prs), 'init-inst'
    for p in pps:
        st.pushP(p)
    for r in rs:
        st.pushR(r)
    for p in prs:
        st.pushPR(p)
    out = [st.copy()]
    for s in body[:-2]:
        st = P.block([s], st)
        out.append(st.copy())
    _, c, g, args = body[-2]
    P.callIf(st, c, g, args)
    P.tail(st, args, G.term[0][1])
    return out


def cuts(body, budget):
    """Cut points `0 = a0 < a1 < .. < aN = len(body)`, each window at most `budget` atoms (or one statement)."""
    out, acc = [0], 0
    for i, s in enumerate(body):
        n = atoms(s)
        if acc and acc + n > budget:
            out.append(i)
            acc = 0
        acc += n
    out.append(len(body))
    return out


# ---- Lean text

def lcell(c):
    return E.lcell(c)


def lprun(r):
    return f'⟨{lcell(r[0])}, {r[1]}, {lcell(r[2])}, {lcell(r[3])}⟩'


def lnums(l):
    return '[' + ', '.join(map(str, l)) + ']'


def lentries(d, val):
    """A trie's entries, keys increasing (keys past `Exec.indexDepth` dropped, as `setF` drops them)."""
    items = [f'({k}, {val(v)})' for k, v in sorted(d.items()) if k < KEYMAX]
    return '[' + ',\n      '.join(items) + ']'


def lstate(st):
    cd = ', '.join(f'⟨{lcell(mx)}, {j}, [{", ".join(map(lcell, cs))}], [{", ".join(map(lprun, rs))}], '
                   f'[{", ".join(f"({lcell(p[0])}, {lnums(p[1])})" for p in ps)}], '
                   f'[{", ".join(f"({lprun(p[0])}, {lnums(p[1])})" for p in prs)}]⟩'
                   for mx, j, cs, rs, ps, prs in st.cd)
    eqs = ', '.join(f'({lcell(a)}, {lcell(b)})' for a, b in st.eqs)
    pair = lambda p: f'({lcell(p[0])}, {lcell(p[1])})'
    return (f'mkCSt\n    {lentries(st.env, lcell)}\n    {lentries(st.sc, lcell)}\n    {lentries(st.rs, lprun)}\n'
            f'    {lentries(st.ad, pair)}\n    {lentries(st.sv, pair)}\n    {lentries(st.src, lcell)}\n'
            f'    {lentries(st.pf, lambda p: f"({lcell(p[0])}, {lnums(p[1])})")}\n'
            f'    {lentries(st.pr, lambda p: f"({lprun(p[0])}, {lnums(p[1])})")}\n'
            f'    {st.n} {st.nr} {st.nc} {st.nt} [{cd}] [{eqs}]')


HEADER = '''/-
  LeanVM.Guest.CoreMode.GenCW.«{fn}».{mod}

  Generated by `scripts/core-mode/heapwin.py`; do not edit.
  {what}
-/

module

'''


def sig_lam(k, names):
    arms = ''.join(f'\n    | "{n}" => Fn.«{I.callee(n)}».hcert.sig' for n in sorted(names) if I.callee(n) in I.CORE)
    return f'(fun g ↦ match g with{arms}\n    | _ => .empty)' if arms else '(fun _ ↦ .empty)'


def emit(k, H, sts, cs, names, po):
    """The modules of one function: `[(name, text)]`."""
    pack, core_mod = po[k][0], po[k][1]
    cal = sorted({I.callee(n) for n in names} & set(I.CORE))
    data = sorted({f'LeanVM.Guest.CoreMode.GenC.«{po[c][0]}».Data' for c in cal + [k]})
    ns = f'LeanVM.Guest.Fn.«{k}»'
    base = f'LeanVM.Guest.CoreMode.GenCW.«{k}»'
    mods = []
    st = HEADER.format(fn=k, mod='St', what=f'The callees\' signatures and the states at the {len(cs)} cut points of '
                       f'`{k}`\'s windowed heap check.')
    st += 'public import LeanVM.Guest.CoreMode.HeapCWin\n' + ''.join(f'public import {m}\n' for m in data)
    st += f'\nset_option maxRecDepth 100000\nset_option linter.all false\n\nnamespace {ns}.HeapW\n\n'
    st += 'open LeanVM.Guest.CoreMode\n\n@[expose] public section\n\n'
    st += f'/-- The callees\' signatures. -/\nnoncomputable def sigW : String → CoreMode.HSig := {sig_lam(k, names)}\n'
    for i, a in enumerate(cs):
        st += f'\n/-- The state before statement {a}. -/\nnoncomputable def st{i} : CSt := {lstate(sts[a])}\n'
    st += f'\nend\nend {ns}.HeapW\n'
    mods.append(('St', st))
    imps = (f'public import {base}.St\npublic import LeanVM.Guest.Data.Pows\n'
            f'public import LeanVM.Guest.Pack.«{pack}».{core_mod}\n')
    for i in range(len(cs) - 1):
        a, b = cs[i], cs[i + 1]
        w = HEADER.format(fn=k, mod=f'W{i}', what=f'Window {i} of `{k}`\'s heap check: statements {a} to {b - 1}.')
        w += imps + f'\nset_option Elab.async false\n\nnamespace {ns}.HeapW\n\nopen LeanVM.Guest.CoreMode\n\n'
        w += (f'@[expose] public section\n\n/-- Statements {a} to {b - 1}. -/\ntheorem win{i} : winOk Data.powTree sigW '
              f'core hcert (((Memory.loopBody core).drop {a}).take ({b} - {a})) st{i} st{i + 1} = true := by\n'
              f'  decide +kernel\n\nend\nend {ns}.HeapW\n')
        mods.append((f'W{i}', w))
    n = len(cs) - 1
    ei = H.sig.term[0][1]
    lei = E.lidx(ei)
    ok = HEADER.format(fn=k, mod='Ok', what=f'`{k}`\'s heap check, from its {n} windows.')
    ok += ''.join(f'public import {base}.W{i}\n' for i in range(n))
    ok += f'\nset_option Elab.async false\n\nnamespace {ns}.HeapW\n\nopen LeanVM.Guest.CoreMode\n\n@[expose] public section\n\n'
    ok += (f'/-- The parameters, the tail\'s shape, the entry state. -/\ntheorem head_ok : headOk Data.powTree sigW core '
           f'hcert {lei} {cs[-1]} st0 = true := by\n  decide +kernel\n\n')
    ok += (f'/-- The tail call and the guarantees at `ret []`. -/\ntheorem tail_ok : tailOkW Data.powTree sigW core hcert '
           f'{lei} st{n} = true := by\n  decide +kernel\n\n')
    ok += f'end\nend {ns}.HeapW\n\nnamespace {ns}\n\n@[expose] public section\n\n'
    lst = ', '.join(f'({cs[i]}, HeapW.st{i})' for i in range(1, n + 1))
    wins = ''.join(f'HeapW.win{i}, by omega,\n    ' for i in range(n))
    ok += (f'/-- `{k}`: the heap check, in {n} windows. -/\ntheorem heap_okC : CoreMode.heapOkC Data.powTree\n'
           f'    {sig_lam(k, names)}\n    core hcert = true :=\n'
           f'  CoreMode.heapOkC_of_wins (l := [{lst}]) HeapW.head_ok\n    ⟨{wins}trivial⟩ rfl HeapW.tail_ok\n')
    ok += f'\nend\nend {ns}\n'
    mods.append(('Ok', ok))
    return mods


def main():
    fns = argv[argv.index('--fn') + 1].split(',') if '--fn' in argv else FNS
    budget = int(argv[argv.index('--atoms') + 1]) if '--atoms' in argv else ATOMS
    out = argv[argv.index('--out') + 1] if '--out' in argv else os.path.join(GUEST, 'CoreMode', 'GenCW')
    I.F.difference_update(E.OFF)
    I.set_features(argv)
    res, dt = I.run_all()
    print(f'inferred {len(res)} functions in {dt:.1f} s')
    sigs, certs, why, drops, stmt_names, stats = E.build(res, set(fns))
    po = E.pack_of()
    stale, mods = [], []
    for k in fns:
        if k in why:
            sys.exit(f'{k}: the Python check fails: {why[k][:3]}')
        H = certs[k]
        sts = states(k, H, lambda g: sigs.get(I.callee(g), C.EMPTY))
        pre = I.CORE[k][1][:-2]
        cs = cuts(pre, budget)
        sizes = [sum(atoms(s) for s in pre[cs[i]:cs[i + 1]]) for i in range(len(cs) - 1)]
        print(f'{k}: {len(pre)} statements, {sum(sizes)} atoms, {len(cs) - 1} windows of at most {max(sizes)} atoms')
        for name, text in emit(k, H, sts, cs, stmt_names[k], po):
            path = os.path.join(out, k, name + '.lean')
            mods.append(f'LeanVM.Guest.CoreMode.GenCW.«{k}».{name}')
            if '--check' in argv:
                if not os.path.exists(path) or open(path, encoding='utf-8').read() != text:
                    stale.append(path)
            else:
                os.makedirs(os.path.dirname(path), exist_ok=True)
                with open(path, 'w', encoding='utf-8') as fh:
                    fh.write(text)
    if '--mods' in argv:
        with open(argv[argv.index('--mods') + 1], 'w') as fh:
            fh.write('\n'.join(mods) + '\n')
    if '--check' in argv:
        print('checked: ' + (f'{len(stale)} stale: {stale[:5]}' if stale else 'up to date'))
        if stale:
            sys.exit(1)


if __name__ == '__main__':
    main()
