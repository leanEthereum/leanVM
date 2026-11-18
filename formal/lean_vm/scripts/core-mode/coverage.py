"""Coverage of the core inference (`infer.py`) by milestone scope (`formal/notes/core-mode.md`, section 5), under
`heapOkC`'s format and with the inference's further features. A measurement, not a proof.

Scopes, from the census (`census.py`): M2, the functions with calls and no loop (226, 210 strict) and those reading
through a callee's returned word (the census's callee-returned class, the 11 `open_stacked` among them); M3, the
functions whose reads are points or loop runs (1,280); M4, the rest; all.

usage (from formal/lean_vm): python3 -I scripts/core-mode/coverage.py [--configs lean,lean+callIfR,...,full]
"""
import sys, os, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
argv = list(sys.argv)
sys.argv = sys.argv[:1]
import infer as I
import census as C


def census_sets():
    sigs, res = {}, {}
    for k in C.order():
        f = C.Fn(k, sigs)
        sigs[k] = f.run()
        res[k] = f
    hard = {'pointer-from-memory', 'data-index', 'callee-returned', 'own-buffer-unwritten', 'other',
            'unknown-pointer', 'callee-loop-run-pre', 'pre-loop-run'}
    soft = {'pre-loop-run', 'callee-loop-run-pre'}
    returned = {k for k, f in res.items() if any(c == 'callee-returned' for c, _ in f.unc)}
    m3 = {k for k, f in res.items() if not any(c in hard - soft for c, _ in f.unc)}
    m2 = {k for k in res if I.shape(k) == 'calls'} | returned
    return {'M2': m2, 'M3': m3 - m2, 'M4': set(res) - m2 - m3, 'all': set(res)}


CONFIGS = {
    'lean': set(),
    'lean+callIfR': {'callIfR'},
    'lean+callIfR+rules+idx': {'callIfR', 'rules', 'idx'},
    'requested': {'callIfR', 'retM', 'hv', 'join', 'cond', 'idx', 'div', 'rules'},
    'full': set(I.FEATURES),
    # milestone 4's families (`objs.py`, `ptrrun.py`) over what milestones 2-3 had
    'm3': set(I.FEATURES) - {'obj', 'narrow', 'pfr', 'armx'},
    'm3+obj': set(I.FEATURES) - {'narrow', 'pfr', 'armx'},
    'm3+obj+narrow': set(I.FEATURES) - {'pfr', 'armx'},
    'm3+obj+narrow+pfr': set(I.FEATURES) - {'armx'},
}


def main():
    scopes = census_sets()
    names = argv[argv.index('--configs') + 1].split(',') if '--configs' in argv else list(CONFIGS)
    print('scope sizes:', {s: len(v) for s, v in scopes.items()})
    for name in names:
        feats = CONFIGS[name] if name in CONFIGS else set(name.split('+')) - {'lean'}
        I.F.clear()
        I.F.update(feats)
        res, dt = I.run_all()
        clean, closed = I.closure(res)
        nres = {k: len(I.used_res(P)) for k, P in res.items()}
        print(f'{name} ({",".join(sorted(feats)) or "heapOkC"}; {dt:.1f} s): witnessed / closed / residuals / uncovered reads')
        for s, ks in scopes.items():
            unc = sum(len(res[k].unc) + I.misses(res[k]) for k in ks)
            print(f'  {s:4s} {len(ks):5d} fns: {sum(k in clean for k in ks):5d} witnessed, {sum(k in closed for k in ks):5d} closed,'
                  f' {sum(nres[k] for k in ks):5d} residuals in {sum(1 for k in ks if nres[k]):4d} fns, {unc:6d} uncovered')
        fams = collections.Counter()
        for k, P in res.items():
            for i in I.used_res(P):
                fams[I.res_family(P, P.res[i])] += 1
        print('  residuals by family:', dict(sorted(fams.items(), key=lambda x: -x[1])))


if __name__ == '__main__':
    main()
