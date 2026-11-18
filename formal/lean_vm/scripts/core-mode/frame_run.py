"""Run the frame walk (`frame.py`) on every guest function and report: functions passing, failures
by cause, oracle loads, residual divisors. `MODE_CERT_CACHE` names `gen.py`'s cache of today's walk
(for the oracle); `FRAME_CACHE` caches the oracle run."""
import os, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import frame as FR  # noqa: E402
import frame_data as FD  # noqa: E402


def inputs(D, n):
    f = D['fns'][n]
    fx = D['facts'][n]
    F = FR.Facts(fx['env'], fx['fpOne'], fx['arms'], fx['scaled'], D['pows'])
    entry, ln = f['entry'], f['count']
    idx = {}; arms = {}; calls = {}; ids = {}
    for i, size in sorted(f['tabs'].items()):
        d0 = f['ops'][i - 1][1][1]
        pcs = tuple(sorted(set(p for p in (D['jt'].get(d0 + j) for j in range(size)) if p is not None)))
        local = all(entry < pc < entry + ln for pcs_ in [pcs] for pc in pcs_)
        key = ('a' if local else 'c', pcs)
        if key not in ids:
            tab = arms if local else calls
            ids[key] = len(tab)
            tab[ids[key]] = [pc - entry for pc in pcs] if local else list(pcs)
        idx[i] = ids[key]
    tgt = (idx, arms, calls)
    nzr = {i: [r[1] for r in rs if r[0] == 'nz'] for i, rs in D['R'].get(n, {}).items()}
    nzr = {i: v for i, v in nzr.items() if v}
    return F, entry, ln, D['fsig'][entry], tgt, nzr


def run(D, n, O=None, need=None):
    f = D['fns'][n]
    F, entry, ln, sig, tgt, nzr = inputs(D, n)
    w = FR.Walk(F, entry, ln, sig, D['fsig'], f['hints'], nzr, tgt, set(D['O'].get(n, []) if O is None else O),
                D['halt'], need=need)
    w.run(f['ops'])
    return w


def main():
    D = FD.load(os.environ['MODE_CERT_CACHE'], os.environ.get('FRAME_CACHE'))
    ok = 0; fails = collections.Counter(); ex = {}
    loads = 0; olen = 0; nzn = 0; needs = collections.Counter()
    for n in sorted(D['fns']):
        try:
            w = run(D, n)
            ok += 1; loads += sum(w.loads.values()); olen += len(D['O'].get(n, []))
            nzn += sum(len(v) for v in inputs(D, n)[5].values())
        except FR.Fail as e:
            k = e.args[0][0]
            fails[k] += 1; ex.setdefault(k, []).append((n, e.args[0][:4]))
    print('pass', ok, 'of', len(D['fns']), 'oracle offsets', olen, 'oracle loads used', loads, 'nz residuals', nzn)
    print('fails', fails.most_common())
    for k, xs in ex.items():
        print(k, len(xs), [(n, str(e)[:120]) for n, e in xs[:6]])


if __name__ == '__main__':
    main()
