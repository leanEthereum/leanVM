"""The frame walk's (`frame.py`) inputs for a function (`inputs`) and its residual divisors from its own walk (`own_nz`),
for `frame_gen.py`."""
import os, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import frame as FR  # noqa: E402


def inputs(D, n, nzr):
    """The walk's inputs, its residual divisors `nzr`."""
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
            # one numbering for both kinds: the walk reads a table's arms and its callees at the same key
            tab = arms if local else calls
            ids[key] = len(ids)
            tab[ids[key]] = [pc - entry for pc in pcs] if local else list(pcs)
        idx[i] = ids[key]
    tgt = (idx, arms, calls)
    return F, entry, ln, D['fsig'][entry], tgt, nzr


def own_nz(D, n, O, S=frozenset()):
    """The residual divisors the walk needs (`FFun.nzr`), by offset: each `MUL` it back-solves through a divisor it
    cannot show nonzero, by its own inference."""
    f = D['fns'][n]
    F, entry, ln, sig, tgt, _ = inputs(D, n, {})
    nz = collections.defaultdict(set)

    def need(*why):
        if why[0] == 'nz':
            nz[why[1]].add(why[2])
            return True
        return False
    FR.Walk(F, entry, ln, sig, D['fsig'], f['hints'], {}, tgt, set(O), D['halt'], need=need, S=set(S)).run(f['ops'])
    return {i: sorted(xs) for i, xs in sorted(nz.items())}
