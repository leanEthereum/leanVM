"""`open_stacked`'s rules: its rate values' exponent bounds (`level_rate`'s, matched per level) and its table read at
its rate selector."""
import re


# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []


# ---- its rate values (`CoreMode.armExpB`, its family `CoreMode.Own.open_stacked.fams`, `expFam`)

def _os(k):
    return re.fullmatch(r'open_stacked__L\d+', k) is not None


def _pow(c):
    """`CoreMode.powOf1`: the exponent of the constant word `c = g^e` the guest's powers name, `1` at `0`."""
    import infer
    if c is None or c[1] != 0:
        return None
    return 0 if c[0] == 1 else dict(infer.D['pows']).get(c[0])


def arm_exp(k, x):
    """`CoreMode.armExpB`: `x` copied from a constant `g^e` in every arm of a top-level `match` before any statement
    that may return (`level_rate`'s values, bound once by its `match`): the least bound `max e + 1`, or None."""
    import infer as I
    import heapc
    for s in I.CORE[k][1]:
        if s[0] == 'match' and s[2]:
            es = []
            for arm in s[2]:
                atoms = []
                for t in arm:
                    if t[0] == 'a':
                        atoms.append(t[1])
                    elif not heapc.noret(t):
                        break
                cs = {a[1]: a[2] for a in atoms if a[0] == 'const'}
                e = next((_pow(cs.get(a[2])) for a in atoms if a[0] == 'copy' and a[1] == x and _pow(cs.get(a[2])) is not None),
                         None)
                if e is None:
                    break
                es.append(e)
            else:
                return max(es) + 1
        if not heapc.noret(s):
            return None
    return None


def arg_bound(k, x):
    return arm_exp(k, x) if _os(k) else None


def _sels(k):
    """The selectors of the top-level `match`es before any statement that may return, with their numbers of arms."""
    import infer as I
    import heapc
    out = []
    for s in I.CORE[k][1]:
        if s[0] == 'match':
            out.append((s[1], len(s[2])))
        if not heapc.noret(s):
            break
    return out


def sel_pts(k, r):
    """`CoreMode.Own.open_stacked.selPts`: a cell `[B]·[J]·g^o`, `J` a top-level `match`'s selector of `m` arms, one of
    the points `[B]·g^(o + t)`, `t < m` (`pos_totals[rate_sel]`)."""
    if r[0] != 'subP' or len(r[1][0]) != 2 or any(e != 1 for _, e in r[1][0]):
        return False
    (a, _), (b, _) = r[1][0]
    for B, J in ((a, b), (b, a)):
        for x, m in _sels(k):
            if x == J and m <= 64 and all((((B, 1),), r[1][1] + t) in r[2] for t in range(m)):
                return True
    return False


def fam(k, r):
    """`CoreMode.Own.open_stacked.fams`: `expFam` (`e(x) < n`, `x` pinned below `n`, `callcres.val_exp`) or `selPts`."""
    import callcres
    if not _os(k):
        return False
    if r[0] == 'lt' and r[1][0] == 'val' and r[2][0] == 'num' and r[2][1] < 2 ** 62:
        import infer
        return callcres.val_exp(infer.CORE[k][1], r[1][1], 0, r[2][1])
    return sel_pts(k, r)


# a read at a selector among the points it can be (`sel_pts`) wants the solver's `lastres` form
FEATURES = {k: [{'lastres'}] for k in __import__('fnrules').shapes('open_stacked')}


def fact(EM, base):
    """The solver's fact `e(x) < n` of a top-level selector `x` of `m <= n` arms (the `sel` family), at offset `0`."""
    def f(self, st, a, b):
        if not _os(self.k) or b[0] or not b[1] < 2 ** 62 or a[1] != 0 or len(a[0]) != 1 or a[0][0][1] != 1:
            return None
        x = a[0][0][0]
        if EM.C.idxF(st.env, ('val', x)) != (((x, 1),), 0):
            return None
        if any(x2 == x and m <= b[1] for x2, m in _sels(self.k)):
            return [self.use(('sel', x, 0, b[1]), ('lt', ('val', x), ('num', b[1])))]
        return None
    return f


_SIGS = {}


def res_filter(k, r):
    """The residuals the solver states at it are of a family (the pool's facts the solver may use there)."""
    if not _os(k):
        return True
    import callcres
    if not _SIGS:
        import route
        _SIGS.update(route.sigs())
    return callcres.res_ok(k, [r], _SIGS)


# ---- its certificate split at the rate selector (`CoreMode.heapOkC`, `HCert.arms`): each rate's arm checked with its
# own `level_rate` constants, every later level's rate `match` on the same selector taken at that arm (`cond`), so
# `level_residual` reads the positions its arm's `level_positions` wrote

def split(k):
    """`(x, n)`: the rate selector (its first top-level `match`'s) and its arms."""
    if not _os(k):
        return None
    s = _sels(k)
    return s[0] if s else None


# ---- its contracts (`sigc.py`): the proof stream's cells it reads, `cursor[g^k]`, `k < N` (its shared scalars, one
# count a stacked log-size, whatever the rate), and the tables' runs its windows and grinds read; it writes its returned
# point and `1 + point` whole, `SIZE_BITS + QKECCAK_SLOT_LOG` cells each (returns `1`, `2`: `check_stack_terminal`'s)
from sigseed import sig as _sig, cell as _cell, num as _num, run as _run
from fnrules import guest_const as _gc

STREAM = [103, 109, 119, 137, 132, 138, 148, 166, 161, 167, 177, 195, 190, 196, 206]
_PT = _gc('SIZE_BITS') + _gc('QKECCAK_SLOT_LOG')


def contract(m):
    return _sig(range(13), None, [13, 14, 15, 16, 17, 18], pre=[_cell(k, [(11, 1)]) for k in range(STREAM[m])],
                preR=[_run(_cell(0, [(12, 1)]), _num(0), _num(n), 1, 0) for n in (2, 64, 128, 2048)],
                postR=[_run(_cell(0, [(r, 1)]), _num(0), _num(_PT), 1, 0) for r in (14, 15)])


CONTRACTS = {'open_stacked__L%d' % m: contract(m) for m in range(len(STREAM))}
