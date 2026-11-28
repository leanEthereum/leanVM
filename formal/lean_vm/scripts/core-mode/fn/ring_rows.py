"""`ring_rows`'s contracts (`sigc.py`). `ring_rows(chain, zs, ps, c_table, count_g)` reads `c_table[g^k]`,
`k < BASE_FIELD_BITS`, and `zs[g^i]`, `ps[g^i]`, `i < log(count_g)`, and writes the rows `m <= log(count_g)` of
`BASE_FIELD_BITS` cells at `chain·g^(BASE_FIELD_BITS·m)`, as `BASE_FIELD_BITS` residue runs. Its loop `ring_rows_loop0(x, q, chain, zs, ps)`, one iteration a chunk of
`RS_CHUNK` rows, reads chunk `log x`'s first row and coordinates and leaves its rows written."""
import fnrules
from fnrules import guest_const, lean_def
from sigseed import sig, cell, num, ex, run

B = guest_const('BASE_FIELD_BITS')
C = guest_const('RS_CHUNK')


def loop0():
    W = B * C
    pre = [cell(k, [(2, W), (4, 1)]) for k in range(B)]
    preR = [run(cell(0, [(o, 1)]), ex(2), ex(3), C, d) for o in (5, 6) for d in range(C)]
    postL = [run(cell(0, [(4, 1)]), ex(2), ex(3), W, d) for d in range(B, W + B)]
    return sig(range(7), 7, [], pre=pre, preR=preR, term=['((.ex (.fr 2) 0), (.ex (.fr 3) 0))'], postL=postL)


CONTRACTS = {
    'ring_rows': sig(range(7), None, [],
                     preR=[run(cell(0, [(5, 1)]), num(0), num(B), 1, 0), run(cell(0, [(3, 1)]), num(0), ex(6), 1, 0),
                           run(cell(0, [(4, 1)]), num(0), ex(6), 1, 0)],
                     postR=[run(cell(0, [(2, 1)]), num(0), ex(6, 1), B, d) for d in range(B)]),
    'ring_rows_loop0': loop0(),
}


def _tup(x):
    return tuple(_tup(e) for e in x) if isinstance(x, (list, tuple)) else x


# its `count = q^8·r` split from hinted bits (`CoreMode.splitsC`), as its Lean data says (`CoreMode.spRg`)
SPLITS = {'ring_rows': _tup(lean_def('ring_rows', 'Fam', 'spRg'))}



def split(k):
    """Its certificate split at the dispatch's selector `r` (`HCert.arms`): each arm's rows past the loop's."""
    import infer as I
    if I.callee(k) == 'ring_rows':
        sp = SPLITS['ring_rows']
        return (sp[2], sp[4])
    return None


def arm_path(k):
    """Each arm checked under its selector's value (`CoreMode.armPath`): arm `j` knows `e(r) = j`."""
    import infer as I
    return I.callee(k) == 'ring_rows'


def sel_bound(k, x):
    """Its `count_g` below `g^(8·8)`, from its split (`CoreMode.splitRes`), bounding its rows' runs."""
    import infer as I
    if I.callee(k) == 'ring_rows' and x == fnrules.val('ring_rows', 'count_g'):
        sp = SPLITS['ring_rows']
        return sp[4] * sp[5]
    return None


OWN = []
