"""`squeeze_packed`'s contracts (`sigc.py`): `squeeze_packed(fs0, .., fs4, out, count_g)` writes the `8` rate cells of
each of its `e(count_g)` permutations, `out·g^(8j + d)`, `d < 8`, `j < e(count_g)`, as `8` residue runs (the loop's `32`
merged, then the tail arms' blocks, `armblock`). Its loop `squeeze_packed_loop0(xk, h_g, recs, out)`, over `xk = g^j`,
`j < e(h_g)`, reads the record `recs·xk^FS_CELLS·g^i`, `i < FS_CELLS`, and writes the next one and the `32` rate cells
`out·xk^32·g^d`, `d < 32`."""
from fnrules import guest_const
from sigseed import sig, cell, num, ex, run

FS = guest_const('FS_CELLS')
# the rate cells a frame of four permutations writes
CELLS = 32


def loop():
    # the counter `xk` (cell `2`) below the bound `h_g` (cell `3`); `recs` cell `4`, `out` cell `5`
    over = lambda base, S, d: run(cell(0, [(base, 1)]), ex(2), ex(3), S, d)
    return sig(range(6), 6, [], pre=[cell(i, [(2, FS), (4, 1)]) for i in range(FS)],
               term=['(%s, %s)' % (ex(2), ex(3))],
               postL=[over(5, CELLS, d) for d in range(CELLS)] + [over(4, FS, FS + i) for i in range(FS)])


def top():
    # `out` cell `7`, `count_g` cell `8`; the five returned words cells `9..13`
    return sig(range(9), None, range(9, 14), postR=[run(cell(0, [(7, 1)]), num(0), ex(8), 8, d) for d in range(8)])


CONTRACTS = {'squeeze_packed_loop0': loop(), 'squeeze_packed': top()}

# its count `count_g` (value `6`), `g^p`, `p < 64` (its six hinted bits; `B1.Link.MeaningSP`): the bound of its runs
# (`CoreMode.Own.squeeze_packed.countFam`)
COUNT_V, COUNT_B = 6, 64
CAPE = 2 ** 62


def sel_bound(k, x):
    return COUNT_B if k == 'squeeze_packed' and x == COUNT_V else None


def fam(k, r):
    """`CoreMode.Own.squeeze_packed.countFam`: `e(count_g) < m`, `64 <= m < capE`."""
    return (k == 'squeeze_packed' and r[0] == 'lt' and tuple(r[1]) == ('val', COUNT_V) and r[2][0] == 'num' and
            COUNT_B <= r[2][1] < CAPE)

OWN = []
