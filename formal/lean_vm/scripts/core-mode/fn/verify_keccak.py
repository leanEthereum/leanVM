"""`verify_keccak`'s rules (`callc.py`): its loops' and its layers' bounds, arguments of exponent facts (`arg_bound`):
`pack_g = tau_g·g^-KECCAK_PACK_LOG` (value `18`), `e < 21` (`tau_g = kb[2 + TABLE_KECCAK]`, the Keccak table's log height
in `[FLOORS[TABLE_KECCAK], 24]`, carried from `verify_sub`); `step_g` (value `29`), `e < 2`, and `rem_g` (value `48`),
`e < KR_STEP`, products of its pinned bits; `tau_g` (value `6`), `e < 25` (`sel_bound`), the bound of the `z_vals`
runs its contract promises. Its equation residual (`RES_EQ`) names step `0`'s claim point by the point; its runs over
the head's exponents (`RUNS`) put each read run inside a written one. Its contract (`CONTRACTS`): the proof stream, the
table point `chi[0, e(tau_g))`, the output lanes and the windows table read; the two `z_vals` points
`[0, e(tau_g) + QKECCAK_SLOT_LOG)` (`check_stack_terminal`'s reads) and the 64 `slices` written. Its family:
`CoreMode/Fn/verify_keccak/{Fam, ExpB, Runs}.lean`."""
from fnrules import guest_const
from sigseed import sig, cell, num, run, ex

ARG_BOUNDS = {18: 25 - guest_const('KECCAK_PACK_LOG'), 29: 2, 48: guest_const('KR_STEP')}


def arg_bound(k, x):
    return ARG_BOUNDS.get(x) if k == 'verify_keccak' else None


# `tau_g` (value `6`), `e < 25`, the bound of its `z_vals` runs (`sel_bound`)
TAU_V, TAU_MIN, TAU_B = 6, 9, 25
EXP_B = {**ARG_BOUNDS, TAU_V: TAU_B}


def sel_bound(k, x):
    return TAU_B if k == 'verify_keccak' and x == TAU_V else None


WIN = 2 ** guest_const('WIN_TAB_BITS')
# frame cells of `cursor`, `tau_g`, `chi`, `output_lanes`, `z_vals`, `slices`, `tabs` (parameter `i` at `2 + i`)
CUR, TAU, CHI, OL, ZV, SL, TABS = 7, 8, 9, 10, 11, 12, 13
QS, QV = guest_const('QKECCAK_SLOT_LOG'), guest_const('QKECCAK_VARS_CAP')
# the proof stream: it reads `k = 24(h - 3) + 1106` words past `cursor` (`tau_g = g^h`), so no constant run holds them;
# `ST_S` residue runs `⟨cursor·g^d, ST_S, 0, e(tau_g) + ST_HI⟩`, `d < ST_S`, the words `[0, 24(h + ST_HI))`, which
# `verify_sub`'s stream has (`k` and at least `103` words of `open_stacked` past it)
ST_S, ST_HI = 24, 44
CONTRACTS = {'verify_keccak': sig(
    range(14), None, range(14, 21),
    preR=[run(cell(0, [(CUR, 1)]), num(0), ex(TAU, ST_HI), ST_S, d) for d in range(ST_S)] +
         [run(cell(0, [(CHI, 1)]), num(0), ex(TAU), 1, 0),
          run(cell(0, [(OL, 1)]), num(0), num(guest_const('KECCAK_LANES')), 1, 0),
          run(cell(0, [(TABS, 1)]), num(0), num(WIN), 1, 0)],
    postR=[run(cell(0, [(ZV, 1)]), num(0), ex(TAU, QS), 1, d) for d in (0, QV)] +
          [run(cell(0, [(SL, 1)]), num(0), num(guest_const('BASE_FIELD_BITS')), 1, 0)])}

# its loop0's run `chi·g^4·[0, e(tau_g·g^-4))` inside `chi[0, e(tau_g))` (`der`'s `negshiftR`)
FEATURES = {'verify_keccak': [{'der'}]}

# step `0`'s claim point (value `443`, loaded from `claims·g^KC_POINT`) is the point (value `62`) stored there
RES_EQ = {'verify_keccak': [((((443, 1),), 0), (((62, 1),), 0))]}


# the table height's lower bound `e(tau_g) >= KECCAK_MIN = 9`, carried from `verify_sub` with its upper bound
def fact(EM, base):
    """The solver's fact `c < e(tau_g)`, `c < 9`."""
    def f(self, st, a, b):
        if self.k != 'verify_keccak' or a[0] or not a[1] < TAU_MIN or b != (((TAU_V, 1),), 0):
            return None
        return [self.use(('vkTau', a[1]), ('lt', ('num', a[1]), ('val', TAU_V)))]
    return f


# Its runs over the head's exponents (`Fam.lean`'s `runFam`): `pack_g = tau_g·g^-4` as the monomial `P`, `y_g` as
# `Y = step_g^16·rem_g` (`rem_g` the product of its bit factors, values `33`, `37`, `42`, `47`), `e(tau_g) = h`,
# `e(pack_g) = h - 4`, `e(y_g) = h - 3`, `9 <= h <= 24`
P = ((6, 1), (17, 1))
REM = ((33, 1), (37, 1), (42, 1), (47, 1))
Y = (((29, 16),) + REM, 0)


def _run(b, o, S, lo, hi):
    return (((b, 1),), o), S, lo, hi


RUNS = [
    # loop0's run `chi·g^4·[0, e(pack_g))` inside `chi[0, e(tau_g))` (`der`)
    ('subR', _run(7, 4, 1, ('num', 0), ('mono', (P, 0))), _run(7, 0, 1, ('num', 0), ('val', 6))),
    # the point's residue runs inside its whole run `[0, e(y_g))`
    ('subR', ((((29, 16), (62, 1)), 0), 1, ('num', 0), ('mono', (REM, 0))), _run(62, 0, 1, ('num', 0), ('mono', Y))),
    # loop2's reads of the last layer's point `[0, e(pack_g))` inside its whole run
    ('subR', _run(1740, 0, 1, ('num', 0), ('mono', (P, 0))), _run(1740, 0, 1, ('num', 0), ('mono', Y))),
    # `z_vals`' pack coordinates `[4, e(tau_g))`, written by loops 1 and 2 at `z_vals·g^(4 + o)`
    ('subR', _run(9, 0, 1, ('num', 4), ('val', 6)), _run(9, 4, 1, ('num', 0), ('mono', (P, 0)))),
    ('subR', _run(9, QV, 1, ('num', 4), ('val', 6)), _run(9, QV + 4, 1, ('num', 0), ('mono', (P, 0)))),
] + [('subR', _run(62, d, 16, ('num', 0), ('val', 29)), _run(62, 0, 1, ('num', 0), ('mono', Y))) for d in range(16)]


def run_fam(r):
    """`runFam`: a run of `RUNS`, under any conditions; `e(pack_g) < n`, `21 <= n`; `c < e(pack_g·g^k)`, `c < 5 + k`."""
    if r in RUNS or (r[0] == 'under' and r[2] in RUNS):
        return True
    if r[0] == 'lt' and r[1] == ('mono', (P, 0)) and r[2][0] == 'num':
        return 21 <= r[2][1] < 2 ** 62
    if r[0] == 'lt' and r[1][0] == 'num' and r[2][0] == 'mono' and r[2][1][0] == P:
        return r[1][1] < 5 + r[2][1][1] and r[2][1][1] < 4294967296
    return False


# ---- the proof stream (`Fam.lean`'s `stFam`, `Stream.lean`): its `ST_S` residue runs merged
# (`callcres.merged_runs`) into `stQ = ⟨cursor, 1, 0, tau_g^ST_S·g^(ST_S·ST_HI)⟩` (`cursor` value `5`); each read
# `sub c stQ` and callee run `subR q stQ`, `c`, `q`'s base `cursor·M·g^o`, lies in it at every height `9 <= h <= 24`,
# each value of `M` and of the bounds a power of `g` whose exponent `stEx h` gives (the head's: `tau_g`, `step_g`,
# `rem_g`'s bit factors and their products)
CUR_V = 5
ST_B = (((CUR_V, 1),), 0)
ST_Q = (ST_B, 1, ('num', 0), ('mono', (((TAU_V, ST_S),), ST_S * ST_HI)))


def merged_runs(k):
    """`callcres.merged_runs`' hook: the stream's residue runs."""
    return [(ST_B, ST_S)] if k == 'verify_keccak' else None


def merged_cell(k, c):
    """`callcres.cs_reads`' hook: a cell over `cursor`."""
    return k == 'verify_keccak' and bool(c[0]) and tuple(c[0][0]) == (CUR_V, 1)


def st_ex(h):
    """`stEx h`: the exponents at height `h` of the head's values."""
    y = h - 3
    return {6: h, 29: y // 16, 48: y % 16, 33: y % 2, 37: 2 * (y // 2 % 2), 42: 4 * (y // 4 % 2),
            47: 8 * (y // 8 % 2)}


def _st_cell(h, c):
    bs, o = c
    t = o
    for v, a in bs:
        e = st_ex(h).get(v)
        if e is None:
            return None
        t += a * e
    return t


def _st_idx(h, i):
    i = tuple(i)
    if i[0] == 'num':
        return i[1]
    if i[0] == 'val':
        return st_ex(h).get(i[1])
    return _st_cell(h, (tuple(map(tuple, i[1][0])), i[1][1]))


def _st_rest(c):
    """`c`'s monomial past `cursor`, if `c` is over `cursor`."""
    bs = tuple(map(tuple, c[0]))
    return (bs[1:], c[1]) if bs and bs[0] == (CUR_V, 1) else None


def st_fam(r):
    """`stFam`: a read or a callee's run in the stream, or a bound over the head's values, under any conditions."""
    if r[0] == 'under':
        return st_fam(r[2])
    if r[0] == 'lt':
        # a run bound over the head's values below a constant at every height (the stream runs' `e(tau_g) + ST_HI`)
        a, b = tuple(r[1]), tuple(r[2])
        if a[0] != 'mono' or b[0] != 'num' or not b[1] < 2 ** 62:
            return False
        return all(_st_idx(h, a) is not None and _st_idx(h, a) < b[1] for h in range(TAU_MIN, TAU_B))
    if r[0] not in ('sub', 'subR') or tuple(r[2]) != ST_Q:
        return False
    q = (r[1], 1, ('num', 0), ('num', 1)) if r[0] == 'sub' else r[1]
    rest = _st_rest(q[0])
    if rest is None:
        return False
    for h in range(TAU_MIN, TAU_B):
        t, lo, hi = _st_cell(h, rest), _st_idx(h, q[2]), _st_idx(h, q[3])
        if t is None or lo is None or hi is None or not (lo < 2 ** 32 and hi < 2 ** 32):
            return False
        if lo < hi and not t + q[1] * (hi - 1) < ST_S * (h + ST_HI):
            return False
    return True


def fam(k, r):
    """Its exponent facts, equation residual, runs and stream (`Fam.lean`'s `expFam`, `ptEq`, `runFam`, `stFam`)."""
    if k != 'verify_keccak':
        return False
    if run_fam(r) or st_fam(r):
        return True
    if r[0] == 'eq':
        return (r[1], r[2]) in RES_EQ[k]
    if r[0] != 'lt':
        return False
    if r[1][0] == 'val' and r[2][0] == 'num':
        return EXP_B.get(r[1][1]) is not None and EXP_B[r[1][1]] <= r[2][1] < 2 ** 62
    return r[1][0] == 'num' and r[1][1] < TAU_MIN and r[2] == ('val', TAU_V)


OWN = []
