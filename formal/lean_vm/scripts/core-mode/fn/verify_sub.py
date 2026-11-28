"""`verify_sub`'s contract (`sigc.py`): `verify_sub(pi_0, pi_1, seed_0, seed_1, g_squares, defer_out)` reads the exponent
tables `g_squares[g^i]`, `i < WIN_TAB_AT + WIN_TAB_LEN` (`exponent_tables`': the squares, the nibble shares and the
windows table, which its reads stay within), and leaves the fresh claim `defer_out[g^d]`, `d < DEFER_SIZE`, written."""
from fnrules import guest_const
from sigseed import sig, cell, num, run

TAB = guest_const('WIN_TAB_AT') + guest_const('WIN_TAB_LEN')
DSZ = guest_const('DEFER_SIZE')
_TAB = run(cell(0, [(6, 1)]), num(0), num(TAB), 1, 0)
CONTRACTS = {'verify_sub': sig(range(8), None, [], pre=[cell(0, [(6, 1)])], preR=[_TAB],
                               postR=[_TAB, run(cell(0, [(7, 1)]), num(0), num(DSZ), 1, 0)])}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []


# ---- its values' exponent bounds where they bound its callees' runs (`CoreMode.Own.verify_sub.vsBounds`, `gwFam`):
# `g_w` (409, `19 <= w <= 24`, range checked), `kb[2 + TABLE_KECCAK]` (120, its certified sizes), `g_n` (408, `g_n / kb[2]`
# range checked), `g_log_mem` (101) and `gmv` (485) (its certified sizes)

BOUNDS = {409: 25, 120: 25, 408: 49, 101: 31, 485: 31}


# ---- the proof stream (`hint_stream`'s `STREAM_CHUNK` residue runs of `stream·[0, STREAM_CHUNK·e(n))`,
# `n = stream_chunks`): its reads and its callees' runs over it, made up as the stream's run `⟨stream, 1, g^0,
# n^STREAM_CHUNK⟩` (`callcres.merged_runs`) and placed in it by residuals `sub c Q`, `subR q Q`. Their family
# (`CoreMode.Own.verify_sub.streamFam`) is sound by `EndExec.vsStreamQ` (`streamFam_okA`).
import fnrules as _R

STREAM_FAM = True


def _stream():
    return (((_R.val('verify_sub', 'stream'), 1),), 0)


def _stream_q():
    """`⟨stream, 1, g^0, stream_chunks^STREAM_CHUNK⟩`, a residual's run."""
    import infer as I
    n = next(s[2][1] for s in I.CORE['verify_sub'][1] if s[0] == 'call' and s[1] == 'hint_stream')
    return (_stream(), 1, ('num', 0), ('mono', (((n, _R.guest_const('STREAM_CHUNK')),), 0)))


def stream_runs(k):
    """The stream, its residues' stride (`callcres.merged_runs`, through `merged_runs`)."""
    return [(_stream(), _R.guest_const('STREAM_CHUNK'))] if k == 'verify_sub' else []


_CURS = []


def _cursors():
    """`verify_sub`'s values that may point into the stream: the stream, a product of such a value and a constant, a
    word a call or a dispatch returns given such an argument (an over-approximation, for the solver's search only)."""
    if not _CURS:
        import infer as I
        S = {_stream()[0][0][0]}
        for s in I.stmts(I.CORE['verify_sub'][1]):
            if s[0] == 'a' and s[1][0] in ('mul', 'copy') and any(v in S for v in s[1][2:]):
                S.add(s[1][1])
            elif s[0] == 'call' and any(v in S for v in s[2]):
                S.update(s[3])
            elif s[0] == 'dispatch' and any(v in S for v in s[3]):
                S.update(s[4])
        _CURS.append(S)
    return _CURS[0]


def merged_runs(k):
    """`callcres.merged_runs`' hook: each `(B, S)` whose `S` residue runs `⟨B·g^d, S, g^0, H⟩` it merges (the stream's;
    other blocks add theirs here)."""
    return (stream_runs(k) + chal_runs(k) or None) if k == 'verify_sub' else None


def merged_cell(k, c):
    """`callcres.cs_reads`' hook: a cell the merged runs may hold (the stream's cursors; other blocks add theirs)."""
    return stream_cell(k, c) or chal_cell(k, c)


def stream_cell(k, c):
    """A cell over a value that may point into the stream (`_cursors`)."""
    return k == 'verify_sub' and STREAM_FAM and any(b in _cursors() for b, _ in c[0])


# `CoreMode.Own.verify_sub.osRoom`, `lrsRoom`
OS_ROOM = [103, 109, 119, 137, 132, 138, 148, 166, 161, 167, 177, 195, 190, 196, 206]
LRS_ROOM = [(8, 57), (10, 63), (11, 75), (12, 81)]


def _arm(g, x):
    return next((c[2] for c in g if c[0] == 'arm' and c[1] == x), None)


def _cell(g, c):
    """`streamCell`."""
    bs, o = tuple(map(tuple, c[0])), c[1]
    if bs == ((1076, 1),) and o < 144:
        return True
    if bs == ((2920, 1),):
        m = _arm(g, 489)
        return o == 0 or (m is not None and m < 15 and 1 <= o <= OS_ROOM[m])
    if (bs, o) == (((55, 1), (108, 2), (460, 2)), 15):
        return True
    a = _arm(g, 1070)
    if a is None or a >= 4:
        return False
    S, K = LRS_ROOM[a]
    return bs == ((55, 1), (108, 2), (115, S), (412, S), (460, 2)) and 16 <= o <= K


# `verify_keccak`'s stream runs at its cursor `cursor@3·g^144` (`[1076]·g^144`), `tau_g = kb[7]` (value `120`): the
# `VK_S` residue runs `⟨[1076]·g^(144 + d), VK_S, 0, e(kb[7]) + VK_HI⟩` (`fn/verify_keccak.py`'s `ST_S`, `ST_HI`)
VK_AT, VK_S, VK_HI = 144, 24, 44


def arg_bound_mono(k, x):
    """`e(kb[7]) < 25` for `verify_keccak`'s stream bound `kb[7]·g^VK_HI` (`CoreMode.resArg`'s `.mono`)."""
    return BOUNDS.get(x) if k == 'verify_sub' and x == 120 else None


def _run(g, q):
    """`streamRun`."""
    (bs, o), S, lo, hi = q
    bs = tuple(map(tuple, bs))
    if bs == ((55, 1),) and o in (13, 14) and S == 2 and tuple(lo) == ('num', 0) and \
            tuple(hi) == ('mono', (((108, 1), (460, 1)), 1)):
        return True
    if bs == ((1076, 1),) and VK_AT <= o < VK_AT + VK_S and S == VK_S and tuple(lo) == ('num', 0) and \
            tuple(hi) == ('mono', (((120, 1),), VK_HI)):
        return True
    a = _arm(g, 1070)
    return a is not None and a < 4 and bs == ((55, 1), (108, 2), (460, 2)) and S == LRS_ROOM[a][0] and \
        16 <= o < 16 + S and tuple(lo) == ('num', 0) and tuple(hi) == ('mono', (((115, 1), (412, 1)), 0))


def stream_fam(k, r, g=()):
    """`CoreMode.Own.verify_sub.streamFamU`: a read or a callee's run in the stream, under the branch conditions."""
    if k != 'verify_sub' or not STREAM_FAM:
        return False
    if r[0] == 'under':
        return stream_fam(k, r[2], tuple(g) + tuple(r[1]))
    if r[0] == 'sub':
        return tuple(r[2]) == _stream_q() and _cell(g, r[1])
    if r[0] == 'subR':
        return tuple(r[2]) == _stream_q() and _run(g, r[1])
    if r[0] == 'lt':
        # `0 < e(stream_chunks)`
        return tuple(r[1]) == ('num', 0) and tuple(r[2]) == ('val', _stream_q()[3][1][0][0][0])
    return False


def arg_bound(k, x):
    """`e(x) < BOUNDS[x]` where `x` bounds a callee's runs (`link_rounds`', `check_stack_terminal`'s), the residual its
    family proves."""
    return BOUNDS.get(x) if k == 'verify_sub' else None


def fam(k, r):
    """`CoreMode.Own.verify_sub.gwFam` (`e(v) < m`, `BOUNDS[v] <= m < 2^62`), `chalFam`, `streamFam`."""
    return (k == 'verify_sub' and r[0] == 'lt' and tuple(r[1])[0] == 'val' and tuple(r[2])[0] == 'num' and
            r[1][1] in BOUNDS and BOUNDS[r[1][1]] <= r[2][1] < 2 ** 62) or chal_fam(k, r) or stream_fam(k, r)


# ---- the link's challenges: `squeeze_packed(.., chal·g, g_p)` writes `chal·g^(1 + i)`, `i < 8·e(g_p)`, its `8` residue
# runs `⟨[chal]·g^(1 + d), 8, 0, e(g_p)⟩`; `g_p` (value `645`, `g^p`, `p < 64`) bounds them
# (`CoreMode.Own.verify_sub.chalFam`)

CHAL_BOUNDS = {645: 64}
_arg_bound_gw = arg_bound


def arg_bound(k, x):
    """`e(g_p) < 64`, besides `BOUNDS`."""
    if k == 'verify_sub' and x in CHAL_BOUNDS:
        return CHAL_BOUNDS[x]
    return _arg_bound_gw(k, x)


# `8p >= LINK_FIXED + n + w + d >= 88 + n + 25` (`w >= 19`, `d >= 6`): the cells `chal·g^c`, `1 <= c <= 113`, and
# `chal·g_n·g^c`, `c <= 113`, are written (`CoreMode.Own.verify_sub.chalRead`)
CHAL, GP = 10, 645
CHAL_RUN = ((((CHAL, 1),), 1), 1, ('num', 0), ('mono', (((GP, 8),), 0)))
CHAL_BASES = (((CHAL, 1),), ((CHAL, 1), (115, 1), (412, 1)))
# `nu = chal·g_n·g_w·g^89` (`g_w = [108]·[460]·g`), read `[0, m)` under `link_terminal`'s arm `j` (selector `2893`),
# `m <= CHUNK_D[19 + j]` (`CoreMode.Own.verify_sub.nuRead`)
NU_BASES, NU_OFF, NU_SEL = ((CHAL, 1), (108, 1), (115, 1), (412, 1), (460, 1)), 90, 2893
NU_LENS = [6, 6, 7, 7, 8, 9]


def chal_runs(k):
    """The challenges' `8` residue runs, merged (`callcres.merged_runs`)."""
    return [(CHAL_RUN[0], 8)] if k == 'verify_sub' else []


def chal_cell(k, c):
    """A read or a needed run's base over the challenges."""
    return k == 'verify_sub' and (tuple(c[0]) in CHAL_BASES or tuple(map(tuple, c[0])) == NU_BASES)


def nu_read(g, q):
    """`CoreMode.Own.verify_sub.nuRead`."""
    b, S, lo, hi = q
    return (tuple(map(tuple, b[0])) == NU_BASES and b[1] == NU_OFF and S == 1 and lo[0] == 'num' and
            hi[0] == 'num' and any(c[0] == 'arm' and c[1] == NU_SEL and c[2] < 6 and hi[1] <= NU_LENS[c[2]]
                                   for c in g))


def chal_fam(k, r):
    """`CoreMode.Own.verify_sub.chalFam`."""
    if k != 'verify_sub':
        return False
    if r[0] == 'under' and r[2][0] == 'subR':
        return tuple(r[2][2]) == CHAL_RUN and (chal_fam(k, r[2]) or nu_read(r[1], r[2][1]))
    if r[0] == 'under':
        return chal_fam(k, r[2])
    if r[0] == 'lt' and tuple(r[1])[0] == 'val' and tuple(r[2])[0] == 'num':
        return CHAL_BOUNDS.get(r[1][1]) == r[2][1]
    if r[0] == 'lt' and tuple(r[1])[0] == 'num' and tuple(r[2]) == ('val', GP):
        return r[1][1] <= 14
    if r[0] == 'subR':
        (b, S, lo, hi), R2 = r[1], r[2]
        return (tuple(R2) == CHAL_RUN and tuple(b[0]) in CHAL_BASES and S == 1 and lo[0] == 'num' and
                hi[0] == 'num' and 1 <= b[1] and b[1] + hi[1] <= 114)
    return False


# ---- the blocks its dispatches write (`armblock`): `index_side`'s `below[0, w + 1)` as the run
# `⟨below, 1, 0, g_w·g⟩`, `one_plus_suffixes`' `corners[0, n + 1)` as `⟨corners, 1, 0, g_n·g⟩`; the residuals placing
# reads in them and the index point's below `g_w` (`CoreMode.Own.verify_sub.ixFam`)
_IX_GW = ((((108, 1), (460, 1)), 2))
_IX_GW_SEL = ((((108, 1), (460, 1), (795, 1)), 21))
_IX_GN = ((((115, 1), (412, 1)), 1))
_IX_GMV = ((((485, 1), (488, 1)), 17))
_fam_ix = fam


def _mono(x):
    return (tuple(map(tuple, x[1][0])), x[1][1]) if tuple(x)[0] == 'mono' else None


def ix_fam(k, r):
    """`CoreMode.Own.verify_sub.ixFam`."""
    if k != 'verify_sub':
        return False
    if r[0] == 'eq':
        return tuple(r[1]) == tuple(r[2])
    if r[0] == 'lt':
        a, b = tuple(r[1]), tuple(r[2])
        if a[0] == 'num' and b == ('val', 409):
            return a[1] <= 18
        if a[0] == 'num' and b[0] == 'mono':
            return _mono(b) in (_IX_GW, _IX_GW_SEL) and a[1] <= 19
        if a[0] == 'val' and b[0] == 'mono':
            return (_mono(b) in (_IX_GW_SEL, _IX_GW) and a[1] == 101) or (_mono(b) == _IX_GN and 115 <= a[1] <= 120) \
                or (_mono(b) == _IX_GMV and a[1] == 485)
        return False
    if r[0] == 'under' and len(r[1]) == 1 and tuple(r[1][0])[0] == 'arm' and r[2][0] == 'lt':
        _, x, j = tuple(r[1][0])
        a, b = tuple(r[2][1]), tuple(r[2][2])
        if a[0] != 'num' or b[0] != 'mono':
            return False
        return (x in (796, 2893) and _mono(b) == _IX_GW and j <= 5 and a[1] <= 19 + j) or \
            (115 <= x <= 120 and _mono(b) == _IX_GN and j <= 24 and a[1] <= j)
    return False


def fam(k, r):
    """`ixFam`, besides the families above."""
    return _fam_ix(k, r) or ix_fam(k, r)


FEATURES = dict(globals().get('FEATURES') or {})
FEATURES.setdefault('verify_sub', []).append({'armblock'})

# `kb[2 + TABLE_KECCAK]` (value `120`) named by its own base from the start (`seedEnv`): its floor check
# `kb[7] = q·g^9` would otherwise name it `q·g^9` there, after `table_size`'s dispatch on it and before `table_point`'s,
# whose arms then miss the former's guarantees (`condSt` matches a dispatch by its selector's monomial)
RES_EQ = dict(globals().get('RES_EQ') or {})
RES_EQ.setdefault('verify_sub', []).append(((((120, 1),), 0), (((120, 1),), 0)))

# ---- the windows-table index `g_w·g^-1` on the `flag == 1` arm (`zero 471`, `471 = flag + 1`): the read
# `g_squares[g_w·g^-1]`, its index `[108]·[460]·[472]·g` (`g_log_mem = [108]·g`, `g_w = [460]·g_log_mem`,
# `[472] = g^-1`), `w - 1 <= 23` (`CoreMode.Own.verify_sub.gwInvFam`)
GW_INV = (((108, 1), (460, 1), (472, 1)), 1)


def gw_inv_fam(k, r):
    """`CoreMode.Own.verify_sub.gwInvFam`: `under [.., zero 471, ..] (e(g_w·g^-1) < m)`, `24 <= m < 2^62`."""
    if k != 'verify_sub' or r[0] != 'under':
        return False
    q = r[2]
    return (('zero', 471) in [tuple(c) for c in r[1]] and q[0] == 'lt' and tuple(q[1])[0] == 'mono' and
            (tuple(tuple(b) for b in q[1][1][0]), q[1][1][1]) == GW_INV and tuple(q[2])[0] == 'num' and
            24 <= q[2][1] < 2 ** 62)


_fam_gc = fam


def fam(k, r):
    """`gwFam`, `chalFam`, `streamFam`, `ixFam` (in `_fam_gc`), `gwInvFam`."""
    return _fam_gc(k, r) or gw_inv_fam(k, r)
