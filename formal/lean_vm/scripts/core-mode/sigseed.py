"""Contracts given by hand (`sigc.py`), for functions that have no signature as written (new to the guest, their frame
layout changed, or named by `sigc.py --fresh`): by stable name, the literal fields of `Fn.«k».csig : Mode.Sig` past its entry, as
`CoreMode/Sig/<pack>.lean` writes them (entry cells, self cell, pre, preR, term, return cells, post, postR, postL, preP,
postP, postLP, retV, postT, postC). The route's checks hold each to the function's heap signature (`CoreMode.ownOk`,
`fitB`) like any other.

A function's parameter `i` is its frame cell `2 + i`; a heap cell `⟨0, k, [(cell, e), ..]⟩` is `Π [cell]^e · g^k`, a run
`⟨cell, lo, hi, S, d⟩` its cells `·g^(S·i + d)`, `lo <= i < hi`."""


def _cell(k, bs):
    return '⟨0, %d, [%s]⟩' % (k, ', '.join('((.fr %d), %d)' % b for b in bs))


def _num(n):
    return '(.num %d)' % n


def _ex(o, c=0):
    return '(.ex (.fr %d) %d)' % (o, c)


def _run(c, lo, hi, S, d):
    return '⟨%s, %s, %s, %d, %d⟩' % (c, lo, hi, S, d)


def _l(xs):
    return '[%s]' % ', '.join(xs)


def _sig(entry, self_, ret, pre=(), preR=(), term=(), post=(), postR=(), postL=()):
    return ', '.join([_l(map(str, entry)), 'none' if self_ is None else '(some %d)' % self_, _l(pre), _l(preR),
                      _l(term), _l(map(str, ret)), _l(post), _l(postR), _l(postL)] + ['[]'] * 6)


# the proof stream, a parameter's run `[0, 8192)`
def _stream(o):
    return _run(_cell(0, [(o, 1)]), _num(0), _num(8192), 1, 0)


SEEDS = {}

# `eq_prefix_run_rev(chain, out, src, b1, n)`: reads `src`, `b1` below `g^n`, writes `chain` to `g^n` and `out` below.
for _n in range(33):
    SEEDS['eq_prefix_run_rev__L%d' % _n] = _sig(
        range(6), None, [6],
        pre=[_cell(k, [(o, 1)]) for k in range(_n) for o in (4, 5)],
        postR=[_run(_cell(0, [(2, 1)]), _num(0), _num(_n + 1), 1, 0)] +
        [_run(_cell(0, [(o, 1)]), _num(0), _num(_n), 1, 0) for o in (3, 4, 5) if _n])

# `eq_prefix_chain_rev(chain, out, src, b1, count_g)`: as `eq_prefix_chain`, `out` written below `count_g`.
SEEDS['eq_prefix_chain_rev'] = _sig(
    range(7), None, [],
    preR=[_run(_cell(0, [(o, 1)]), _num(0), _ex(6), 1, 0) for o in (4, 5)],
    postR=[_run(_cell(0, [(2, 1)]), _num(0), _ex(6, 1), 1, 0), _run(_cell(0, [(2, 1)]), _num(0), _num(1), 1, 0)] +
    [_run(_cell(0, [(o, 1)]), _num(0), _ex(6), 1, 0) for o in (3, 4, 5)])

# `verify_bus_gkr`'s point copy (the former `verify_bus_gkr_loop1`): `zeta[x] = row[x]` from `x` below `bound`.
SEEDS['verify_bus_gkr_loop0'] = _sig(
    range(6), 6, [],
    preR=[_run(_cell(0, [(5, 1)]), _ex(2), _ex(3), 1, 0)], term=['(%s, %s)' % (_ex(2), _ex(3))],
    postL=[_run(_cell(0, [(4, 1)]), _ex(2), _ex(3), 1, 0)])

# The radix-four layers (`gkr_layer(layers, rounds, gkr_pts, x_m, x_j, start_g, g_bus_mu, tabs, stream, par, odd)`,
# layer `j = 4m + par` at `x_m = g^m`, `x_j = g^j`). Its record `layers·x_j^20·start_g^10`, the next one `20` words on;
# its point in row `j + 1` of `gkr_pts` (`gkr_pts·x_j^40·g^40`), its cells `[0, 2 par)`, then `8` a step of the loop,
# `m` steps, then the last `2 - odd`; it writes row `j + 2` alike, from `2 par + 2`.
REC, ROW0 = 10, 40


def _layer(p, o):
    rec = [(2, 1), (6, 20), (7, 10)]
    row = [(4, 1), (6, 40)]
    tail = [(4, 1), (5, 8), (6, 40)]
    return _sig(
        range(11), None, [],
        pre=[_cell(k, rec) for k in range(REC)] + [_cell(ROW0 + c, row) for c in range(2 * p)] +
        [_cell(ROW0 + 2 * p + q, tail) for q in range(2 - o)],
        preR=[_run(_cell(ROW0, row), _num(0), _ex(5), 8, 2 * p + q) for q in range(8)] + [_stream(10)],
        post=[_cell(2 * REC + k, rec) for k in range(REC)] + [_cell(2 * ROW0 + c, row) for c in range(2 * p + 2)] +
        [_cell(2 * ROW0 + 2 * p + 2 + q, tail) for q in range(2)],
        postR=[_run(_cell(2 * ROW0, row), _num(0), _ex(5), 8, 2 * p + 2 + q) for q in range(8)])


# `gkr_layer`'s loop (`y, x_m, head, qrow, nqrow, tabs`): `8` rounds from the record `head·y` (fields `862` apart, its
# cursor at `4310`), the point `qrow·y^8`, the record `head·y·g` and the cells `nqrow·y^8·g^q` written; the stream is its
# caller's cell `10` (`CoreMode.stLoops`).
def _layer_loop():
    rd = [(2, 1), (4, 1)]
    return _sig(
        range(8), 8, [],
        pre=[_cell(862 * f, rd) for f in range(7)],
        preR=[_run(_cell(0, [(5, 1)]), _ex(2), _ex(3), 8, q) for q in range(8)] +
        ['⟨⟨0, 0, [((.hp 1 10), 1)]⟩, (.num 0), (.num 8192), 1, 0⟩'],
        term=['(%s, %s)' % (_ex(2), _ex(3))],
        postL=[_run(_cell(0, [(4, 1)]), _ex(2), _ex(3), 1, 862 * f + 1) for f in range(7)] +
        [_run(_cell(0, [(6, 1)]), _ex(2), _ex(3), 8, q) for q in range(8)])


# `gkr_layers(layers, rounds, gkr_pts, n_four, rem_g, start_g, g_bus_mu, tabs, stream, odd)`: layers `0 .. 4n + r`
# (`n_four = g^n`, `rem_g = g^r`): from the record of layer `0` and row `1`, to the record of layer `L = 4n + r` and
# row `L + 1` (its cells `[0, 2r)`, `8` a step for `n` steps, the last two), over the selector `rem_g` (`abx`).
def _layers(o):
    row = [(4, 1), (5, 160), (6, 40)]
    return _sig(
        range(11), None, [11],
        pre=[_cell(k, [(2, 1), (7, 10)]) for k in range(REC)] + [_cell(ROW0 + q, [(4, 1)]) for q in range(2)],
        preR=[_stream(10)],
        post=[_cell(k, [(2, 1), (5, 80), (6, 20), (7, 10)]) for k in range(REC)] +
        [_cell(ROW0 + q, [(4, 1), (5, 168), (6, 42)]) for q in range(2)],
        postR=[_run(_cell(ROW0, row), _num(0), _ex(6), 2, d) for d in range(2)] +
        [_run(_cell(ROW0, [(4, 1), (5, 160), (6, 42)]), _num(0), _ex(5), 8, q) for q in range(8)])


# `gkr_layers`' loop (`x_m, n_four, layers, rounds, gkr_pts, start_g, g_bus_mu, tabs, stream`): layers `4m .. 4m + 3`.
def _layers_loop(o):
    return _sig(
        range(11), 11, [],
        pre=[_cell(k, [(2, 80), (4, 1), (7, 10)]) for k in range(REC)] +
        [_cell(ROW0 + q, [(2, 168), (6, 1)]) for q in range(2 - o)],
        preR=[_run(_cell(ROW0, [(2, 160), (6, 1)]), _num(0), _ex(2), 8, q) for q in range(8)] + [_stream(10)],
        term=['(%s, %s)' % (_ex(2), _ex(3))],
        post=[_cell(k, [(3, 80), (4, 1), (7, 10)]) for k in range(REC)] +
        [_cell(ROW0 + q, [(3, 168), (6, 1)]) for q in range(2)],
        postR=[_run(_cell(ROW0, [(3, 160), (6, 1)]), _num(0), _ex(3), 8, q) for q in range(8)],
        postL=[_run(_cell(0, [(4, 1), (7, 10)]), _ex(2), _ex(3), 80, 20 * t + k) for t in range(1, 5)
               for k in range(REC)] +
        [_run(_cell(0, [(6, 1)]), _ex(2), _ex(3), 168, 208 + q) for q in range(2)])


# `gkr_last_layers(layers, rounds, gkr_pts, n_four, m4, start_g, g_bus_mu, tabs, stream, r, odd)`: layers
# `4n .. 4n + r - 1` (`m4 = g^(4n)`), from the record of layer `4n` and its row to those of layer `4n + r`.
def _last(r, o):
    rec = [(2, 1), (6, 20), (7, 10)]
    if r == 0:
        # no layer: the record it is given is the last
        return _sig(range(11), None, [11], pre=[_cell(k, rec) for k in range(REC)],
                    post=[_cell(k, rec) for k in range(REC)])
    row = [(4, 1), (6, 40)]
    tail = [(4, 1), (5, 8), (6, 40)]
    return _sig(
        range(11), None, [11],
        pre=[_cell(k, rec) for k in range(REC)] + [_cell(ROW0 + q, tail) for q in range(2 - o)],
        preR=[_run(_cell(ROW0, row), _num(0), _ex(5), 8, q) for q in range(8)] + [_stream(10)],
        post=[_cell(20 * t + k, rec) for t in range(1, r + 1) for k in range(REC)] +
        [_cell(ROW0 * (r + 1) + c, row) for c in range(2 * r)] +
        [_cell(ROW0 * (t + 1) + 2 * t + q, tail) for t in range(1, r + 1) for q in range(2)],
        postR=[_run(_cell(ROW0 * (r + 1), row), _num(0), _ex(5), 8, 2 * r + q) for q in range(8)])


for _o in range(2):
    for _p in range(4):
        SEEDS['gkr_layer__L%d_L%d' % (_p, _o)] = _layer(_p, _o)
        SEEDS['gkr_layer__L%d_L%d_loop0' % (_p, _o)] = _layer_loop()
        SEEDS['gkr_last_layers__L%d_L%d' % (_p, _o)] = _last(_p, _o)
    SEEDS['gkr_layers__L%d' % _o] = _layers(_o)
    SEEDS['gkr_layers__L%d_loop0' % _o] = _layers_loop(_o)


# `decode_query_windows__L14_L2`'s windows: its last window has four cells and the frame cell eight past it is
# not written at the return (the compiler reuses it), so that pointer's cells `[0, 8)`, the others' `[0, 9)`.
SEEDS['decode_query_windows__L14_L2'] = '[0, 1, 2, 3, 4, 5], none, [], [⟨⟨0, 0, [((.fr 5), 1)]⟩, (.num 0), (.num 64), 1, 0⟩], [], [], [], [⟨⟨0, 0, [((.fr 3), 1)]⟩, (.num 0), (.num 9), 1, 0⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.num 0), (.num 9), 1, 0⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.num 0), (.num 64), 1, 0⟩], [], [], [(⟨⟨0, 0, [((.fr 4), 1)]⟩, (.num 0), (.num 8), 1, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 4), 1)]⟩, (.num 8), (.num 9), 1, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7])], [], [], [], []'

# Their callers, which pass the windows on (the last window of each block of nine likewise).
SEEDS['level_positions__L3_L14_L2'] = '[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], none, [], [⟨⟨0, 0, [((.fr 10), 1)]⟩, (.num 0), (.num 64), 1, 0⟩], [], [11, 12, 13, 14, 15], [], (List.flatten [[⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 0), (.num 9), 1, 0⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 3), 9, 0⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 3), 9, 1⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 3), 9, 2⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 3), 9, 3⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 3), 9, 4⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 3), 9, 5⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 3), 9, 6⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 3), 9, 7⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 3), 9, 8⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 0), (.num 9), 1, 0⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 0⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 1⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 2⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 3⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 4⟩], [⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 5⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 6⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 7⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 8⟩, ⟨⟨0, 0, [((.fr 10), 1)]⟩, (.num 0), (.num 64), 1, 0⟩]]), [], [], [(⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 0), (.num 8), 1, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 8), (.num 9), 1, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 1⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 2⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 3⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 4⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 5⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 6⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 7⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 3), 9, 8⟩, [0, 1, 2, 3, 4, 5, 6, 7])], [], [], [], []'
SEEDS['level_positions__L3_L14_L2_loop0'] = '[0, 1, 2, 3, 4, 5, 6, 7], (some 8), [⟨0, 0, [((.fr 2), 5), ((.fr 4), 1)]⟩, ⟨0, 1, [((.fr 2), 5), ((.fr 4), 1)]⟩, ⟨0, 2, [((.fr 2), 5), ((.fr 4), 1)]⟩, ⟨0, 3, [((.fr 2), 5), ((.fr 4), 1)]⟩, ⟨0, 4, [((.fr 2), 5), ((.fr 4), 1)]⟩], [⟨⟨0, 0, [((.fr 7), 1)]⟩, (.num 0), (.num 64), 1, 0⟩], [((.ex (.fr 2) 0), (.ex (.fr 3) 0))], [], [], [], (List.flatten [[⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 5⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 6⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 7⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 8⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 9⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 0⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 1⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 2⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 3⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 4⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 5⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 6⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 7⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 8⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 0⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 1⟩], [⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 2⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 3⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 4⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 5⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 6⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 7⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 8⟩]]), [], [], [(⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 1⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 2⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 3⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 4⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 5⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 6⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 7⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 8⟩, [0, 1, 2, 3, 4, 5, 6, 7])], [], [], []'
SEEDS['level_positions__L4_L14_L2'] = '[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], none, [], [⟨⟨0, 0, [((.fr 10), 1)]⟩, (.num 0), (.num 64), 1, 0⟩], [], [11, 12, 13, 14, 15], [], (List.flatten [[⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 0), (.num 9), 1, 0⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 4), 9, 0⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 4), 9, 1⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 4), 9, 2⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 4), 9, 3⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 4), 9, 4⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 4), 9, 5⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 4), 9, 6⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 4), 9, 7⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 4), 9, 8⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 0), (.num 9), 1, 0⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 0⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 1⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 2⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 3⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 4⟩], [⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 5⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 6⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 7⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 8⟩, ⟨⟨0, 0, [((.fr 10), 1)]⟩, (.num 0), (.num 64), 1, 0⟩]]), [], [], [(⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 0), (.num 8), 1, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 8), (.num 9), 1, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 1⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 2⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 3⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 4⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 5⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 6⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 7⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 4), 9, 8⟩, [0, 1, 2, 3, 4, 5, 6, 7])], [], [], [], []'
SEEDS['level_positions__L4_L14_L2_loop0'] = '[0, 1, 2, 3, 4, 5, 6, 7], (some 8), [⟨0, 0, [((.fr 2), 5), ((.fr 4), 1)]⟩, ⟨0, 1, [((.fr 2), 5), ((.fr 4), 1)]⟩, ⟨0, 2, [((.fr 2), 5), ((.fr 4), 1)]⟩, ⟨0, 3, [((.fr 2), 5), ((.fr 4), 1)]⟩, ⟨0, 4, [((.fr 2), 5), ((.fr 4), 1)]⟩], [⟨⟨0, 0, [((.fr 7), 1)]⟩, (.num 0), (.num 64), 1, 0⟩], [((.ex (.fr 2) 0), (.ex (.fr 3) 0))], [], [], [], (List.flatten [[⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 5⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 6⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 7⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 8⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 9⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 0⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 1⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 2⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 3⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 4⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 5⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 6⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 7⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 8⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 0⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 1⟩], [⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 2⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 3⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 4⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 5⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 6⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 7⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 8⟩]]), [], [], [(⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 1⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 2⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 3⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 4⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 5⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 6⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 7⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 8⟩, [0, 1, 2, 3, 4, 5, 6, 7])], [], [], []'
SEEDS['level_positions__L7_L14_L2'] = '[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], none, [], [⟨⟨0, 0, [((.fr 10), 1)]⟩, (.num 0), (.num 64), 1, 0⟩], [], [11, 12, 13, 14, 15], [], (List.flatten [[⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 0), (.num 9), 1, 0⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 7), 9, 0⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 7), 9, 1⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 7), 9, 2⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 7), 9, 3⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 7), 9, 4⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 7), 9, 5⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 7), 9, 6⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 7), 9, 7⟩, ⟨⟨0, 0, [((.fr 8), 1)]⟩, (.num 1), (.num 7), 9, 8⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 0), (.num 9), 1, 0⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 0⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 1⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 2⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 3⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 4⟩], [⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 5⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 6⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 7⟩, ⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 8⟩, ⟨⟨0, 0, [((.fr 10), 1)]⟩, (.num 0), (.num 64), 1, 0⟩]]), [], [], [(⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 0), (.num 8), 1, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 8), (.num 9), 1, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 1⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 2⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 3⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 4⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 5⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 6⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 7⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 9), 1)]⟩, (.num 1), (.num 7), 9, 8⟩, [0, 1, 2, 3, 4, 5, 6, 7])], [], [], [], []'
SEEDS['level_positions__L7_L14_L2_loop0'] = '[0, 1, 2, 3, 4, 5, 6, 7], (some 8), [⟨0, 0, [((.fr 2), 5), ((.fr 4), 1)]⟩, ⟨0, 1, [((.fr 2), 5), ((.fr 4), 1)]⟩, ⟨0, 2, [((.fr 2), 5), ((.fr 4), 1)]⟩, ⟨0, 3, [((.fr 2), 5), ((.fr 4), 1)]⟩, ⟨0, 4, [((.fr 2), 5), ((.fr 4), 1)]⟩], [⟨⟨0, 0, [((.fr 7), 1)]⟩, (.num 0), (.num 64), 1, 0⟩], [((.ex (.fr 2) 0), (.ex (.fr 3) 0))], [], [], [], (List.flatten [[⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 5⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 6⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 7⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 8⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 5, 9⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 0⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 1⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 2⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 3⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 4⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 5⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 6⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 7⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 8⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 0⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 1⟩], [⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 2⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 3⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 4⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 5⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 6⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 7⟩, ⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 8⟩]]), [], [], [(⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 1⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 2⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 3⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 4⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 5⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 6⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 7⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 6), 1)]⟩, (.ex (.fr 2) 0), (.ex (.fr 3) 0), 9, 8⟩, [0, 1, 2, 3, 4, 5, 6, 7])], [], [], []'
