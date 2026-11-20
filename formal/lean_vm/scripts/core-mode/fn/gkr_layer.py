"""`gkr_layer`'s rules: its specializations `gkr_layer__L{par}_L{odd}` and their loops."""
from sigseed import sig, cell, num, ex, run, stream
import fnrules


# `x_m`'s exponent below `4` (`Res.expFacts`, `EndExec.GlQ`)
EXP_FACTS = [('gkr_layer__L%d_L%d' % (p, o), fnrules.param('gkr_layer', 'x_m'), None, 4) for p in range(4) for o in range(2)]

# its loop reads the proof stream past the cursor `17`, its caller's cell `10` the stream, `32` words an iteration
# (`CoreMode.stLoops`)
ST_LOOPS = {'gkr_layer__L%d_L%d_loop0' % (p, o): (10, 17, 32) for p in range(4) for o in range(2)}

# its cursors (`CoreMode.glQC`, `EndExec.gl_curs`): the value its layer record's cursor is loaded to (`21`), read `8 par`
# words past (its first `2 par` rounds), and its last record's (the tail), read `4 (2 - odd) + 12` words past (its last
# rounds and the children), in its stream, parameter `8`
GL_TAIL = (77, 163, 243, 323)
GL_CURS = {'gkr_layer__L%d_L%d' % (p, o): dict(([(21, 8 * p)] if p else []) + [(GL_TAIL[p], 20 - 4 * o)])
           for p in range(4) for o in range(2)}
GL_STREAM = 8


def sub(k, c):
    """`CoreMode.glQC`: a read `c` words past one of its cursors, one of its stream's `[8]·[0, 8192)`."""
    import infer as I
    cs = GL_CURS.get(I.callee(k))
    if cs and len(c[0]) == 1 and c[0][0][1] == 1 and c[1] < cs.get(c[0][0][0], 0):
        return ('sub', c, ((((GL_STREAM, 1),), 0), 1, ('num', 0), ('num', 8192)))
    return None


def fam(k, r):
    """`CoreMode.glQC`: a read past its cursors (`sub`), under branch conditions."""
    if r[0] == 'under':
        return fam(k, r[2])
    return r[0] == 'sub' and sub(k, r[1]) == r


# The radix-four layers (`gkr_layer(layers, rounds, gkr_pts, x_m, x_j, start_g, g_bus_mu, tabs, stream, par, odd)`,
# layer `j = 4m + par` at `x_m = g^m`, `x_j = g^j`). Its record `layers·x_j^20·start_g^10`, the next one `20` words on;
# its point in row `j + 1` of `gkr_pts` (`gkr_pts·x_j^40·g^40`), its cells `[0, 2 par)`, then `8` a step of the loop,
# `m` steps, then the last `2 - odd`; it writes row `j + 2` alike, from `2 par + 2`.
REC, ROW0 = 10, 40


def _layer(p, o):
    rec = [(2, 1), (6, 20), (7, 10)]
    row = [(4, 1), (6, 40)]
    tail = [(4, 1), (5, 8), (6, 40)]
    return sig(
        range(11), None, [],
        pre=[cell(k, rec) for k in range(REC)] + [cell(ROW0 + c, row) for c in range(2 * p)] +
        [cell(ROW0 + 2 * p + q, tail) for q in range(2 - o)],
        preR=[run(cell(ROW0, row), num(0), ex(5), 8, 2 * p + q) for q in range(8)] + [stream(10)],
        post=[cell(2 * REC + k, rec) for k in range(REC)] + [cell(2 * ROW0 + c, row) for c in range(2 * p + 2)] +
        [cell(2 * ROW0 + 2 * p + 2 + q, tail) for q in range(2)],
        postR=[run(cell(2 * ROW0, row), num(0), ex(5), 8, 2 * p + 2 + q) for q in range(8)])


# `gkr_layer`'s loop (`y, x_m, head, qrow, nqrow, tabs`): `8` rounds from the record `head·y` (fields `862` apart, its
# cursor at `4310`), the point `qrow·y^8`, the record `head·y·g` and the cells `nqrow·y^8·g^q` written; the stream is its
# caller's cell `10` (`CoreMode.stLoops`).
def _layer_loop():
    rd = [(2, 1), (4, 1)]
    return sig(
        range(8), 8, [],
        pre=[cell(862 * f, rd) for f in range(7)],
        preR=[run(cell(0, [(5, 1)]), ex(2), ex(3), 8, q) for q in range(8)] +
        ['⟨⟨0, 0, [((.hp 1 10), 1)]⟩, (.num 0), (.num 8192), 1, 0⟩'],
        term=['(%s, %s)' % (ex(2), ex(3))],
        postL=[run(cell(0, [(4, 1)]), ex(2), ex(3), 1, 862 * f + 1) for f in range(7)] +
        [run(cell(0, [(6, 1)]), ex(2), ex(3), 8, q) for q in range(8)])



CONTRACTS = {}
for _o in range(2):
    for _p in range(4):
        CONTRACTS['gkr_layer__L%d_L%d' % (_p, _o)] = _layer(_p, _o)
        CONTRACTS['gkr_layer__L%d_L%d_loop0' % (_p, _o)] = _layer_loop()

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fn/gkr_layer/*.lean',
]
