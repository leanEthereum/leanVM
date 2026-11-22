"""`gkr_layers`' rules: its specializations `gkr_layers__L{odd}` and their loops."""
from sigseed import sig, cell, num, ex, run, stream
import fnrules
from fnrules import lean_def


# a loop's runs where it is not entered (`join`), its own guarantees over its dispatch's selector (`armsub`)
FEATURES = {'gkr_layers__L%d' % o: [{'join', 'armsub'}] for o in range(2)}

# `n_four`'s and `rem_g`'s exponents below `4` (`Res.expFacts`, `EndExec.GlsQ`), as its Lean data says
EXP_FACTS = lean_def('gkr_layers', 'Data', 'expFacts')

REC, ROW0 = 10, 40


# `gkr_layers(layers, rounds, gkr_pts, n_four, rem_g, start_g, g_bus_mu, tabs, stream, odd)`: layers `0 .. 4n + r`
# (`n_four = g^n`, `rem_g = g^r`): from the record of layer `0` and row `1`, to the record of layer `L = 4n + r` and
# row `L + 1` (its cells `[0, 2r)`, `8` a step for `n` steps, the last two), over the selector `rem_g` (`abx`).
def _layers(o):
    row = [(4, 1), (5, 160), (6, 40)]
    return sig(
        range(11), None, [11],
        pre=[cell(k, [(2, 1), (7, 10)]) for k in range(REC)] + [cell(ROW0 + q, [(4, 1)]) for q in range(2)],
        preR=[stream(10)],
        post=[cell(k, [(2, 1), (5, 80), (6, 20), (7, 10)]) for k in range(REC)] +
        [cell(ROW0 + q, [(4, 1), (5, 168), (6, 42)]) for q in range(2)],
        postR=[run(cell(ROW0, row), num(0), ex(6), 2, d) for d in range(2)] +
        [run(cell(ROW0, [(4, 1), (5, 160), (6, 42)]), num(0), ex(5), 8, q) for q in range(8)])


# `gkr_layers`' loop (`x_m, n_four, layers, rounds, gkr_pts, start_g, g_bus_mu, tabs, stream`): layers `4m .. 4m + 3`.
def _layers_loop(o):
    return sig(
        range(11), 11, [],
        pre=[cell(k, [(2, 80), (4, 1), (7, 10)]) for k in range(REC)] +
        [cell(ROW0 + q, [(2, 168), (6, 1)]) for q in range(2 - o)],
        preR=[run(cell(ROW0, [(2, 160), (6, 1)]), num(0), ex(2), 8, q) for q in range(8)] + [stream(10)],
        term=['(%s, %s)' % (ex(2), ex(3))],
        post=[cell(k, [(3, 80), (4, 1), (7, 10)]) for k in range(REC)] +
        [cell(ROW0 + q, [(3, 168), (6, 1)]) for q in range(2)],
        postR=[run(cell(ROW0, [(3, 160), (6, 1)]), num(0), ex(3), 8, q) for q in range(8)],
        postL=[run(cell(0, [(4, 1), (7, 10)]), ex(2), ex(3), 80, 20 * t + k) for t in range(1, 5)
               for k in range(REC)] +
        [run(cell(0, [(6, 1)]), ex(2), ex(3), 168, 208 + q) for q in range(2)])



CONTRACTS = {}
for _o in range(2):
    CONTRACTS['gkr_layers__L%d' % _o] = _layers(_o)
    CONTRACTS['gkr_layers__L%d_loop0' % _o] = _layers_loop(_o)

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
