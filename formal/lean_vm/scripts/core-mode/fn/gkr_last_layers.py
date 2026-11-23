"""`gkr_last_layers`' contracts (`sigc.py`)."""
from sigseed import sig, cell, num, ex, run, stream

REC, ROW0 = 10, 40


# `gkr_last_layers(layers, rounds, gkr_pts, n_four, m4, start_g, g_bus_mu, tabs, stream, r, odd)`: layers
# `4n .. 4n + r - 1` (`m4 = g^(4n)`), from the record of layer `4n` and its row to those of layer `4n + r`.
def _last(r, o):
    rec = [(2, 1), (6, 20), (7, 10)]
    if r == 0:
        # no layer: the record it is given is the last
        return sig(range(11), None, [11], pre=[cell(k, rec) for k in range(REC)],
                    post=[cell(k, rec) for k in range(REC)])
    row = [(4, 1), (6, 40)]
    tail = [(4, 1), (5, 8), (6, 40)]
    return sig(
        range(11), None, [11],
        pre=[cell(k, rec) for k in range(REC)] + [cell(ROW0 + q, tail) for q in range(2 - o)],
        preR=[run(cell(ROW0, row), num(0), ex(5), 8, q) for q in range(8)] + [stream(10)],
        post=[cell(20 * t + k, rec) for t in range(1, r + 1) for k in range(REC)] +
        [cell(ROW0 * (r + 1) + c, row) for c in range(2 * r)] +
        [cell(ROW0 * (t + 1) + 2 * t + q, tail) for t in range(1, r + 1) for q in range(2)],
        postR=[run(cell(ROW0 * (r + 1), row), num(0), ex(5), 8, 2 * r + q) for q in range(8)])



CONTRACTS = {'gkr_last_layers__L%d_L%d' % (_p, _o): _last(_p, _o) for _o in range(2) for _p in range(4)}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
