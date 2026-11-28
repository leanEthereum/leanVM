"""`link_terminal`'s contracts (`sigc.py`): `link_terminal__L{w}(r, sent, coef, shifts, cert_w, nu, rest, claim)` reads
`r[g^k]`, `k < w`, the slices `sent[g^k]` its chunks name, `LINK_N_SENT <= k < SENT_END[w]`, `shifts[g^s]`,
`s < LINK_MAX_SHIFT`, and `nu[g^i]`, `i < CHUNK_D[w]`."""
from fnrules import guest_const
from sigseed import sig, cell, num, run

SENT = guest_const('LINK_N_SENT')
SHIFTS = guest_const('LINK_MAX_SHIFT')
# the end of the slices chunk `i` reads at stride `2^CHUNK_WIDTH`, and `CHUNK_D[w]`, by `w`
SENT_END = {19: 136, 20: 144, 21: 140, 22: 144, 23: 144, 24: 144}
CHUNKS = {19: 6, 20: 6, 21: 7, 22: 7, 23: 8, 24: 9}


def par(i, lo, hi):
    """Parameter `i`'s cells `[p]·g^k`, `lo <= k < hi`."""
    return run(cell(0, [(2 + i, 1)]), num(lo), num(hi), 1, 0)


def contract(w):
    return sig(range(10), None, [10], preR=[par(0, 0, w), par(1, SENT, SENT_END[w]), par(3, 0, SHIFTS),
                                            par(5, 0, CHUNKS[w])], postR=[])


CONTRACTS = {'link_terminal__L%d' % w: contract(w) for w in SENT_END}

OWN = []
