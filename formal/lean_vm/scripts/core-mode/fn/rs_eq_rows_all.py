"""`rs_eq_rows_all`'s contracts (`sigc.py`): `rs_eq_rows_all__L{n}(row, zs, ps)` reads `zs[g^i]`, `ps[g^i]`, `i < n`,
and row `0`, `row[g^k]`, `k < BASE_FIELD_BITS`, and leaves rows `0..n` written, `row[g^k]`, `k < BASE_FIELD_BITS·(n + 1)`."""
from fnrules import guest_const
from sigseed import sig, cell, num, run

B = guest_const('BASE_FIELD_BITS')


def par(i, n):
    """Parameter `i`'s cells `[p]·g^k`, `k < n`."""
    return run(cell(0, [(2 + i, 1)]), num(0), num(n), 1, 0)


def contract(n):
    # its reads as cells, as `rs_eq_rows`' (a caller's rows and coordinates from a loop's strided runs, one cell each)
    pre = [cell(k, [(2, 1)]) for k in range(B)] + [cell(i, [(o, 1)]) for o in (3, 4) for i in range(n)]
    return sig(range(5), None, [5], pre=pre, postR=[par(0, B * (n + 1))])


CONTRACTS = {'rs_eq_rows_all__L%d' % n: contract(n) for n in range(0, 64)}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
