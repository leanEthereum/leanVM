"""`shared_selector_tables`' rules: its `len = q^4·r` split from hinted bits (`CoreMode.splitsC`)."""

from fnrules import lean_def


def _tup(x):
    return tuple(_tup(e) for e in x) if isinstance(x, (list, tuple)) else x


# as its Lean data says (`CoreMode.spSst`)
SPLITS = {'shared_selector_tables': _tup(lean_def('shared_selector_tables', 'Fam', 'spSst'))}


# ---- its counts (`scripts/count`)

# counted by its tree's shape in the `W` family (`verify_tables`')
COUNT_SHAPE = {'shared_selector_tables': 'W'}


def count_walk(C, k, n):
    """Its instructions: its body, its loop `15` times."""
    import vscount
    if n != vscount.L('shared_selector_tables'):
        return None
    lp = vscount.L('shared_selector_tables_loop0')

    def call_if(f):
        assert f == lp, f
        return 15 * C.loop(k, f)
    return C.walk(k, n, call_if)

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
