"""Residual rules of the core inference (`infer.py`): the bytecode walk's `rules_fix.py` and `rules_da.py` on core
names. Each hook returns a witness whose residuals (`P.addres`) are closed statements on core names, or `None`."""


def read(P, st, c, site):
    return None


def run(P, st, r, site, conds):
    return None


def term(P, st, a, b, cond):
    return None
