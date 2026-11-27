"""Packed numbers for the Lean checkers of `LeanVM/Guest/Packed/`, for the generators that write their certificates.

- `nat_hex(n)`: the Lean literal `nat_hex% "…"` of `n` (`Packed/NatLit.lean`), read in time quasi-linear in its length.
"""


def nat_hex(n):
    """The Lean literal of `n`."""
    return f'nat_hex% "{n:x}"'
