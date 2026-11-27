"""Packed numbers for the Lean checkers of `LeanVM/Guest/Packed/`, for the generators that write their certificates.

- `nat_hex(n)`: the Lean literal `nat_hex% "…"` of `n` (`Packed/NatLit.lean`), read in time quasi-linear in its length.
- `pack(values, w)`: the vector whose lane `i` of `w` bits is `values[i]` (`Packed.pack`).
"""


def nat_hex(n):
    """The Lean literal of `n`."""
    return f'nat_hex% "{n:x}"'


def pack(values, w):
    """The vector of lanes `values`, each below `2^w`, joined by halves."""
    values = list(values)
    assert all(0 <= v < 1 << w for v in values)

    def go(lo, hi):
        if hi - lo <= 64:
            n = 0
            for v in reversed(values[lo:hi]):
                n = n << w | v
            return n
        mid = (lo + hi) // 2
        return go(lo, mid) | go(mid, hi) << (w * (mid - lo))

    return go(0, len(values))
