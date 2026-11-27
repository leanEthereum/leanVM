"""Packed numbers for the Lean checkers of `LeanVM/Guest/Packed/`, for the generators that write their certificates.

- `nat_hex(n)`: the Lean literal `nat_hex% "…"` of `n` (`Packed/NatLit.lean`), read in time quasi-linear in its length.
- `pack(values, w)`: the vector whose lane `i` of `w` bits is `values[i]` (`Packed.pack`).
- `chunks(values, w, c)`: the Lean list of the chunks of `c` lanes of a long vector (`Packed.Chunks`).
- `pmap(entries, w)`: the packed map of a dict `key -> value`, slots of `w` bits, salt `0` (`Packed.PMap`).
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


def chunks(values, w, c):
    """The Lean list of the chunks of `values`, `c` lanes of `w` bits each."""
    values = list(values)
    return '[' + ', '.join(nat_hex(pack(values[i:i + c], w)) for i in range(0, len(values), c)) + ']'


def pmap(entries, w):
    """The packed map of `entries`: key `k`'s slot is lane `k` above the 64-bit salt, `v + 1` for the value `v`."""
    n = max(entries, default=-1) + 1
    return pack([entries[k] + 1 if k in entries else 0 for k in range(n)], w) << 64
