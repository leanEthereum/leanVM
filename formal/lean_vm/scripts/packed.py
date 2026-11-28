"""Packed numbers for the Lean checkers of `LeanVM/Guest/Packed/`, for the generators that write their certificates.

- `nat_hex(n)`: the Lean literal `nat_hex% "…"` of `n` (`Packed/NatLit.lean`), read in time quasi-linear in its length.
- `bits(xs)`: the literal of the bitset of `xs`.
- `enc(s)`: a name's code (`encS`, `Guest/NameIx.lean`).
- `ntree(items, val)`, `ntab(entries, val)`: the literal of an `NTree` search tree, of an `NTab` name table
  (`CoreMode/Fam/TabDefs.lean`).
- `pack(values, w)`: the vector whose lane `i` of `w` bits is `values[i]` (`Packed.pack`).
- `chunks(values, w, c)`: the Lean list of the chunks of `c` lanes of a long vector (`Packed.Chunks`).
- `pmap(entries, w)`: the packed map of a dict `key -> value`, slots of `w` bits, salt `0` (`Packed.PMap`).
- `ptree(entries, w, d)`: the Lean term of the `Packed.PTree` of depth `d` of a dict, its leaves `pmap`s.
"""


def nat_hex(n):
    """The Lean literal of `n`."""
    return f'nat_hex% "{n:x}"'


def bits(xs):
    """The literal of the bitset with bit `x` set for each `x` of `xs`."""
    return nat_hex(sum(1 << x for x in set(xs)))


def enc(s):
    """`encS`: the name's UTF-8 bytes as digits in base `2^9`, each shifted by one, the first the lowest."""
    n = 0
    for c in reversed(s.encode('utf-8')):
        n = n * 512 + c + 1
    return n


def ntree(items, val, ind='  '):
    """A balanced `NTree` literal over sorted `(key, value)` items."""
    if not items:
        return '.leaf'
    m = len(items) // 2
    k, v = items[m]
    return '(.node %d %s\n%s%s\n%s%s)' % (k, val(v), ind, ntree(items[:m], val, ind + ' '), ind,
                                         ntree(items[m + 1:], val, ind + ' '))


def ntab(entries, val):
    """An `NTab` literal of `(name, payload)` entries: the payloads by the name's code."""
    by = {}
    for f, p in entries:
        ps = by.setdefault(enc(f), [])
        if p not in ps:
            ps.append(p)
    return ntree(sorted(by.items()), lambda ps: '[%s]' % ', '.join(map(val, ps)))


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


def ptree(entries, w, d):
    """The `PTree` of depth `d` of `entries`, as a Lean term: key `k` in leaf `k % 2^d` (its low bits, even to the
    left first), at `k >> d`."""
    def go(r, level):
        if level == d:
            m = pmap({k >> d: v for k, v in entries.items() if k % (1 << d) == r}, w)
            return f'(.leaf {nat_hex(m) if m else 0})'
        return f'(.node {go(r, level + 1)} {go(r | 1 << level, level + 1)})'
    return go(0, 0)
