"""Lean text of `infer.py`'s own witnesses (the printers `emitc.py` had before it solved witnesses in `heapc.py`'s pass):
`loopc.py`'s certificates."""


class Unsupported(Exception):
    pass


def lcell(c):
    if any(e < 0 for _, e in c[0]) or c[1] < 0:
        raise Unsupported(('cell', c))
    return '⟨[' + ', '.join(f'({b}, {e})' for b, e in c[0]) + f'], {c[1]}⟩'


def lidx(i):
    """A signature run's bound: `.num n` or `.val slot`."""
    if not i[0]:
        if i[1] >= 2 ** 62 or i[1] < 0:
            raise Unsupported(('idx', i))
        return f'(.num {i[1]})'
    if len(i[0]) == 1 and i[0][0][1] == 1 and i[1] == 0:
        return f'(.val {i[0][0][0]})'
    raise Unsupported(('idx', i))


def lrun(r):
    Q, S, lo, hi = r
    return f'⟨{lcell(Q)}, {S}, {lidx(lo)}, {lidx(hi)}⟩'


def lres(r):
    """A residual: `.lt a b` over value numbers."""
    if r[0] != 'lt' or len(r) < 5 or r[4] is None:
        raise Unsupported(('res', r[:4]))
    (ka, a), (kb, b) = r[4]
    return f'.lt (.{ka} {a}) (.{kb} {b})'


def lwit(P, w):
    k = w[0]
    if k == 'ev':
        return f'.ev {w[1]}'
    if k == 'pre':
        return f'.pre {w[1]}'
    if k == 'run':
        rw = w[1]
        r = rw[1] if isinstance(rw, tuple) and rw[0] == 'preR' else (len(P.sig.preR) + rw if isinstance(rw, int) else None)
        if r is None:
            raise Unsupported(('wit', w))
        return f'.run {r} [{", ".join(str(P.wren[i]) for i in w[2])}]'
    raise Unsupported(('wit', w[0]))


def wrap(items, ind='    ', width=110):
    lines, cur = [], ''
    for it in items:
        if cur and len(ind) + len(cur) + len(it) + 2 > width:
            lines.append(cur + ',')
            cur = ''
        cur = f'{cur}, {it}' if cur else it
    if cur:
        lines.append(cur)
    return ('\n' + ind).join(lines)
