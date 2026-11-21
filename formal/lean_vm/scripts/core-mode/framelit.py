"""The `frame_fn%` commands of the frame walks' modules (`CoreMode/Pack/*/Frame*.lean`, `CoreMode/FrameLit.lean`),
read back: each one's arguments (`envC`'s callees among them), for the generators that read those modules."""
import re

START = re.compile(r'^frame_fn% ', re.M)
KEYS = ('sigs', 'env', 'fpOne', 'scaled', 'nzr', 'tidx', 'arms', 'calls', 'fnz', 'main')
FLAGS = ('fpOne', 'main')


def _term(s, i):
    """The balanced term of `s` at `i` (a bracketed one, or up to the next space): (term, end)."""
    if s[i] in '([{⟨':
        d = 0
        for j in range(i, len(s)):
            if s[j] in '([{⟨': d += 1
            elif s[j] in ')]}⟩':
                d -= 1
                if d == 0: return s[i:j + 1], j + 1
        raise ValueError('unbalanced: %s' % s[i:i + 80])
    j = i
    while j < len(s) and not s[j].isspace(): j += 1
    return s[i:j], j


def _idents(lst):
    return re.findall(r'«([^»]+)»', lst)


def parse(text):
    """Each `frame_fn%` of a module's text: {name: its arguments}, `callees`/`sigs` as names, the other clauses as
    their terms, `n` its length."""
    out = {}
    for m in START.finditer(text):
        end = m.end()
        while True:
            nl = text.find('\n', end)
            if nl < 0 or not text.startswith('    ', nl + 1): break
            end = nl + 1
        s = ' '.join(text[m.end():nl if nl >= 0 else len(text)].split())
        name, i = _term(s, 0)
        n, i = _term(s, i + 1)
        cs, i = _term(s, i + 1)
        d = dict(name=name.strip('«»'), n=int(n), callees=_idents(cs))
        while i < len(s):
            i += 1
            k, i = _term(s, i)
            assert k in KEYS, (k, s)
            if k in FLAGS:
                d[k] = True; continue
            v, i = _term(s, i + 1)
            d[k] = _idents(v) if k == 'sigs' else v
        out[d['name']] = d
    return out

