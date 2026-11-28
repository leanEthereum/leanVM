"""Contract literals for the contracts given by hand (`sigc.py`), in each function's rule file (`fn/<f>.py`, `CONTRACTS`):
by stable name, the literal fields of `Fn.«k».csig : Mode.Sig` past its entry, as
`CoreMode/Sig/<pack>.lean` writes them (entry cells, self cell, pre, preR, term, return cells, post, postR, postL, preP,
postP, postLP, retV, postT, postC). The route's checks hold each to the function's heap signature (`CoreMode.ownOk`,
`fitB`) like any other.

A function's parameter `i` is its frame cell `2 + i`; a heap cell `⟨0, k, [(cell, e), ..]⟩` is `Π [cell]^e · g^k`, a run
`⟨cell, lo, hi, S, d⟩` its cells `·g^(S·i + d)`, `lo <= i < hi`."""


def cell(k, bs):
    return '⟨0, %d, [%s]⟩' % (k, ', '.join('((.fr %d), %d)' % b for b in bs))


def num(n):
    return '(.num %d)' % n


def ex(o, c=0):
    return '(.ex (.fr %d) %d)' % (o, c)


def run(c, lo, hi, S, d):
    return '⟨%s, %s, %s, %d, %d⟩' % (c, lo, hi, S, d)


def lst(xs):
    return '[%s]' % ', '.join(xs)


def sig(entry, self_, ret, pre=(), preR=(), term=(), post=(), postR=(), postL=(), preP=(), postP=(), postLP=(),
        retV=()):
    return ', '.join([lst(map(str, entry)), 'none' if self_ is None else '(some %d)' % self_, lst(pre), lst(preR),
                      lst(term), lst(map(str, ret)), lst(post), lst(postR), lst(postL), lst(preP), lst(postP),
                      lst(postLP), lst(retV)] + ['[]'] * 2)


def ptrs(r, cells):
    """A `preP`/`postP` entry: each word of the run `r` a pointer whose cells `cells` past it are written."""
    return '(%s, [%s])' % (r, ', '.join(map(str, cells)))


def lt_fact(lo, hi):
    """A termination fact `e(lo) < e(hi)`."""
    return '(%s, %s)' % (lo, hi)


# the proof stream, a parameter's run `[0, 8192)`
def stream(o):
    return run(cell(0, [(o, 1)]), num(0), num(8192), 1, 0)
