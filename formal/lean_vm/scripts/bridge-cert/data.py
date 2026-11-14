"""The guest's generated data as the bridge's certificates read it: each compiled function's core body
(`Pack/*/Core*.lean`), code and certificate cells (`Pack/*/Bundle.lean`, `Cells*.lean`) and plumbing
(`Bundle.lean`'s `plumb`), and its advice (`Data/AdviceHints.lean`), parsed from the Lean text."""
import re, glob, os
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN_VM = os.path.normpath(os.path.join(HERE, '..', '..'))
ROOT = os.path.join(LEAN_VM, 'LeanVM', 'Guest')

TOK = re.compile(r'\s*(?:("(?:[^"\\]|\\.)*")|(::|\+\+|[()\[\],⟨⟩])|([A-Za-z_.][A-Za-z0-9_.!?\']*)|(0x[0-9a-fA-F]+|\d+))')


def tokens(s):
    out, i, n = [], 0, len(s)
    while i < n:
        m = TOK.match(s, i)
        if not m:
            if s[i:].strip() == '':
                break
            raise ValueError(s[i:i + 60])
        i = m.end()
        if m.group(1) is not None:
            out.append(('s', m.group(1)[1:-1]))
        elif m.group(2) is not None:
            out.append(('p', m.group(2)))
        elif m.group(3) is not None:
            out.append(('i', m.group(3)))
        elif m.group(4) is not None:
            out.append(('n', int(m.group(4), 0)))
    return out


class P:
    """A term: `expr := cons ('++' cons)*`, `cons := app ('::' cons)?`, `app := atom+`."""

    def __init__(self, toks):
        self.t, self.k = toks, 0

    def peek(self):
        return self.t[self.k] if self.k < len(self.t) else ('e', None)

    def eat(self, v):
        assert self.peek() == ('p', v), (self.peek(), v, self.t[max(0, self.k - 5):self.k + 5])
        self.k += 1

    def expr(self):
        xs = [self.cons()]
        while self.peek() == ('p', '++'):
            self.k += 1
            xs.append(self.cons())
        return xs[0] if len(xs) == 1 else ('++', xs)

    def cons(self):
        hs = [self.app()]
        while self.peek() == ('p', '::'):
            self.k += 1
            hs.append(self.app())
        if len(hs) == 1:
            return hs[0]
        if hs[-1] == ('list', []):
            return ('list', hs[:-1])
        return ('++', [('list', hs[:-1]), hs[-1]])

    def app(self):
        xs = [self.atom()]
        while True:
            k, v = self.peek()
            if k in ('s', 'i', 'n') or (k == 'p' and v in ('(', '[', '⟨')):
                xs.append(self.atom())
            else:
                break
        return xs[0] if len(xs) == 1 else ('app', xs[0], xs[1:])

    def seq(self, close):
        xs = []
        if self.peek() == ('p', close):
            self.k += 1
            return xs
        while True:
            xs.append(self.expr())
            if self.peek() == ('p', ','):
                self.k += 1
                continue
            self.eat(close)
            return xs

    def atom(self):
        k, v = self.peek()
        self.k += 1
        if k == 'p' and v == '(':
            xs = self.seq(')')
            return xs[0] if len(xs) == 1 else ('tuple', xs)
        if k == 'p' and v == '[':
            return ('list', self.seq(']'))
        if k == 'p' and v == '⟨':
            return ('tuple', self.seq('⟩'))
        if k == 's':
            return ('str', v)
        if k == 'n':
            return v
        if k == 'i':
            return ('id', v)
        raise ValueError((k, v))


def parse(s):
    p = P(tokens(s))
    e = p.expr()
    assert p.k == len(p.t), p.t[p.k:p.k + 10]
    return e


def as_list(e, env):
    """A list term, its named parts resolved in `env`."""
    if isinstance(e, tuple) and e[0] == 'list':
        return e[1]
    if isinstance(e, tuple) and e[0] == '++':
        out = []
        for x in e[1]:
            out += as_list(x, env)
        return out
    if isinstance(e, tuple) and e[0] == 'id':
        return as_list(env(e[1]), env)
    raise ValueError(e)


def head(e):
    """The constructor of an application or a bare constructor, and its arguments."""
    if isinstance(e, tuple) and e[0] == 'app':
        return e[1][1], e[2]
    if isinstance(e, tuple) and e[0] == 'id':
        return e[1], []
    raise ValueError(e)


def val(e):
    """A value's index: `.n i` or `⟨path, tag, idx⟩`."""
    h, a = head(e) if not (isinstance(e, tuple) and e[0] == 'tuple') else ('tuple', e[1])
    if h == '.n':
        return a[0]
    if h == 'tuple':
        return a[2]
    raise ValueError(e)


def vals(e, env):
    return [val(x) for x in as_list(e, env)]


def dest(e, env):
    h, a = head(e)
    if h == '.stack':
        return ('stack', vals(a[0], env))
    if h == '.heap':
        return ('heap', val(a[0]), a[1], a[2])
    raise ValueError(e)


def core_hint(e, env):
    h, a = head(e)
    if h == '.witness':
        return ('witness', a[0][1], dest(a[1], env))
    if h == '.bits':
        return ('bits', val(a[0]), a[1], a[2], dest(a[3], env))
    if h == '.bitsExp':
        return ('bitsExp', val(a[0]), a[1], dest(a[2], env))
    if h == '.digitsExp':
        sc = a[5]
        if sc == ('id', 'none'):
            sc = None
        else:
            sh, sa = head(sc)
            assert sh == 'some'
            sc = val(sa[0])
        return ('digitsExp', val(a[0]), a[1], a[2], a[3], a[4], sc, dest(a[6], env))
    if h == '.windowsExp':
        return ('windowsExp', val(a[0]), a[1], a[2], a[3], dest(a[4], env))
    if h == '.limbs':
        return ('limbs', val(a[0]), vals(a[1], env))
    if h == '.log2Ceil':
        return ('log2Ceil', dest(a[0], env), a[1], a[2], val(a[3]))
    if h == '.inverse':
        return ('inverse', val(a[0]), val(a[1]))
    if h == '.alloc':
        return ('alloc', val(a[0]), a[1])
    if h == '.allocDyn':
        return ('allocDyn', val(a[0]), val(a[1]))
    raise ValueError(h)


def stmt(e, env):
    """A statement: `('atom', kind, hint)`, `('ite', zero, nonzero)`, `('match', arms)`, or
    `('ctl', kind)` for calls and returns."""
    h, a = head(e)
    if h == '.atom':
        ah, aa = head(a[0])
        if ah == '.hint':
            return ('atom', 'hint', core_hint(aa[0], env))
        return ('atom', ah[1:], None)
    if h == '.ite':
        return ('ite', block(a[1], env), block(a[2], env))
    if h == '.match_':
        return ('match', [block(x, env) for x in as_list(a[1], env)])
    return ('ctl', h[1:])


def block(e, env):
    return [stmt(x, env) for x in as_list(e, env)]


DEF = re.compile(r'^(?:noncomputable )?def (\w+) : ([^\n]*?) :=', re.M)


def defs(text):
    """The definitions of a namespace's text, by name: their terms' text."""
    ms = list(DEF.finditer(text))
    out = {}
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        body = text[m.end():end]
        body = re.split(r'\n/--|\nend\b|\nnamespace |\n@\[|\nopen ', body)[0]
        out[m.group(1)] = body
    return out


def core_texts():
    """Each function's core text, by stable name."""
    out = {}
    for p in sorted(glob.glob(ROOT + '/Pack/P[0-9]*/Core.lean')):
        t = open(p, encoding='utf-8').read()
        for m in re.finditer(r'^namespace LeanVM\.Guest\.Fn\.«([^»]+)»\n(.*?)^end LeanVM\.Guest\.Fn\.«\1»$', t,
                             re.M | re.S):
            out[m.group(1)] = m.group(2)
    for d in sorted(glob.glob(ROOT + '/Pack/*/')):
        key = os.path.basename(os.path.dirname(d))
        if re.fullmatch(r'P\d+', key):
            continue
        files = sorted(glob.glob(d + 'Core*.lean'), key=lambda p: int(os.path.basename(p)[4:-5] or 0))
        if files:
            out[key] = ''.join(open(p, encoding='utf-8').read() for p in files)
    return out


def body_of(text):
    """A core function's body, parsed."""
    i = text.index('namespace core')
    ds = defs(text[i:])
    cache = {}

    def env(n):
        if n not in cache:
            cache[n] = parse(ds[n])
        return cache[n]
    return block(env('body'), env)


def bundles():
    """Each compiled function's code, certificate cells and plumbing cells, by stable name."""
    out = {}
    cells_texts = {}
    for p in glob.glob(ROOT + '/Pack/*/Cells*.lean'):
        key = os.path.basename(os.path.dirname(p))
        cells_texts.setdefault(key, []).append(open(p, encoding='utf-8').read())
    for b in sorted(glob.glob(ROOT + '/Pack/*/Bundle.lean')):
        pack = b.split('/')[-2]
        t = open(b, encoding='utf-8').read()
        for blk in t.split('\nnamespace LeanVM.Guest.Fn.')[1:]:
            key = blk.split('\n', 1)[0].strip().strip('«»')
            text = blk + ''.join(cells_texts.get(key, []))
            ds = defs(text)
            cache = {}

            def env(n, ds=ds, cache=cache):
                if n not in cache:
                    cache[n] = parse(ds[n])
                return cache[n]
            cm = re.search(r'def code : CompiledFunction :=\s*⟨"([^"]*)", (\d+), (\d+), \[([^\]]*)\]⟩', blk)
            entry, cnt = int(cm.group(2)), int(cm.group(3))
            code = []
            for c in cm.group(4).split(','):
                c = c.strip()
                if c:
                    code += [head(x)[0] for x in as_list(env(c), env)]
            assert len(code) == cnt, (key, len(code), cnt)
            cert = re.search(r'noncomputable def cert : Check\.Cert where\n(.*?)\n(?:/--|\Z)', blk, re.S).group(1)
            cl = re.search(r'^  cells := (.*)$', cert, re.M).group(1)
            locs = []
            for w in as_list(parse(cl), env):
                locs += as_list(w, env)
            pl = re.search(r'noncomputable def plumb : B2C\.Plumb where\n(.*?)\n(?:/--|\Z)', blk, re.S)
            plumb = set()
            if pl:
                pt = pl.group(1)
                st = re.search(r'^  stat := (.*)$', pt, re.M)
                if st:
                    plumb |= set(int(x) for x in re.findall(r'\((\d+), \(\.', st.group(1)))
                si = re.search(r'^  sites := (.*)$', pt, re.M)
                if si:
                    for m in re.finditer(r'⟨\[[^\]]*\], \[[^\]]*\], (\d+), (\d+), (\d+)⟩', si.group(1)):
                        plumb |= {int(m.group(1)), int(m.group(3))}
                ar = re.search(r'^  arms := (.*)$', pt, re.M)
                if ar:
                    plumb |= set(int(m.group(2)) for m in re.finditer(r'\((\d+), (\d+), (\d+)\)', ar.group(1)))
            out[key] = dict(key=key, pack=pack, entry=entry, count=cnt, code=code, locs=locs, plumb=plumb)
    return out


def advice():
    """The advice by function: its index in `Data.adviceFns`, keyed by entry pc, with its hints by pc."""
    t = open(ROOT + '/Data/AdviceHints.lean', encoding='utf-8').read()
    ds = defs(t)

    def env(n):
        return parse(ds[n])

    def hl(e):
        if isinstance(e, tuple) and e[0] == 'app' and e[1] == ('id', 'List.flatten'):
            return [p for x in as_list(e[2][0], env) for p in hl(x)]
        return as_list(e, env)
    out = {}
    for n in ds:
        m = re.fullmatch(r'adviceFn(\d+)', n)
        if not m:
            continue
        entry, length, hs = parse(ds[n])[1]
        hints = []
        for p in hl(hs):
            pc, l = p[1]
            hints.append((pc, [isa_hint(h) for h in as_list(l, None)]))
        out[entry] = dict(j=int(m.group(1)), entry=entry, length=length, hints=hints)
    return out


def bdest(e):
    h, a = head(e)
    return (h[1:], a[0])


def isa_hint(e):
    h, a = head(e)
    h = h[1:]
    if h in ('witnessStack', 'witnessHeap', 'allocAdvice'):
        return (h,) + tuple(x[1] if isinstance(x, tuple) and x[0] == 'str' else x for x in a)
    if h in ('log2Ceil',):
        return (h, bdest(a[0])) + tuple(a[1:])
    if h in ('bitDecompose', 'bitDecomposeExp', 'windowsExp'):
        return (h, a[0], bdest(a[1])) + tuple(a[2:])
    if h == 'digitDecomposeExp':
        sc = a[6]
        sc = None if sc == ('id', 'none') else head(sc)[1][0]
        return (h, a[0], bdest(a[1]), a[2], a[3], a[4], a[5], sc)
    if h == 'allocArm':
        return (h, a[0], a[1], as_list(a[2], None))
    if h == 'allocFrames':
        return (h, a[0], a[1], a[2], None, a[4])
    return (h,) + tuple(a)
