"""The guest's generated data as the bridge's certificates read it: each compiled function's core body
(`Pack/*/Core*.lean`), code and certificate cells (`Pack/*/Bundle.lean`, `Cells*.lean`) and plumbing
(`Bundle.lean`'s `plumb`), and its advice (`Statement/Data/AdviceHints*.lean`), parsed from the Lean text."""
import re, glob, os, functools
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN_VM = os.path.normpath(os.path.join(HERE, '..', '..'))
ROOT = os.path.join(LEAN_VM, 'LeanVM', 'Guest')
# The statement's generated data, where `guest-export` writes the advice (`Statement/Data/AdviceHints*.lean`).
STATEMENT_DATA = os.path.join(LEAN_VM, '..', 'Statement', 'Data')


def _halt():
    """The halting pc, the program's last: `2^logSize - 1` (`LeanVM/Guest/Data/Functions.lean`)."""
    t = open(os.path.join(LEAN_VM, 'LeanVM', 'Guest', 'Data', 'Functions.lean'), encoding='utf-8').read()
    return 2 ** int(re.search(r'def logSize : ℕ := (\d+)', t).group(1)) - 1


HALT = _halt()


IMPORT = re.compile(r'^(?:public )?(?:meta )?import ', re.M)


def quiet(files):
    """`files` (path to text) with the linters off after each module's imports, unless it turns them off itself: they
    find nothing in a generated module, and each runs in the interpreter on every declaration."""
    def one(text):
        ms = list(IMPORT.finditer(text))
        if 'set_option linter.all false' in text or not ms:
            return text
        end = text.index('\n', ms[-1].start()) + 1
        return text[:end] + '\nset_option linter.all false\n' + text[end:]
    return {p: one(t) for p, t in files.items()}


def advice_text():
    """The text of the advice's modules, `AdviceHints` and its chunks, one after another."""
    names = sorted(n for n in os.listdir(STATEMENT_DATA) if n.startswith('AdviceHints') and n.endswith('.lean'))
    return ''.join(open(os.path.join(STATEMENT_DATA, n), encoding='utf-8').read() for n in names)

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


# ---- the core IR, parsed once: `core_fn`, `core_body`

def _bool(e):
    return e == ('id', 'true')


def _word(e):
    h, a = head(e)
    assert h == 'word', e
    return (a[0], a[1])


def core_atom(e, env):
    """An atom as `Core.Atom`, values by number: `('const', x, word)`, `('add'|'mul', x, a, b)`, `('copy', x, a)`,
    `('load', p, o, w)`, `('assertEq', a, b)`, `('assertNe', a, b, c)`, `('rangeCheck', ...)`, `('assertInK', a, b)`,
    `('keccak', ins, outs, b, b)`, `('frameAddr', x, xs)`, `('hint', core_hint)`, `('touch', p, o)`."""
    h, a = head(e)
    k = h[1:]
    if k == 'const':
        return ('const', val(a[0]), _word(a[1]))
    if k in ('add', 'mul'):
        return (k, val(a[0]), val(a[1]), val(a[2]))
    if k == 'copy':
        return ('copy', val(a[0]), val(a[1]))
    if k == 'load':
        return ('load', val(a[0]), val(a[1]), a[2])
    if k == 'assertEq':
        return ('assertEq', val(a[0]), val(a[1]))
    if k == 'assertNe':
        return ('assertNe', val(a[0]), val(a[1]), val(a[2]))
    if k == 'rangeCheck':
        return ('rangeCheck',) + tuple(val(x) for x in a[:5])
    if k == 'assertInK':
        return ('assertInK', val(a[0]), val(a[1]))
    if k == 'keccak':
        return ('keccak', vals(a[0], env), vals(a[1], env), _bool(a[2]), _bool(a[3]))
    if k == 'frameAddr':
        return ('frameAddr', val(a[0]), vals(a[1], env))
    if k == 'hint':
        return ('hint', core_hint(a[0], env))
    if k == 'touch':
        return ('touch', val(a[0]), val(a[1]))
    raise ValueError(k)


def core_stmt(e, env):
    """A statement: `('a', atom)`, `('ite', c, zero, nonzero)`, `('match', x, arms)`, `('call', f, args, rets)`,
    `('callIf', c, f, args)`, `('dispatch', x, fs, args, rets)`, `('ret', vs)`."""
    h, a = head(e)
    if h == '.atom':
        return ('a', core_atom(a[0], env))
    if h == '.ite':
        return ('ite', val(a[0]), core_block(a[1], env), core_block(a[2], env))
    if h == '.match_':
        return ('match', val(a[0]), [core_block(x, env) for x in as_list(a[1], env)])
    if h == '.call':
        return ('call', a[0][1], vals(a[1], env), vals(a[2], env))
    if h == '.callIf':
        return ('callIf', val(a[0]), a[1][1], vals(a[2], env))
    if h == '.dispatch':
        return ('dispatch', val(a[0]), [x[1] for x in as_list(a[1], env)], vals(a[2], env), vals(a[3], env))
    if h == '.ret':
        return ('ret', vals(a[0], env))
    raise ValueError(h)


def core_block(e, env):
    return [core_stmt(x, env) for x in as_list(e, env)]


def core_fn(text):
    """A function's core text (`core_texts`) parsed: its parameters, body and compiled name."""
    i = text.index('namespace core')
    ds = defs(text[i:])
    cache = {}

    def env(n):
        if n not in cache:
            cache[n] = parse(ds[n])
        return cache[n]
    params = vals(parse(re.search(r'params := (.*)', text).group(1)), env)
    name = re.search(r'name := "([^"]*)"', text).group(1)
    return params, core_block(env('body'), env), name


def core_body(text):
    """A function's body, parsed (`core_stmt`)."""
    return core_fn(text)[1]


def outline(body):
    """The body as the hint bridge's checks read it: `('atom', kind, hint)`, `('ite', zero, nonzero)`,
    `('match', arms)`, `('ctl', kind)` for calls and returns."""
    out = []
    for s in body:
        if s[0] == 'a':
            out.append(('atom', s[1][0], s[1][1] if s[1][0] == 'hint' else None))
        elif s[0] == 'ite':
            out.append(('ite', outline(s[2]), outline(s[3])))
        elif s[0] == 'match':
            out.append(('match', [outline(x) for x in s[2]]))
        else:
            out.append(('ctl', s[0]))
    return out


DEF = re.compile(r'^(?:noncomputable )?def (\w+) : ([^\n]*?) :=', re.M)


def defs(text):
    """The definitions of a namespace's text, by name: their terms' text."""
    ms = list(DEF.finditer(text))
    out = {}
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        body = text[m.end():end]
        body = re.split(r'\n/--|\nend\b|\nnamespace |\n@\[|\nopen ', body)[0]
        # `data% t` (`Guest/DataLit.lean`) is the literal `t`
        out[m.group(1)] = re.sub(r'^\s*data% ', ' ', body)
    return out


# ---- the generated packs, read once: `core_blocks`, `bundle_blocks`

_TEXTS = {}


def read_text(p):
    if p not in _TEXTS:
        with open(p, encoding='utf-8') as fh:
            _TEXTS[p] = fh.read().replace('data% ', '')  # the data literals' `data%` (`Guest/DataLit.lean`)
    return _TEXTS[p]


def unlit(t):
    """A pack's `Bundle.lean` text with its numerals as written before `(nat_lit n)` (`GuestCert.natLits`)."""
    return NAT_LIT.sub(r'\1', t)


NAT_LIT = re.compile(r'\(nat_lit (\w+)\)')


def core_paths():
    """The packs' core modules, by pack and module number (`Core`, `Core1`, `Core2`, ...)."""
    return sorted(glob.glob(ROOT + '/Pack/*/Core*.lean'),
                  key=lambda p: (p.split('/')[-2], int(os.path.basename(p)[4:-5] or 0)))


CORE_NS = re.compile(r'^namespace LeanVM\.Guest\.Fn\.«([^»]+)»\n(.*?)^end LeanVM\.Guest\.Fn\.«\1»$', re.M | re.S)


def core_blocks():
    """Each function's namespace blocks in the packs' core modules, by stable name: `[(pack, module, text)]`, in
    module order."""
    out = {}
    for p in core_paths():
        pack, mod = p.split('/')[-2], os.path.basename(p)[:-5]
        for m in CORE_NS.finditer(read_text(p)):
            out.setdefault(m.group(1), []).append((pack, mod, m.group(2)))
    return out


def own_packs():
    """The functions with a pack of their own (`Pack/<key>/`), their core over its `Core*.lean`."""
    return {os.path.basename(os.path.dirname(d)) for d in glob.glob(ROOT + '/Pack/*/')
            if not re.fullmatch(r'P\d+', os.path.basename(os.path.dirname(d)))}


@functools.cache
def core_texts():
    """Each function's core text, by stable name: its block of its pack's `Core.lean`, or, with a pack of its own,
    all its pack's core modules."""
    out = {}
    own = own_packs()
    paths = core_paths()
    for p in paths:
        if p.split('/')[-2] not in own and os.path.basename(p) == 'Core.lean':
            for m in CORE_NS.finditer(read_text(p)):
                out[m.group(1)] = m.group(2)
    for p in paths:
        pack = p.split('/')[-2]
        if pack in own:
            out[pack] = out.get(pack, '') + read_text(p)
    return out


@functools.cache
def bundle_blocks():
    """Each compiled function's part of its pack's `Bundle.lean`, from its name to the next function, by stable
    name: `(pack, text)`."""
    out = {}
    for b in sorted(glob.glob(ROOT + '/Pack/*/Bundle.lean')):
        pack = b.split('/')[-2]
        for blk in unlit(read_text(b)).split('\nnamespace LeanVM.Guest.Fn.')[1:]:
            out[blk.split('\n', 1)[0].strip().strip('«»')] = (pack, blk)
    return out


CODE = re.compile(r'def code : CompiledFunction :=\s*⟨"([^"]*)", (\d+), (\d+), \[([^\]]*)\]⟩')


def code_of(blk):
    """A bundle block's `code`: its compiled name, entry pc, instruction count and chunks' names."""
    m = CODE.search(blk)
    return m.group(1), int(m.group(2)), int(m.group(3)), [c.strip() for c in m.group(4).split(',') if c.strip()]


def chunks_of(blk):
    """A bundle block's code chunks, each a list of its instructions `(op, operands)` (`head`)."""
    ds = defs(blk)
    cache = {}

    def env(n):
        if n not in cache:
            cache[n] = parse(ds[n])
        return cache[n]
    return [[head(x) for x in as_list(env(c), env)] for c in code_of(blk)[3]]


def body_of(text):
    """A core function's body as the hint bridge's checks read it (`outline`)."""
    return outline(core_body(text))


@functools.cache
def bundles():
    """Each compiled function's code, certificate cells, self frame pointer cells and plumbing cells, by stable name."""
    out = {}
    cells_texts = {}
    for p in glob.glob(ROOT + '/Pack/*/Cells*.lean'):
        key = os.path.basename(os.path.dirname(p))
        cells_texts.setdefault(key, []).append(read_text(p))
    for key, (pack, blk) in bundle_blocks().items():
        text = blk + ''.join(cells_texts.get(key, []))
        ds = defs(text)
        cache = {}

        def env(n, ds=ds, cache=cache):
            if n not in cache:
                cache[n] = parse(ds[n])
            return cache[n]
        _, entry, cnt, _ = code_of(blk)
        code = [i[0] for ch in chunks_of(blk) for i in ch]
        assert len(code) == cnt, (key, len(code), cnt)
        cert = re.search(r'noncomputable def cert : Check\.Cert where\n(.*?)\n(?:/--|\Z)', blk, re.S).group(1)
        cl = re.search(r'^  cells := (.*)$', cert, re.M).group(1)
        locs = []
        for w in as_list(parse(cl), env):
            locs += as_list(w, env)
        fe = re.search(r'^  facts := \{ env := \[([^\]]*)\]', cert, re.M)
        selfs = [int(x) for x in re.findall(r'\((\d+), \(', fe.group(1))] if fe else []
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
        out[key] = dict(key=key, pack=pack, entry=entry, count=cnt, code=code, locs=locs, plumb=plumb, env=selfs)
    return out


@functools.cache
def advice():
    """The advice by function: its index in `Data.adviceFns`, keyed by entry pc, with its hints by pc."""
    t = advice_text()
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
    if h in ('witnessStack', 'witnessHeap'):
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


def fn_thms(thms, ns='LeanVM.Guest'):
    """Per-function theorems in one section of namespace `ns`: each `(k, name, stmt, prf)` declared as
    `Fn.«k».name`, so its statement and proof see function `k`'s namespace; `prf` a tactic script (lines joined),
    or a term (`:= t`)."""
    out = []
    for t in thms:
        if isinstance(t, str):
            # a command of its own (`Bridge/ChkLit.lean`'s `alloc_chk%`, `align_chk%`)
            out.append(t); continue
        k, name, stmt, prf = t
        if prf.startswith(':= '):
            out.append(f'theorem Fn.«{k}».{name} : {stmt} {prf}\n'); continue
        tac = '; '.join(x.strip() for x in prf.strip().split('\n'))
        out.append(f'theorem Fn.«{k}».{name} : {stmt} := by {tac}\n')
    return (f'set_option linter.style.nameCheck false\n\nnamespace {ns}\n\npublic section\n\n' + ''.join(out) +
            f'\nend\n\nend {ns}\n')


# ---- the hints `compiles` pairs (`Bridge/Defs.lean`)

# the ISA hints that compile a core flow hint
FLOW = {'witnessStack', 'witnessHeap', 'log2Ceil', 'bitDecompose', 'bitDecomposeExp', 'windowsExp',
        'digitDecomposeExp', 'fieldLimbs', 'inverse'}


def run_need(vs, b):
    return [(v, b + i) for i, v in enumerate(vs)]


def dest_need(d, bd, pos, n):
    if d[0] == 'stack' and bd[0] == 'stack' and len(d[1]) == n:
        return run_need(d[1], bd[1] + pos)
    if d[0] == 'heap' and bd[0] == 'heap' and d[2] == pos and d[3] == n:
        return [(d[1], bd[1])]
    return None


def need(c, h):
    """The cells `compiles` needs of the core hint `c`'s values for the ISA hint `h`, `(value, cell)`,
    or `None` when no cell map makes `h` compile `c`."""
    k, t = c[0], h[0]
    if k == 'witness' and c[2][0] == 'stack' and t == 'witnessStack':
        return run_need(c[2][1], h[2]) if c[1] == h[1] and len(c[2][1]) == h[3] else None
    if k == 'witness' and c[2][0] == 'heap' and t == 'witnessHeap':
        _, p, off, ln = c[2]
        return [(p, h[2])] if c[1] == h[1] and off == h[3] and ln == h[4] else None
    if k == 'bits' and t == 'bitDecompose':
        _, v, start, nbits, d = c
        if start != 0 or nbits != h[3]:
            return None
        dn = dest_need(d, h[2], 0, nbits)
        return None if dn is None else [(v, h[1])] + dn
    if k == 'bitsExp' and t == 'bitDecomposeExp':
        _, v, nbits, d = c
        if nbits != h[3] or nbits > 62:
            return None
        dn = dest_need(d, h[2], 0, nbits)
        return None if dn is None else [(v, h[1])] + dn
    if k == 'digitsExp' and t == 'digitDecomposeExp':
        _, v, nb, nd, db, st, sc, d = c
        if (nb, nd, db, st) != tuple(h[3:7]) or nb > 62 or (sc is None) != (h[7] is None):
            return None
        dn = dest_need(d, h[2], 0, nd)
        return None if dn is None else [(v, h[1])] + ([] if sc is None else [(sc, h[7])]) + dn
    if k == 'windowsExp' and t == 'windowsExp':
        _, v, st, w, n, d = c
        if (st, w, n) != tuple(h[4:7]):
            return None
        dn = dest_need(d, h[2], h[3], n)
        return None if dn is None else [(v, h[1])] + dn
    if k == 'log2Ceil' and t == 'log2Ceil':
        _, d, nbits, fl, dst = c
        if (nbits, fl) != (h[3], h[4]):
            return None
        dn = dest_need(d, h[1], 0, nbits)
        return None if dn is None else dn + [(dst, h[2])]
    if k == 'inverse' and t == 'inverse':
        return [(c[1], h[1]), (c[2], h[2])]
    if k == 'limbs' and t == 'fieldLimbs':
        return [(c[1], h[1])] + run_need(c[2], h[2]) if len(c[2]) == h[3] else None
    return None


def core_module(key):
    """The core IR module of a function whose pack is its own (`align.py` reads it)."""
    if os.path.isdir(os.path.join(ROOT, 'Pack', key)):
        return f'LeanVM.Guest.Pack.«{key}».Core'
    return None
