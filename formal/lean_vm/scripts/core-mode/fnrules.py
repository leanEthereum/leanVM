"""Each guest function's own routing rules, read generically.

`fn/<f>.py` holds what the core route knows of the source function `f` alone: its specializations' and loops' rules
(`src(k)` maps a core name to its source function, and a rule file names only its own), as module-level tables and
hooks. The generators read them through this module, merged; none of them names a function. A guest edit to one
function changes that function's rule file at most (`formal/notes/core-mode.md`).

Tables (each a dict by core name, or a list of entries whose first field is a core name):
  FEATURES     inference feature sets tried after the generic ones (`callcres.py`), a list of extra sets
  EXP_FACTS    `(k, parameter, offset, bound)` (`Res.expFacts`); DIM_FACTS `(k, base, bound, pairs)` (`Res.dimFacts`)
  EXP_VALS     `(k, value, bound)`: a value `g^e`, `e < bound` (`CoreMode.expVal`)
  ST_LOOPS     stream-cursor loops `(D, v, S)` (`CoreMode.stLoops`)
  CM_LOOPS     the gap walk's frame loops, claims a frame (`CoreMode.cmK`)
  SPLITS       `g`-power splits (`CoreMode.splitsC`)
  CTR_PRE      loops whose run preconditions may be over the counter (`infer.py`)
  CONTRACTS    contracts given by hand (`sigc.py`), as `Mode.Sig` literal fields past the entry
  CORE_WIN, PAIR_WIN, FRAME_WIN: functions checked in windows of their own sizes, and the sizes (`windows.py`)
  The counts (`scripts/count`, by stable name; `gen.py`, `vscount.py` name no function):
  STATIC       the entry's statically bounded callees `Count/Static.lean` bounds: `(order, kind, Lean name)`, kind
               `const`, `loop` or one its `count_static` writes
  RATIOV       functions counted within ratios of their words (`Count/RatioV*`): `(order, Lean name)`
  COUNT_SHAPE  functions counted by their trees' shapes (`count_walk`, `count_parts`), not a certificate: the family
               letter whose certificates cover their other callees
  RATIO_WORDS  callees counted within a ratio of these words: a number, or a function of the counts and the name
  COUNT_OM     functions whose frame weights a count module holds: `(module, order)`
Hooks (functions; each answers for its own core names only, else `None`/`False`):
  fam(k, r)        a ghost-free residual of the function's family (`CoreMode.resFamG`'s own families)
  ghost(k, r)      a residual of its ghost family (no bound on its values)
  sub(k, c)        a read `c` witnessed by a residual `sub c R` of its family: that residual
  exp_bound(k, x)  an exponent bound of `x`, plus one, its family proves (`expQB`)
  arg_bound(k, x), arg_bound_mono(k, x), sel_bound(k, x): bounds of a callee's argument, a word times `g^c`, a
                   parameter as a selector
  res_filter(k, r) whether the solver may state residual `r` (`emitc.RES_FILTER`); fact(EM, base): the solver's
                   exponent facts of the function's family
  ml_k(k)          the ghost family `ml`'s index (`CoreMode.mlK`)
Count hooks (`scripts/count`; a function's may name its callees, as its counts are made of theirs):
  count_arms(g)    the opening arms, by stack log (`gen.G.os_names`)
  count_static(n, kind, N, certs, OPS, opdef, hcf): `Count/Static.lean`'s text for its `STATIC` entry of another kind
  count_walk(C, k, n): its instructions at opcode index `k` by its tree's shape, from its family's counts `C`
  count_words_by_name(g): text appended to `Count/Words.lean`'s tables
  count_parts(g, OPS): its parts of the count modules (`vscount.write`)
  deployed_value(W, name), deployed_parts(W): its values of `B1.Main.mainWords` and its parts of the
                   `Count/Deployed*` modules (`deployed.py`)
"""
import os, re, sys, glob, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
FN = os.path.join(HERE, 'fn')
SOURCE = os.path.join(HERE, '..', '..', 'LeanVM', 'Guest', 'Data', 'Source.lean')
CONSTS = os.path.join(HERE, '..', '..', 'LeanVM', 'Guest', 'Data', 'Consts.lean')
VALNAMES = os.path.join(HERE, '..', '..', 'LeanVM', 'Guest', 'Data', 'ValNames')

class _Infer:
    """`infer`, imported at first use: a rule file reads the inference's state (`I.callee`, `I.GB`, `I.F`) only in its
    hooks, so loading the rule files imports nothing."""
    def __getattr__(self, a):
        import infer
        return getattr(infer, a)


I = _Infer()

_SRC = re.compile(r'^(.*?)((__L\d+)(_L\d+)*)?((_loop\d+)*)$')


def src(k):
    """The source function a core function belongs to: its name less its specialization (`__L…`) and loop
    (`_loop…`) suffixes, a loop's of its caller's."""
    while True:
        m = re.fullmatch(r'(.*)_loop\d+', k)
        if not m:
            break
        k = m.group(1)
    return re.sub(r'__L\d+(_L\d+)*$', '', k)


def _load():
    mods = {}
    for p in sorted(glob.glob(os.path.join(FN, '*.py'))):
        name = os.path.basename(p)[:-3]
        spec = importlib.util.spec_from_file_location('fn_' + name, p)
        m = importlib.util.module_from_spec(spec)
        sys.modules['fn_' + name] = m
        spec.loader.exec_module(m)
        mods[name] = m
    return mods



def _own(f, k):
    if src(k) != f:
        raise SystemExit('fnrules: fn/%s.py names %s, of %s' % (f, k, src(k)))
    return k


def table(name):
    """The table `name` over every rule file: a dict merged, or a list concatenated (each key or entry its file's)."""
    out = None
    for f, m in MODS.items():
        t = getattr(m, name, None)
        if t is None:
            continue
        if isinstance(t, dict):
            out = {} if out is None else out
            for k, v in t.items():
                out[_own(f, k[0] if isinstance(k, tuple) else k)] = v
        elif isinstance(t, (set, frozenset)):
            out = set() if out is None else out
            out |= {_own(f, k) for k in t}
        else:
            out = [] if out is None else out
            for e in t:
                _own(f, e[0])
            out += list(t)
    return out


def hooks(name):
    """The rule files' hooks `name`."""
    return [getattr(m, name) for m in MODS.values() if callable(getattr(m, name, None))]


def first(name, *args):
    """The first hook `name` answering (not `None`)."""
    for h in hooks(name):
        r = h(*args)
        if r is not None:
            return r
    return None


def some(name, *args):
    """A hook `name` holds."""
    return any(h(*args) for h in hooks(name))


_PARAMS = {}


def param(f, p):
    """`param% f "p"`: the position of source function `f`'s parameter `p` (`Data/Source.lean`), every one up to it a
    runtime scalar."""
    if not _PARAMS:
        t = open(SOURCE, encoding='utf-8').read()
        for name, ps in re.findall(r'def fn_(\w+) : Func :=\s*\{ name := "[^"]*", params := \[(.*?)\], returnShapes', t, re.S):
            _PARAMS[name] = re.findall(r'⟨"([^"]+)", \(([^)]*)\)⟩', ps)
    ps = _PARAMS[f]
    for i, (n, kind) in enumerate(ps):
        if kind != '.runtime .scalar':
            break
        if n == p:
            return i
    raise SystemExit('fnrules: %s has no runtime scalar parameter %s up front' % (f, p))


def guest_const(name):
    """The guest's constant `name` (`guest_const%`)."""
    t = open(CONSTS, encoding='utf-8').read()
    return int(re.search(r'def const_%s : Nat := (\d+)' % name, t).group(1))


_NAMES = {}


def _names(key):
    """The names `scripts/val-names/gen.py` resolved for `key` (`Data/ValNames/<key>.lean`), by namespace and name."""
    if key not in _NAMES:
        p = os.path.join(VALNAMES, key + '.lean')
        t = open(p, encoding='utf-8').read() if os.path.exists(p) else ''
        out = {}
        for ns, body in re.findall(r'namespace (V|F|S)\n(.*?)end \1\n', t, re.S):
            for n, i in re.findall(r'abbrev «[^/»]*/([^»]*)» : Nat := (\d+)', body):
                out[(ns, n)] = int(i)
        _NAMES[key] = out
    return _NAMES[key]


def _name(key, ns, n):
    r = _names(key).get((ns, n))
    if r is None:
        raise SystemExit('fnrules: no name %s of %s: cite it and run scripts/val-names/gen.py' % (n, key))
    return r


def val(f, n):
    """`val% f "n"`: the value of core function `f` named `n` (its source name or expansion path)."""
    return _name(f, 'V', n)


def valf(f, *sn):
    """`valf% f [suffix] "n"`: the value named `n` in every specialization of `f` (`f__L…suffix`), one number."""
    suffix, n = ('', sn[0]) if len(sn) == 1 else sn
    return _name(f + '__L' + suffix, 'F', n)


def pos(f, n):
    """`pos% f "n"`: the position of the top-level statement of `f` that names `n` first."""
    return _name(f, 'S', n)


OWNDIR = os.path.join(HERE, '..', '..', 'LeanVM', 'Guest', 'CoreMode', 'Fn')
_LTOK = re.compile(r'\s*(\+\+|↦|[\[\](),+*⟨⟩]|"[^"]*"|«[^»]*»|[A-Za-z_.%][A-Za-z_0-9.%]*|\d+)')
_LEAN = {}


def lean_def(f, mod, name):
    """The literal of `def name` in `CoreMode/Fn/<f>/<mod>.lean`, read: what a rule file mirrors of its function's
    Lean data, so the two never disagree. Lists, `++`, `l.map fun x ↦ e`, `(List.range n)`, tuples and `⟨…⟩`, numerals, `+`,
    `*`, strings, `none`, `some x`, `name% «k»` (`k`), `val%`, `valf%`, `pos%`, `param%`, `guest_const%` (resolved as above),
    `word a b` (`(a, b)`), `.n x` (`x`) and an atom `.op a ...` (`('op', a, ...)`)."""
    key = (f, mod)
    if key not in _LEAN:
        t = open(os.path.join(OWNDIR, f, mod + '.lean'), encoding='utf-8').read()
        _LEAN[key] = re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '', t, flags=re.S))
    m = re.search(r'^(?:noncomputable )?def %s\b[^\n]*?:=(.*?)(?=^\S|\Z)' % re.escape(name), _LEAN[key], re.S | re.M)
    if not m:
        raise SystemExit('fnrules: no def %s in CoreMode/Fn/%s/%s.lean' % (name, f, mod))
    toks = _LTOK.findall(m.group(1))
    v, i = _Lean(toks).expr(0, {})
    if i != len(toks):
        raise SystemExit('fnrules: %s.%s.%s: cannot read %s' % (f, mod, name, ' '.join(toks[i:i + 8])))
    return v


class _Lean:
    def __init__(self, t):
        self.t = t

    def expr(self, i, env):
        v, i = self.prod(i, env)
        while i < len(self.t) and self.t[i] in ('++', '+'):
            w, i = self.prod(i + 1, env)
            v = v + w
        return v, i

    def prod(self, i, env):
        v, i = self.post(i, env)
        while i < len(self.t) and self.t[i] == '*':
            w, i = self.post(i + 1, env)
            v = v * w
        return v, i

    def post(self, i, env):
        v, i = self.term(i, env)
        while i < len(self.t) and self.t[i] == '.map':
            assert self.t[i + 1] == 'fun' and self.t[i + 3] == '↦', self.t[i:i + 4]
            x, b = self.t[i + 2], i + 4
            out, j = [], b
            for e in v:
                w, j = self.expr(b, dict(env, **{x: e}))
                out.append(w)
            if not v:
                j = self.skip(b)
            v, i = out, j
        return v, i

    def skip(self, i):
        d = 0
        while i < len(self.t) and not (d == 0 and self.t[i] in (',', ')', ']', '⟩')):
            d += self.t[i] in ('(', '[', '⟨') and 1 or (self.t[i] in (')', ']', '⟩') and -1 or 0)
            i += 1
        return i

    def ident(self, i):
        return self.t[i].strip('«»'), i + 1

    def str(self, i):
        assert self.t[i].startswith('"'), self.t[i]
        return self.t[i][1:-1], i + 1

    def term(self, i, env):
        t, x = self.t, self.t[i]
        if x in ('[', '(', '⟨'):
            close = {'[': ']', '(': ')', '⟨': '⟩'}[x]
            out, i = [], i + 1
            while t[i] != close:
                v, i = self.expr(i, env)
                out.append(v)
                if t[i] == ',':
                    i += 1
            i += 1
            if x == '[':
                return out, i
            return (out[0] if len(out) == 1 and x == '(' else tuple(out)), i
        if x.isdigit():
            return int(x), i + 1
        if x.startswith('"'):
            return self.str(i)
        if x in env:
            return env[x], i + 1
        if x == 'none':
            return None, i + 1
        if x == 'some':
            return self.term(i + 1, env)
        if x == 'List.range':
            n, i = self.term(i + 1, env)
            return list(range(n)), i
        if x == 'name%':
            return self.ident(i + 1)
        if x == 'guest_const%':
            n, i = self.ident(i + 1)
            return guest_const(n), i
        if x in ('val%', 'pos%', 'param%'):
            f, i = self.ident(i + 1)
            n, i = self.str(i)
            return {'val%': val, 'pos%': pos, 'param%': param}[x](f, n), i
        if x == 'valf%':
            f, i = self.ident(i + 1)
            sn = []
            while not t[i].startswith('"'):
                s, i = self.ident(i)
                sn.append(s)
            n, i = self.str(i)
            return valf(f, *(sn + [n])), i
        if x == 'word':
            a, i = self.term(i + 1, env)
            b, i = self.term(i, env)
            return (a, b), i
        if x == '.n':
            return self.term(i + 1, env)
        if x.startswith('.') and x != '.map':
            args, i = [], i + 1
            while i < len(t) and t[i] not in (',', ')', ']', '⟩', '++', '+', '*', '.map'):
                a, i = self.term(i, env)
                args.append(a)
            return (x[1:],) + tuple(args), i
        raise SystemExit('fnrules: cannot read Lean token %s' % x)


# last: a rule file may use the helpers above (`param`, `guest_const`, `val`, `valf`, `pos`)
MODS = _load()
