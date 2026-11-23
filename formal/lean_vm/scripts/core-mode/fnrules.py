"""Each guest function's own routing rules, read generically.

`fn/<f>.py` holds what the core route knows of the source function `f` alone: its specializations' and loops' rules
(`src(k)` maps a core name to its source function, and a rule file names only its own), as module-level tables and
hooks. The generators read them through this module, merged; none of them names a function, but for the exceptions
`formal/notes/core-mode.md` lists (the root `main`, `monocall.py`'s claim list, the whole-program checks' ranges). A
guest edit to one function changes that function's rule file at most (but for those exceptions); an edit to an
inlined helper is an edit to every function that inlines it, and a positional name (an expansion path, `@k`, `~k`)
can shift on an insertion before it, which the Lean side then reports.

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
  gl(k, np)        the caller's cells linked to a ghost family's or a frame loop's slots (`CoreMode.mlGl`, `cmGl`),
                   `{d: (slot, k)}`, `np` its parameters' count
  split(k)         `(x, n)`: its heap certificate split at the top-level selector `x` of `n` arms (`HCert.arms`)
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


def guest_arr(name):
    """The guest's constant array `name` of numbers (`Data.arr_NAME`)."""
    t = open(CONSTS, encoding='utf-8').read()
    body = re.search(r'def arr_%s : List \(Nat × Nat\) :=\s*\[(.*?)\]' % name, t, re.S).group(1)
    return [int(a) for a, _ in re.findall(r'\((\d+), (\d+)\)', body)]


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


GUEST = os.path.join(HERE, '..', '..', 'LeanVM', 'Guest')
OWNDIR = os.path.join(GUEST, 'CoreMode', 'Fn')
# a token: an operator, a bracket, a string, a «name», an identifier (dotted, `%`-suffixed), a numeral
_LTOK = re.compile(r"\+\+|↦|=>|[\[\](),+\-*/%^⟨⟩]|\"[^\"\n]*\"|«[^»\n]*»|\.?[^\W\d][\w.']*%?|0x[0-9A-Fa-f_]+|\d[\d_]*")
# what ends a definition's body: a top-level command at column 0
_LEND = re.compile(r"^(?:@\[|(?:(?:private|protected|noncomputable|public|meta|partial|unsafe) )*"
                   r"(?:def|abbrev|theorem|lemma|instance|structure|inductive|class|end|namespace|section|open|"
                   r"variable|set_option|example|attribute|#\w+)(?![\w'.]))", re.M)
_LEAN = {}


def _uncomment(t):
    """`t` without its comments, nested block comments included (a string's text kept)."""
    out, i, n = [], 0, len(t)
    while i < n:
        if t.startswith('/-', i):
            d, i = 1, i + 2
            while d:
                if i >= n:
                    raise SystemExit('fnrules: unterminated comment')
                if t.startswith('/-', i):
                    d, i = d + 1, i + 2
                elif t.startswith('-/', i):
                    d, i = d - 1, i + 2
                else:
                    i += 1
            out.append(' ')
        elif t.startswith('--', i):
            while i < n and t[i] != '\n':
                i += 1
        elif t[i] == '"':
            j = t.index('"', i + 1) + 1
            out.append(t[i:j])
            i = j
        else:
            out.append(t[i])
            i += 1
    return ''.join(out)


def _tokens(body, where):
    """`body`'s tokens, which must cover it but for whitespace."""
    toks, i = [], 0
    while True:
        while i < len(body) and body[i].isspace():
            i += 1
        if i == len(body):
            return toks
        m = _LTOK.match(body, i)
        if not m:
            raise SystemExit('fnrules: %s: cannot read %r' % (where, body[i:i + 20]))
        toks.append(m.group(0))
        i = m.end()


def lean_def(f, mod, name, *args):
    """The literal of `def name` in `CoreMode/Fn/<f>/<mod>.lean`, read: what a rule file mirrors of its function's
    Lean data, so the two never disagree. Lists, `++`, `l.map fun x ↦ e`, `(List.range n)`, tuples and `⟨…⟩`, natural
    numerals and `+ - * / % ^` on them (Lean's precedence, `-` truncated), strings, `none`, `some x`, `name% «k»` (`k`),
    `val%`, `valf%`, `pos%`, `param%`, `guest_const%` (resolved as above), `word a b` (`(a, b)`), `.n x` (`x`), an
    atom `.op a ...` (`('op', a, ...)`), the def's explicit parameters (bound to `args`) and another def of the same
    module without parameters. Anything else, or a token left over, fails: the body is read whole or not at all."""
    return lean_def_at(os.path.join(OWNDIR, f, mod + '.lean'), name, *args)


def lean_def_at(path, name, *args):
    """`lean_def` of the module at `path` under `LeanVM/Guest`: a function's data its owner's module holds."""
    where = '%s:%s' % (os.path.relpath(os.path.join(GUEST, path), GUEST), name)
    if path not in _LEAN:
        _LEAN[path] = _uncomment(open(os.path.join(GUEST, path), encoding='utf-8').read())
    t = _LEAN[path]
    heads = list(re.finditer(r"^(?:(?:private|protected|noncomputable|public) )*(?:def|abbrev) %s(?![\w'.])"
                             % re.escape(name), t, re.M))
    if len(heads) != 1:
        raise SystemExit('fnrules: %d defs %s in %s' % (len(heads), name, where.rsplit(':', 1)[0]))
    start = heads[0].end()
    end = _LEND.search(t, start)
    decl = t[start:end.start() if end else len(t)]
    # the signature (its explicit binders the parameters, no `:=` of its own), then the body
    if ':=' not in decl:
        raise SystemExit('fnrules: %s has no body' % where)
    sig, body = decl.split(':=', 1)
    params = [x for g in re.findall(r'\(([^():]+):[^()]*\)', sig) for x in g.split()]
    if re.search(r'[{\[⦃]', sig.split(':')[0]) or len(params) != len(args):
        raise SystemExit('fnrules: %s takes %s, given %d arguments' % (where, params, len(args)))
    toks = _tokens(body, where)
    v, i = _Lean(toks, where, lambda n: lean_def_at(path, n)).expr(0, dict(zip(params, args)))
    if i != len(toks):
        raise SystemExit('fnrules: %s: cannot read %s' % (where, ' '.join(toks[i:i + 8])))
    return v


class _Lean:
    """A recursive descent over the tokens; every method returns its value and the next token's index."""
    # binary operators: precedence (Lean's), right associative
    OPS = {'++': (65, False), '+': (65, False), '-': (65, False), '*': (70, False), '/': (70, False),
           '%': (70, False), '^': (75, True)}
    CLOSE = {'[': ']', '(': ')', '⟨': '⟩'}

    def __init__(self, t, where, ref):
        self.t, self.where, self.ref = t + [None], where, ref

    def fail(self, i, what):
        raise SystemExit('fnrules: %s: %s at %s' % (self.where, what, ' '.join(str(x) for x in self.t[i:i + 8]
                                                                               if x is not None) or 'the end'))

    def expr(self, i, env, prec=0):
        v, i = self.post(i, env)
        while self.t[i] in self.OPS and self.OPS[self.t[i]][0] >= prec:
            op = self.t[i]
            p, right = self.OPS[op]
            w, i = self.expr(i + 1, env, p if right else p + 1)
            v = self.apply(i, op, v, w)
        return v, i

    def apply(self, i, op, v, w):
        if op == '++':
            if not (isinstance(v, list) and isinstance(w, list)):
                self.fail(i, '`++` of non-lists')
            return v + w
        if not (isinstance(v, int) and isinstance(w, int)):
            self.fail(i, '`%s` of non-numerals' % op)
        return {'+': lambda: v + w, '-': lambda: max(v - w, 0), '*': lambda: v * w,
                '/': lambda: v // w if w else 0, '%': lambda: v % w if w else v, '^': lambda: v ** w}[op]()

    def post(self, i, env):
        v, i = self.term(i, env)
        while self.t[i] == '.map':
            if not (self.t[i + 1] == 'fun' and self.t[i + 3] in ('↦', '=>')):
                self.fail(i, 'a `.map` not of `fun x ↦ e`')
            if not isinstance(v, list):
                self.fail(i, '`.map` of a non-list')
            x, b = self.t[i + 2], i + 4
            out, j = [], None
            for e in v:
                w, j = self.expr(b, dict(env, **{x: e}))
                out.append(w)
            if j is None:
                j = self.skip(b)
            v, i = out, j
        return v, i

    def skip(self, i):
        """Past an expression not evaluated (a `.map`'s body over no element)."""
        d = 0
        while self.t[i] is not None and not (d == 0 and self.t[i] in (',', ')', ']', '⟩')):
            d += 1 if self.t[i] in self.CLOSE else -1 if self.t[i] in self.CLOSE.values() else 0
            i += 1
        return i

    def ident(self, i):
        x = self.t[i]
        if x is None or not (x.startswith('«') or re.fullmatch(r"[^\W\d][\w']*", x)):
            self.fail(i, 'a name expected')
        return x.strip('«»'), i + 1

    def str(self, i):
        if self.t[i] is None or not self.t[i].startswith('"'):
            self.fail(i, 'a string expected')
        return self.t[i][1:-1], i + 1

    def term(self, i, env):
        t, x = self.t, self.t[i]
        if x is None:
            self.fail(i, 'a term expected')
        if x in self.CLOSE:
            close = self.CLOSE[x]
            out, i = [], i + 1
            while t[i] != close:
                v, i = self.expr(i, env)
                out.append(v)
                if t[i] == ',':
                    i += 1
                    if t[i] == close:
                        self.fail(i, 'a trailing `,`')
                elif t[i] != close:
                    self.fail(i, '`,` or `%s` expected' % close)
            i += 1
            if x == '[':
                return out, i
            if not out:
                self.fail(i, 'an empty tuple')
            return (out[0] if len(out) == 1 and x == '(' else tuple(out)), i
        if re.fullmatch(r'\d[\d_]*', x):
            return int(x.replace('_', '')), i + 1
        if x.startswith('0x') and re.fullmatch(r'0x[0-9A-Fa-f_]+', x):
            return int(x[2:].replace('_', ''), 16), i + 1
        if x.startswith('"'):
            return self.str(i)
        if x in env:
            return env[x], i + 1
        if x in ('none', '.none'):
            return None, i + 1
        if x in ('some', '.some'):
            return self.term(i + 1, env)
        if x == 'List.range':
            n, i = self.term(i + 1, env)
            if not isinstance(n, int):
                self.fail(i, '`List.range` of a non-numeral')
            return list(range(n)), i
        if x == 'name%':
            return self.ident(i + 1)
        if x == 'guest_const%':
            n, i = self.ident(i + 1)
            return guest_const(n), i
        if x in ('val%', 'pos%', 'param%'):
            fs, i = [], i + 1
            while t[i] is not None and not t[i].startswith('"'):
                g, i = self.ident(i)
                fs.append(g)
            n, i = self.str(i)
            if not fs or (x != 'val%' and len(fs) > 1):
                self.fail(i, '`%s` of %d functions' % (x, len(fs)))
            vs = {{'val%': val, 'pos%': pos, 'param%': param}[x](g, n) for g in fs}
            if len(vs) != 1:
                self.fail(i, '`%s` naming different values in %s' % (x, ' '.join(fs)))
            return vs.pop(), i
        if x == 'valf%':
            f, i = self.ident(i + 1)
            sn = []
            while t[i] is not None and not t[i].startswith('"'):
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
        if re.fullmatch(r"\.[^\W\d][\w']*", x) and x != '.map':
            args, i = [], i + 1
            while t[i] is not None and t[i] not in (',', ')', ']', '⟩', '.map') and t[i] not in self.OPS:
                a, i = self.term(i, env)
                args.append(a)
            return (x[1:],) + tuple(args), i
        if re.fullmatch(r"[^\W\d][\w']*", x):
            return self.ref(x), i + 1
        self.fail(i, 'an unknown token')


NAMESTRINGS = os.path.join(HERE, '..', '..', 'LeanVM', 'Guest', 'Data', 'NameStrings.lean')


def shapes(f):
    """The specializations `f__L{a}_L{b}…` of source function `f` (its loops left out), by core name, each with its
    numbers `(a, b, …)` (`Data/NameStrings.lean`)."""
    t = open(NAMESTRINGS, encoding='utf-8').read()
    return {k: tuple(map(int, re.findall(r'_L(\d+)', k[len(f) + 1:])))
            for k in re.findall(r'abbrev «(%s__L\d+(?:_L\d+)*)» :' % re.escape(f), t)}


# last: a rule file may use the helpers above (`param`, `guest_const`, `val`, `valf`, `pos`, `shapes`)
MODS = _load()
