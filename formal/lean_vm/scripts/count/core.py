"""The generated guest data, read into Python: the core IR (`Data/Core*.lean`) and the back end's
tables (`Deployed/Data.lean`, written by `lake exe guest-tables`): each compiled function's `pmax`,
the frame sizes and the separately counted arms; and the powers of `g` below `2^20` (`pows`).

Every loader takes the data directory, `lean_vm/LeanVM/Guest/Data/`. A function is a dict
`name`, `params` (value indices), `body` (statements as tuples: `('atom', kind, args)`,
`('ite', c, zero, nonzero)`, `('match', x, arms)`, `('call', g, args, rets)`,
`('callIf', c, g, args)`, `('dispatch', x, gs, args, rets)`, `('ret', vs)`), keyed by core index
(`coreProgram[j]`, compiled index `j + 1`)."""
import re, glob, os, sys, pickle, hashlib
sys.setrecursionlimit(1000000)
TOK = re.compile(r'\s*(::|\+\+|[()\[\],⟨⟩]|"[^"]*"|\.?[A-Za-z_][A-Za-z_0-9.]*|\d+)')


def tokenize(s):
    out = []; i = 0
    while i < len(s):
        m = TOK.match(s, i)
        if not m:
            if s[i:].strip() == '': break
            raise ValueError('tok at %r' % s[i:i + 40])
        out.append(m.group(1)); i = m.end()
    return out


class P:
    def __init__(self, toks): self.t = toks; self.i = 0
    def peek(self): return self.t[self.i] if self.i < len(self.t) else None
    def take(self, x=None):
        v = self.t[self.i]; self.i += 1
        if x is not None and v != x: raise ValueError('expected %s got %s' % (x, v))
        return v
    def expr(self):
        a = self.app()
        if self.peek() == '::':
            self.take(); return ('cons', a, self.expr())
        if self.peek() == '++':
            self.take(); return ('append', a, self.expr())
        return a
    def app(self):
        h = self.atom()
        args = []
        while self.peek() is not None and self.peek() not in ('::', '++', ')', ']', ',', '⟩'):
            args.append(self.atom())
        if args:
            return ('app', h, args)
        return h
    def atom(self):
        x = self.peek()
        if x == '(':
            self.take(); e = self.expr(); self.take(')'); return e
        if x == '[':
            self.take(); items = []
            if self.peek() == ']': self.take(); return ('list', [])
            items.append(self.expr())
            while self.peek() == ',': self.take(); items.append(self.expr())
            self.take(']'); return ('list', items)
        if x.startswith('"'): self.take(); return ('str', x[1:-1])
        if x.isdigit(): self.take(); return ('num', int(x))
        self.take(); return ('id', x)


def tolist(e, defs):
    if e[0] == 'list': return e[1]
    if e[0] == 'cons': return [e[1]] + tolist(e[2], defs)
    if e[0] == 'append': return tolist(e[1], defs) + tolist(e[2], defs)
    if e[0] == 'id':
        if e[1] == '[]': return []
        return tolist(defs[e[1]], defs)
    raise ValueError('not a list: %r' % (e,))


def val(e):
    # (.n k)
    assert e[0] == 'app' and e[1] == ('id', '.n'), e
    return e[2][0][1]


def vals(e, defs): return [val(x) for x in tolist(e, defs)]


def word(e):
    assert e[0] == 'app' and e[1] == ('id', 'word'), e
    return tuple(a[1] for a in e[2])


def stmt(e, defs):
    assert e[0] == 'app', e
    h = e[1][1]; a = e[2]
    if h == '.atom':
        at = a[0]
        if at[0] == 'id': return ('atom', at[1][1:], None)
        k = at[1][1]
        if k == '.const': return ('atom', 'const', (val(at[2][0]), word(at[2][1])))
        if k in ('.add', '.mul'): return ('atom', k[1:], tuple(val(x) for x in at[2]))
        if k == '.hint':
            hh = at[2][0]
            kind = hh[1][1][1:] if hh[0] == 'app' else hh[1][1:]
            if kind == 'alloc': return ('atom', 'alloc', hh[2][1][1])
            if kind == 'allocDyn': return ('atom', 'allocDyn', val(hh[2][1]))
            return ('atom', 'hint', kind)
        return ('atom', k[1:], None)
    if h == '.ite': return ('ite', val(a[0]), block(a[1], defs), block(a[2], defs))
    if h == '.match_': return ('match', val(a[0]), [block(x, defs) for x in tolist(a[1], defs)])
    if h == '.call': return ('call', a[0][1], vals(a[1], defs), vals(a[2], defs))
    if h == '.callIf': return ('callIf', val(a[0]), a[1][1], vals(a[2], defs))
    if h == '.dispatch': return ('dispatch', val(a[0]), [x[1] for x in tolist(a[1], defs)], vals(a[2], defs), vals(a[3], defs))
    if h == '.ret': return ('ret', vals(a[0], defs))
    raise ValueError(h)


def block(e, defs): return [stmt(x, defs) for x in tolist(e, defs)]


def _texts(D):
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    import coredata
    return coredata.legacy_texts(D)


def _load(D):
    raw = {}; hdr = {}; cur = None; name = None; hcur = None
    for text in _texts(D):
        for line in text.split('\n'):
            s = line
            m = re.match(r'namespace core(\d+)$', s)
            if m: cur = int(m.group(1)); raw.setdefault(cur, {}); name = None; continue
            if re.match(r'end core\d+$', s): cur = None; name = None; continue
            m = re.match(r'noncomputable def core(\d+) : Core.Fn where', s)
            if m: hcur = int(m.group(1)); hdr[hcur] = []; name = ('H',); continue
            if name == ('H',):
                if s.strip() == '': name = None; continue
                hdr[hcur].append(s); continue
            if cur is None: continue
            if s.startswith('/--'): name = None; continue
            m = re.match(r'noncomputable def (\w+) : List Core.Stmt := (.*)$', s)
            if m: name = m.group(1); raw[cur][name] = [m.group(2)]; continue
            if name: raw[cur][name].append(s)
    fns = {}
    for i, d in raw.items():
        defs = {k: P(tokenize(' '.join(v))).expr() for k, v in d.items()}
        h = ' '.join(hdr[i])
        nm = re.search(r'name := "([^"]*)"', h).group(1)
        ps = [int(x) for x in re.findall(r'\.n (\d+)', re.search(r'params := (.*?) +body :=', h).group(1))]
        fns[i] = dict(name=nm, params=ps, body=block(defs['body'], defs))
    assert sorted(fns) == list(range(len(fns))), 'core indices not contiguous'
    return fns


def load(D, cache=None):
    """The core functions by index; `cache` a directory to keep a parse keyed by the data's hash."""
    if cache is None:
        return _load(D)
    h = hashlib.sha256()
    for t in _texts(D): h.update(t.encode('utf-8'))
    p = os.path.join(cache, 'core-%s.pickle' % h.hexdigest()[:16])
    if os.path.exists(p):
        return pickle.load(open(p, 'rb'))
    fns = _load(D)
    os.makedirs(cache, exist_ok=True)
    pickle.dump(fns, open(p, 'wb'))
    return fns


def pows():
    """The powers `g^e`, `e < 2^20`, by their word's limb 0 to `e`: `g` is `X` in `GF(2^64)`, so
    `g^(e+1)` is `g^e` shifted by one bit, reduced by `X^64 = X^4 + X^3 + X + 1` (`27`, the entry
    `g^64` of `Compiler/Pow.lean`'s `gtab`)."""
    out, x = {}, 1
    for e in range(1 << 20):
        out.setdefault(x, e)
        x = ((x << 1) & 0xFFFFFFFFFFFFFFFF) ^ (27 if x >> 63 else 0)
    return out


def deployed_data(D):
    """The text of `Deployed/Data.lean`, beside the data directory `D`."""
    return open(os.path.join(D, '..', 'Deployed', 'Data.lean'), encoding='utf-8').read()


def load_pmax(D):
    """Each compiled function's `pmax` (`Deployed.pmaxOf j`), by compiled index from `1`."""
    s = deployed_data(D)
    body = s.split('def pmax : List (List Nat) := [', 1)[1].split('\n\n', 1)[0]
    rows = re.findall(r'\[([\d, ]*)\]', body)
    return {j: [int(x) for x in r.replace(' ', '').split(',') if x] for j, r in enumerate(rows) if j > 0}


def load_frame_sizes(D):
    """`Deployed.Data.frameSizes`, by compiled index."""
    m = re.search(r'def frameSizes : List Nat := \[([\d,\s]*)\]', deployed_data(D))
    return [int(x) for x in m.group(1).replace(' ', '').replace('\n', '').split(',') if x]


def load_cpl_arms(D):
    """`Deployed.Data.arms`, by compiled index: the separately counted `match`es, `[(x, [[count per
    opcode] per arm])]`."""
    s = deployed_data(D)
    import ast
    # each counted `match`'s arms are a definition of its own, a list of `::`s
    defs = {m.group(1): '[' + m.group(2).replace(' ::', ',').rsplit(',', 1)[0] + ']'
            for m in re.finditer(r'def (arms\d+_\d+) : List \(List Nat\) :=\s*\((.*?)\)\n\n', s, re.S)}
    body = s.split('def arms : List (List (Nat × List (List Nat))) :=', 1)[1]
    body = re.sub(r'arms\d+_\d+', lambda m: defs[m.group(0)], body)
    body = body.strip()
    # The literal is a Lean list of lists of pairs: valid Python once `(`..`)` stay tuples.
    end = body.index('\n\nend') if '\n\nend' in body else len(body)
    return ast.literal_eval(body[:end].strip())


def load_scalar(D, name):
    """A natural `def`/`abbrev` of `Deployed/Data.lean`: `armFn`, `mainCells`, `jtSlots`."""
    m = re.search(r'(?:def|abbrev) %s : Nat := (\d+)\n' % name, deployed_data(D))
    assert m, 'Deployed.Data.%s not found: rerun guest-tables' % name
    return int(m.group(1))


def load_arm_max(D):
    """`Deployed.Data.armMax`."""
    m = re.search(r'def armMax : List Nat := \[([\d, ]*)\]', deployed_data(D))
    assert m, 'Deployed.Data.armMax not found: rerun guest-tables'
    return [int(x) for x in m.group(1).split(',')]


if __name__ == '__main__':
    D = sys.argv[1]
    fns = load(D)
    print(len(fns), fns[0]['name'], len(fns[0]['body']))


_STABLE = None


def L(s):
    """The compiler's name of the core function of stable name `s` (`Data/NameStrings.lean`): a loop
    helper is `{caller}_loop{k}` there, which no added or removed function renumbers."""
    global _STABLE
    if _STABLE is None:
        lv = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        t = open(os.path.join(lv, 'LeanVM', 'Guest', 'Data', 'NameStrings.lean'), encoding='utf-8').read()
        _STABLE = dict(re.findall(r'abbrev «([^»]+)» : String := "([^"]+)"', t))
    return _STABLE[s]
