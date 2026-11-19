"""The frame walk's inputs, read from the generated data (`compiled.py`): each function's code, hints, executor facts
(`Check.Cert.facts` in its `Bundle`), callee frame signatures (the frame layout's) and table targets; and, for a
function off the core route (whose pairing gives the core route's), the oracle: the offsets whose `DEREF` the mode
walk (`scripts/mode-cert`) treats as a load of a heap cell it knows written, read off a run of that walk with its
inferred signatures (`MODE_CERT_CACHE`, as `mode-cert/gen.py` writes it), and that walk's residual divisors."""
import os, re, sys, glob, pickle, collections

HERE = os.path.dirname(os.path.abspath(__file__))
MODE = os.path.normpath(os.path.join(HERE, '..', 'mode-cert'))
sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)
import compiled as C  # noqa: E402

ROOT = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))


def sym(s):
    m = re.fullmatch(r'\(\.(gp|fpg) (\d+)\)', s.strip())
    if m: return (m.group(1), int(m.group(2)))
    assert s.strip() == '.zero', s
    return ('z',)


def facts():
    """`Check.Cert.facts` of each function: env, fpOne, arms, scaled."""
    out = {}; byns = {}
    for b in sorted(glob.glob(ROOT + '/Pack/*/Bundle.lean')):
        t = open(b).read()
        for blk in t.split('\nnamespace LeanVM.Guest.Fn.')[1:]:
            m = re.search(r'def code : CompiledFunction :=\s*⟨"([^"]*)"', blk)
            if not m: continue
            name = m.group(1)
            nsn = blk.split('\n', 1)[0].strip().strip('«»')
            byns[nsn] = name
            fm = re.search(r'facts := \{ env := \[(.*?)\], fpOne := (\w+), arms := \[(.*?)\],(?: armsT := \w+,)? '
                           r'scaled := \[(.*?)\] \}', blk)
            env = {int(o): sym(v) for o, v in re.findall(r'\((\d+), (\([^()]*\)|\.zero)\)', fm.group(1))}
            arms = {int(o): [int(x) for x in ts.split(',') if x.strip()]
                    for o, ts in re.findall(r'\((\d+), \[([^\]]*)\]\)', fm.group(3))}
            out[name] = dict(env=env, fpOne=fm.group(2) == 'true', arms=arms,
                             scaled=[int(x) for x in fm.group(4).split(',') if x.strip()], armsT='armsT :=' in fm.group(0))
    # `main_loop2`'s arms in a trie (`Cells0.lean`)
    for c in glob.glob(ROOT + '/Pack/*/Cells0.lean'):
        t = open(c).read()
        m = re.search(r'def cert_armsT : Exec\.Trie \(List ℕ\) :=(.*?)(?:\n\n|\Z)', t, re.S)
        if not m: continue
        nm = re.search(r'namespace LeanVM\.Guest\.Fn\.«?([^»\n]*)»?', t).group(1)
        out[byns[nm]]['armsT_src'] = m.group(1)
    return out


def trie_entries(src):
    """The entries of a printed `Exec.Trie`: key `0` at the root, `2m+1` at key `m` of the left
    child, `2m+2` at key `m` of the right one (`Trie.get`)."""
    toks = re.findall(r'\.node|\.nil|\(some \[[^\]]*\]\)|none|\(|\)', src)
    pos = [0]

    def rec():
        depth = 0
        while toks[pos[0]] == '(':
            pos[0] += 1; depth += 1
        t = toks[pos[0]]; pos[0] += 1
        if t == '.nil':
            node = None
        else:
            assert t == '.node', t
            v = toks[pos[0]]; pos[0] += 1
            val = [int(x) for x in re.findall(r'\d+', v)] if v.startswith('(some') else None
            node = (val, rec(), rec())
        for _ in range(depth):
            assert toks[pos[0]] == ')'; pos[0] += 1
        return node
    out = {}

    def entries(node, f):
        if node is None: return
        val, l, r = node
        if val is not None: out[f(0)] = val
        entries(l, lambda m: f(2 * m + 1)); entries(r, lambda m: f(2 * m + 2))
    entries(rec(), lambda m: m)
    return out


def mode_walk(full=False):
    """The mode walk's modules (`scripts/mode-cert/walk.py`, and with `full` its `infer.py`, imported as `mode_infer`:
    the core route has an `infer` of its own), for the functions off the core route."""
    if MODE not in sys.path:
        sys.path.append(MODE)
    import walk as W
    if not full:
        return None, W
    I = sys.modules.get('mode_infer')
    if I is None:
        import importlib.util
        spec = importlib.util.spec_from_file_location('mode_infer', os.path.join(MODE, 'infer.py'))
        I = importlib.util.module_from_spec(spec)
        sys.modules['mode_infer'] = I
        spec.loader.exec_module(I)
    return I, W


def oracle(cache, only=None):
    """Run today's mode walk on each function (of `only`, if given) with its inferred signature and residuals, and record
    each `DEREF` of mode `cell` at each offset: a store, a load of a heap cell it knows written, or
    a link. The oracle: offsets where some path loads and every path stores or loads."""
    I, W = mode_walk(True)
    sigs, fails, R, Esigs, cost = pickle.load(open(cache, 'rb'))
    I.E.sigs = Esigs
    dec = {}
    orig = W.Walk.stepOp

    def stepOp(self, i, A, op, a):
        if op == 'deref' and a[3] == '.cell':
            p, o, c, _ = a
            m = A.mono(p)
            k = W.shift(m, o) if m is not None else None
            d = 'store' if c in A.w else ('load' if k is not None and A.covered(k) else 'link')
            dec[self._name].setdefault(i, set()).add(d)
        return orig(self, i, A, op, a)
    W.Walk.stepOp = stepOp
    try:
        for n, f in I.fns.items():
            if n in fails or only is not None and n not in only: continue
            dec[n] = {}
            w = I.Walk(I.E, f['entry'], f['count'], sigs[n], f['hints'], R.get(n, {}), f['tabs'], main=n == 'main')
            w._name = n
            w.run(f['ops'])
    finally:
        W.Walk.stepOp = orig
    O = {n: sorted(i for i, ds in d.items() if 'load' in ds and 'link' not in ds) for n, d in dec.items()}
    return O, sigs, R, Esigs


def load(cache=None, ocache=None, only=None):
    """The walks' inputs; with the mode walk's cache, also its oracle (`O`, of the functions `only`, if given) and
    residuals (`R`), which only the functions off the core route read."""
    D = dict(C.code(), facts=facts(), O={}, R={})
    if cache and only is not None:
        O, sigs, R, Esigs = oracle(cache, set(only))
        D.update(O=O, R=R)
    elif cache:
        if ocache and os.path.exists(ocache):
            mode_walk()  # the pickled signatures' classes
            O, sigs, R, Esigs = pickle.load(open(ocache, 'rb'))
        else:
            O, sigs, R, Esigs = oracle(cache)
            if ocache: pickle.dump((O, sigs, R, Esigs), open(ocache, 'wb'))
        D.update(O=O, R=R)
    return D
