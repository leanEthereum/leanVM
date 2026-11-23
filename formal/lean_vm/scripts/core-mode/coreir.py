"""The guest's core IR and compiled code, read back from the generated data for the core route's
generators (`formal/notes/core-mode.md`).

`load()` returns a dict: `core`, each core function by stable name, `(params, body)`, statements as tuples
  ('a', atom)              atom = (kind, operands...) as `Core.Atom`, values by number
  ('ite', c, zero, nonzero) ('match', x, arms) ('call', f, args, rets) ('callIf', c, f, args)
  ('dispatch', x, fs, args, rets) ('ret', vs);
`comp`, each compiled function's code `[(op, [operands])]`, entry, instruction count and certificate cells
(`Cert.locs`, by value number); `stable`, the stable name of each compiler name; `pows`, the powers of `g`
by their `K` bits; `jt`, the jump table's targets by cell. Parsed once and cached at `$CORE_MODE_CACHE` (default
this tree's `.lake/core-mode-cache.pkl`), with the digest of what the parse reads (`_inputs`): a cache of other inputs
is parsed again.
"""
import os, sys, re, pickle, glob, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import memo  # noqa: E402,F401  (first: it records what the process reads, `memo.py`)
import compiled  # noqa: E402
BD = compiled.BD
CACHE = os.environ.get('CORE_MODE_CACHE', os.path.join(HERE, '..', '..', '.lake', 'core-mode-cache.pkl'))
sys.setrecursionlimit(1000000)


def _inputs():
    """The digest of what the parse reads: the guest's generated packs and data, the statement's data, and the
    parsing scripts."""
    guest = os.path.join(HERE, '..', '..', 'LeanVM', 'Guest')
    pats = [os.path.join(guest, 'Pack', '*', '*.lean'), os.path.join(guest, 'Data', '*.lean'),
            os.path.join(HERE, '..', '..', '..', 'Statement', 'Data', '*.lean'), os.path.join(HERE, 'coreir.py'),
            os.path.join(HERE, 'compiled.py'), os.path.join(HERE, '..', 'bridge-cert', 'data.py')]
    h = hashlib.sha256()
    for p in sorted(f for pat in pats for f in glob.glob(pat)):
        h.update(os.path.relpath(p, HERE).encode() + b'\0')
        with open(p, 'rb') as fh:
            h.update(hashlib.sha256(fh.read()).digest())
    return h.hexdigest()


def load():
    key = _inputs()
    if os.path.exists(CACHE):
        with open(CACHE, 'rb') as f:
            cached = pickle.load(f)
        if cached.get('key') == key:
            return cached
    texts = BD.core_texts()
    fns, names = {}, {}
    for k, t in texts.items():
        params, body, nm = BD.core_fn(t)
        fns[k] = (params, body)
        names[nm] = k
    md = compiled.load()
    bund = BD.bundles()
    comp = {}
    byns = {m['ns']: m for m in md['fns'].values()}
    for k, b in bund.items():
        m = byns.get(k)
        comp[k] = dict(entry=b['entry'], count=b['count'], locs=b['locs'], plumb=b['plumb'],
                       code=[(op, [int(x) if x.isdigit() else x for x in args]) for op, args in m['code']] if m else None,
                       nargs=m.get('nargs') if m else None)
    out = dict(key=key, core=fns, stable=names, comp=comp, pows=md['pows'], hints=md['hints'], jt=md['jt'],
               core_text_lines={k: t.count('\n') for k, t in texts.items()})
    # written whole, then renamed: generators running at once read a complete cache or none
    tmp = '%s.%d' % (CACHE, os.getpid())
    os.makedirs(os.path.dirname(os.path.abspath(CACHE)), exist_ok=True)
    with open(tmp, 'wb') as f:
        pickle.dump(out, f)
    os.replace(tmp, CACHE)
    return out

