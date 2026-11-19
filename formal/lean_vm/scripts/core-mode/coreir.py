"""The guest's core IR and compiled code, read back from the generated data for the core-mode census
(`formal/notes/core-mode.md`). A measurement, not a proof.

`load()` returns a dict: `core`, each core function by stable name, `(params, body)`, statements as tuples
  ('a', atom)              atom = (kind, operands...) as `Core.Atom`, values by number
  ('ite', c, zero, nonzero) ('match', x, arms) ('call', f, args, rets) ('callIf', c, f, args)
  ('dispatch', x, fs, args, rets) ('ret', vs);
`comp`, each compiled function's code `[(op, [operands])]`, entry, instruction count and certificate cells
(`Cert.locs`, by value number); `stable`, the stable name of each compiler name; `pows`, the powers of `g`
by their `K` bits. Parsed once and cached at `$CORE_MODE_CACHE` (default `/tmp/core-mode-cache.pkl`); delete
the cache after a regen.
"""
import os, sys, re, pickle
HERE = os.path.dirname(os.path.abspath(__file__))
import importlib.util


def _by_path(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, '..', rel))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


BD = _by_path('bridge_data', 'bridge-cert/data.py')
CACHE = os.environ.get('CORE_MODE_CACHE', '/tmp/core-mode-cache.pkl')
sys.setrecursionlimit(1000000)


def _val(e):
    return BD.val(e)


def _vals(e, env):
    return [BD.val(x) for x in BD.as_list(e, env)]


def _bool(e):
    return e == ('id', 'true')


def _word(e):
    h, a = BD.head(e)
    assert h == 'word', e
    return (a[0], a[1])


def atom(e, env):
    h, a = BD.head(e)
    k = h[1:]
    if k == 'const':
        return ('const', _val(a[0]), _word(a[1]))
    if k in ('add', 'mul'):
        return (k, _val(a[0]), _val(a[1]), _val(a[2]))
    if k == 'copy':
        return ('copy', _val(a[0]), _val(a[1]))
    if k == 'load':
        return ('load', _val(a[0]), _val(a[1]), a[2])
    if k == 'assertEq':
        return ('assertEq', _val(a[0]), _val(a[1]))
    if k == 'assertNe':
        return ('assertNe', _val(a[0]), _val(a[1]), _val(a[2]))
    if k == 'rangeCheck':
        return ('rangeCheck',) + tuple(_val(x) for x in a[:5])
    if k == 'assertInK':
        return ('assertInK', _val(a[0]), _val(a[1]))
    if k == 'keccak':
        return ('keccak', _vals(a[0], env), _vals(a[1], env), _bool(a[2]), _bool(a[3]))
    if k == 'frameAddr':
        return ('frameAddr', _val(a[0]), _vals(a[1], env))
    if k == 'hint':
        return ('hint', BD.core_hint(a[0], env))
    if k == 'touch':
        return ('touch', _val(a[0]), _val(a[1]))
    raise ValueError(k)


def stmt(e, env):
    h, a = BD.head(e)
    if h == '.atom':
        return ('a', atom(a[0], env))
    if h == '.ite':
        return ('ite', _val(a[0]), block(a[1], env), block(a[2], env))
    if h == '.match_':
        return ('match', _val(a[0]), [block(x, env) for x in BD.as_list(a[1], env)])
    if h == '.call':
        return ('call', a[0][1], _vals(a[1], env), _vals(a[2], env))
    if h == '.callIf':
        return ('callIf', _val(a[0]), a[1][1], _vals(a[2], env))
    if h == '.dispatch':
        return ('dispatch', _val(a[0]), [s[1] for s in BD.as_list(a[1], env)], _vals(a[2], env), _vals(a[3], env))
    if h == '.ret':
        return ('ret', _vals(a[0], env))
    raise ValueError(h)


def block(e, env):
    return [stmt(x, env) for x in BD.as_list(e, env)]


def _fn(text):
    i = text.index('namespace core')
    ds = BD.defs(text[i:])
    cache = {}

    def env(n):
        if n not in cache:
            cache[n] = BD.parse(ds[n])
        return cache[n]
    pm = re.search(r'params := (.*)', text)
    params = _vals(BD.parse(pm.group(1)), env)
    nm = re.search(r'name := "([^"]*)"', text).group(1)
    return params, block(env('body'), env), nm


def _mode_data():
    return _by_path('compiled', 'core-mode/compiled.py').load()


def load():
    if os.path.exists(CACHE):
        with open(CACHE, 'rb') as f:
            return pickle.load(f)
    texts = BD.core_texts()
    fns, names = {}, {}
    for k, t in texts.items():
        params, body, nm = _fn(t)
        fns[k] = (params, body)
        names[nm] = k
    md = _mode_data()
    bund = BD.bundles()
    comp = {}
    byns = {m['ns']: m for m in md['fns'].values()}
    for k, b in bund.items():
        m = byns.get(k)
        comp[k] = dict(entry=b['entry'], count=b['count'], locs=b['locs'], plumb=b['plumb'],
                       code=[(op, [int(x) if x.isdigit() else x for x in args]) for op, args in m['code']] if m else None,
                       nargs=m.get('nargs') if m else None)
    out = dict(core=fns, stable=names, comp=comp, pows=md['pows'], hints=md['hints'], core_text_lines={k: t.count('\n') for k, t in texts.items()})
    # written whole, then renamed: generators running at once read a complete cache or none
    tmp = '%s.%d' % (CACHE, os.getpid())
    with open(tmp, 'wb') as f:
        pickle.dump(out, f)
    os.replace(tmp, CACHE)
    return out


if __name__ == '__main__':
    d = load()
    print(len(d['core']), 'core functions,', len(d['comp']), 'compiled')
