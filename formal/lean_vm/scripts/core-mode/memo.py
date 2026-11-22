"""A computation's result kept with the inputs it read, reused while they are unchanged.

`cached(name, f)`: `f()`, or, when `CORE_MEMO` names a directory and an earlier `f()` stored there read files whose
contents (and directories whose listings) are still the same, its result. While `f` runs, every file it opens and
every directory it lists is recorded with its digest when read: in this process and in its forks (`pmap.py`) through
an audit hook, and in the interpreters it starts that call `follow()` (`fa_past.py`, `route.route_sub`), all through
the log `CORE_MEMO_LOG`. What the process
read before (from `memo`'s import on, `coreir.py` importing it first), the scripts (`scripts/**/*.py`), the guest's
exported data (`Pack/`, `Data/`, the statement's), the parses the environment names and its `CORE_*`, `MODE_*`,
`FRAME_*` variables count as inputs too. So a result is reused only when nothing it read changed: the regeneration's
steps share one computation of the bodies with calls (`callc.results`), of the core route's pairings (`pair.collect`)
and of the route (`route.route_sub`) instead of one each, and a step that wrote a file one read computes it again. A
computation inside another is stored on its own, its inputs the enclosing one's too.
"""
import os
import sys
import glob
import json
import pickle
import hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
FORMAL = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
SCRIPTS = os.path.normpath(os.path.join(HERE, '..'))
_STATE = {'log': None, 'busy': False, 'hooked': False}
# what this process read before a recorded computation, with its digest then: its state may hold any of it
_SEEN = {}


def _hook(event, args):
    if _STATE['busy']:
        return
    rec = None
    if event == 'open':
        path, mode = args[0], args[1]
        if isinstance(path, (str, bytes)) and (mode is None or not any(c in str(mode) for c in 'wax+')):
            rec = ('f', os.path.abspath(os.fsdecode(path)))
    elif event in ('os.listdir', 'os.scandir'):
        p = args[0]
        if isinstance(p, (str, bytes)) or p is None:
            rec = ('d', os.path.abspath(os.fsdecode(p) if p is not None else '.'))
    elif event == 'glob.glob':
        rec = ('g', os.path.abspath(os.fsdecode(args[0])), bool(args[1]))
    if rec is None or _volatile(rec[1]) or not _relevant(rec):
        return
    _STATE['busy'] = True
    try:
        log = _STATE['log']
        if log is None:
            if rec not in _SEEN:
                _SEEN[rec] = _digest_now(rec)
            return
        with open(log, 'a') as fh:
            fh.write(json.dumps([list(rec), _digest_now(rec)]) + '\n')
    finally:
        _STATE['busy'] = False


def _volatile(p):
    """The memo's own files: no computation's input."""
    d = os.environ.get('CORE_MEMO')
    return bool(d) and p.startswith(os.path.abspath(d) + os.sep)


def _install():
    if not _STATE['hooked']:
        sys.addaudithook(_hook)
        _STATE['hooked'] = True


_install()


def follow():
    """In an interpreter a recorded computation started: record into its log too."""
    log = os.environ.get('CORE_MEMO_LOG')
    if log:
        _install()
        _STATE['log'] = log


def _digest(rec):
    h = hashlib.sha256()
    try:
        if rec[0] == 'f':
            if not os.path.isfile(rec[1]):
                return 'none'
            with open(rec[1], 'rb') as fh:
                h.update(fh.read())
        elif rec[0] == 'd':
            h.update('\0'.join(sorted(os.listdir(rec[1]))).encode() if os.path.isdir(rec[1]) else b'none')
        else:
            h.update('\0'.join(sorted(glob.glob(rec[1], recursive=rec[2]))).encode())
    except OSError:
        return 'error'
    return h.hexdigest()


# a file's digest by its size and modification time, for a file read again
_DIGESTS = {}


def _digest_now(rec):
    """`_digest`, a file's kept while its size and modification time are."""
    if rec[0] != 'f':
        return _digest(rec)
    try:
        st = os.stat(rec[1])
        key = (st.st_size, st.st_mtime_ns)
    except OSError:
        return _digest(rec)
    hit = _DIGESTS.get(rec[1])
    if hit is None or hit[0] != key:
        hit = _DIGESTS[rec[1]] = (key, _digest(rec))
    return hit[1]


def _relevant(rec):
    p = rec[1]
    return not (p.startswith(('/usr/', '/proc/', '/dev/', '/sys/', '/etc/')) or '__pycache__' in p or
                p.endswith('.pyc') or 'site-packages' in p or '/lib/python' in p)


def _fixed():
    """The inputs every computation has: the scripts and the guest's exported data (`Pack/`, `Data/`, the statement's;
    the core IR's parse, `coreir.py`, is keyed by the digest of what it reads)."""
    lv = os.path.join(FORMAL, 'lean_vm')
    pats = [os.path.join(SCRIPTS, '**', '*.py'), os.path.join(lv, 'LeanVM', 'Guest', 'Pack', '**', '*.lean'),
            os.path.join(lv, 'LeanVM', 'Guest', 'Data', '**', '*.lean'), os.path.join(FORMAL, 'Statement', 'Data', '*.lean')]
    recs = [('f', p) for pat in pats for p in sorted(glob.glob(pat, recursive=True))]
    return recs + [('g', pat, True) for pat in pats]


def _env():
    """The environment's settings, which every computation reads."""
    return json.dumps(sorted((k, v) for k, v in os.environ.items() if k.startswith(('CORE_', 'MODE_', 'FRAME_'))
                             and k not in ('CORE_MEMO', 'CORE_MEMO_LOG', 'CORE_MODE_JOBS')))


def _lookup(d, name, env):
    for p in sorted(glob.glob(os.path.join(d, name + '.*.pkl'))):
        try:
            with open(p, 'rb') as fh:
                entry = pickle.load(fh)
        except Exception:
            continue
        if entry['env'] == env and all(_digest_now(r) == h for r, h in entry['deps']):
            return entry
    return None


def _append(log, deps):
    _STATE['busy'] = True
    try:
        with open(log, 'a') as fh:
            for r, h in deps:
                fh.write(json.dumps([list(r), h]) + '\n')
    finally:
        _STATE['busy'] = False


def _read_log(log, deps):
    """The log's records into `deps`, each at its first digest."""
    with open(log) as fh:
        for line in fh:
            r, h = json.loads(line)
            deps.setdefault(tuple(r), h)


def cached(name, f):
    d = os.environ.get('CORE_MEMO')
    if not d:
        return f()
    os.makedirs(d, exist_ok=True)
    env = _env()
    outer = _STATE['log']
    _STATE['log'] = None
    _STATE['busy'] = True
    try:
        entry = _lookup(d, name, env)
        # the inputs every computation has, digested before it runs
        deps = None if entry is not None else {r: _digest_now(r) for r in _fixed() if _relevant(r)}
    finally:
        _STATE['busy'] = False
        _STATE['log'] = outer
    if entry is not None:
        if outer is not None:
            # inside a recorded computation: this one's inputs are its inputs
            _append(outer, entry['deps'])
        return entry['result']
    log = os.path.join(d, '%s.%d.log' % (name, os.getpid()))
    open(log, 'w').close()
    _install()
    old = os.environ.get('CORE_MEMO_LOG')
    os.environ['CORE_MEMO_LOG'] = log
    _STATE['log'] = log
    try:
        result = f()
    finally:
        _STATE['log'] = outer
        if old is None:
            del os.environ['CORE_MEMO_LOG']
        else:
            os.environ['CORE_MEMO_LOG'] = old
    # what this process read before, in the enclosing computation too: its state may hold any of it
    for r, h in _SEEN.items():
        deps.setdefault(r, h)
    _read_log(log, deps)
    if outer is not None:
        _read_log(outer, deps)
    os.remove(log)
    deps = sorted(deps.items())
    if outer is not None:
        _append(outer, deps)
    tmp = os.path.join(d, '%s.%d.tmp' % (name, os.getpid()))
    with open(tmp, 'wb') as fh:
        pickle.dump({'env': env, 'deps': deps, 'result': result}, fh)
    os.replace(tmp, os.path.join(d, '%s.%s.pkl' % (name, hashlib.sha256(repr(deps).encode()).hexdigest()[:16])))
    return result
