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
  KERNEL_WIN, HEAP_WIN, CORE_WIN, PAIR_WIN, FRAME_WIN: functions checked in windows, and their window sizes
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
"""
import os, re, sys, glob, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
FN = os.path.join(HERE, 'fn')
SOURCE = os.path.join(HERE, '..', '..', 'LeanVM', 'Guest', 'Data', 'Source.lean')
CONSTS = os.path.join(HERE, '..', '..', 'LeanVM', 'Guest', 'Data', 'Consts.lean')

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


# last: a rule file may use the helpers above (`param`, `guest_const`)
MODS = _load()
