"""Heap certificates of the core IR (`formal/notes/core-mode.md`), the check without calls: inference and measurement.

For every core function with no call and no loop, the pass `CoreMode.heapOk` runs (`LeanVM/Guest/CoreMode/Heap.lean`),
mirrored here step for step, and its certificate (`HCert`) is inferred:

* the reads: the values `d` of the `load d p off` atoms whose word is not defined before them, by the executor's
  solving rules (a forward pass, scoped, met by intersection at joins); every `load` whose
  word is one of them is checked as a read, every other one is a store;
* each read's witness: the most recent write event in scope (a `load` of any kind, or a heap hint's destination
  cell) of the read's cell, or else the precondition of its cell, a cell over the parameters only;
* the cells: a value's monomial is the first of its defining atoms in scope (a constant power of `g`, a product,
  a copy or an `assert ==` either way), a value with none being its own base.

usage (from formal/lean_vm): python3 -I scripts/core-mode/heap.py [--fn NAME] [--fails] [--emit DIR]
  [--check] (with --emit: compare with the tree, write nothing)
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import coreir
import genfiles

D = coreir.load()
CORE, STABLE, POWS = D['core'], D['stable'], dict(D['pows'])


class Fail(Exception):
    pass


def calls_or_loops(body):
    for s in body:
        if s[0] in ('call', 'callIf', 'dispatch'):
            return True
        if s[0] == 'ite' and (calls_or_loops(s[2]) or calls_or_loops(s[3])):
            return True
        if s[0] == 'match' and any(calls_or_loops(a) for a in s[2]):
            return True
    return False


# ---- (a) def-use: which loads are reads (the designation the composition checks against the frame walk)

def reads_of(params, body):
    R = set()

    def atom(Dset, a):
        k = a[0]
        if k == 'const':
            Dset.add(a[1])
        elif k in ('add', 'mul'):
            d, x, y = a[1:]
            kn = [v in Dset for v in (d, x, y)]
            if kn[1] and kn[2]:
                Dset.add(d)
            elif sum(kn) == 2:
                Dset.add([d, x, y][kn.index(False)])
            else:
                Dset.add(d)
        elif k in ('copy', 'assertEq'):
            x, y = a[1:]
            if x in Dset or y in Dset:
                Dset.add(x); Dset.add(y)
        elif k == 'load':
            d = a[1]
            if d not in Dset:
                R.add(tuple(a[1:]))
                Dset.add(d)
        elif k == 'assertNe':
            Dset.add(a[3])
        elif k == 'rangeCheck':
            Dset.add(a[2])
        elif k == 'keccak':
            Dset.update(a[2])
        elif k == 'frameAddr':
            Dset.add(a[1])
        elif k == 'hint':
            h = a[1]
            for dst in hint_stack_dests(h):
                Dset.add(dst)

    def block(Dset, ss):
        for s in ss:
            if Dset is None:
                return None
            if s[0] == 'a':
                atom(Dset, s[1])
            elif s[0] == 'ite':
                outs = [block(set(Dset), s[2]), block(set(Dset), s[3])]
                outs = [o for o in outs if o is not None]
                Dset = set.intersection(*outs) if outs else None
            elif s[0] == 'match':
                outs = [block(set(Dset), a) for a in s[2]]
                outs = [o for o in outs if o is not None]
                Dset = set.intersection(*outs) if outs else None
            elif s[0] == 'ret':
                return None
        return Dset

    block(set(params), body)
    return R


def hint_stack_dests(h):
    k = h[0]
    dst = {'witness': lambda: h[2], 'bits': lambda: h[4], 'bitsExp': lambda: h[3], 'digitsExp': lambda: h[7],
           'windowsExp': lambda: h[5]}.get(k)
    if dst is not None:
        d = dst()
        return list(d[1]) if d[0] == 'stack' else []
    if k == 'limbs':
        return list(h[2])
    if k == 'log2Ceil':
        return [h[4]]
    if k in ('inverse',):
        return [h[2]]
    if k in ('alloc', 'allocDyn'):
        return [h[1]]
    return []


def hint_heap_dest(h):
    """`(ptr, off, len)` of a hint writing heap words (`Hint.heapDest`)."""
    k = h[0]
    idx = {'witness': 2, 'bits': 4, 'bitsExp': 3, 'digitsExp': 7, 'windowsExp': 5}.get(k)
    if idx is None:
        return None
    d = h[idx]
    return (d[1], d[2], d[3]) if d[0] == 'heap' else None


# ---- monomials: sorted tuples of (value, exponent), and an offset

def ins(a, l):
    k, e = a
    for i, (k2, e2) in enumerate(l):
        if k == k2:
            return l[:i] + ((k, e + e2),) + l[i + 1:]
        if k < k2:
            return l[:i] + ((k, e),) + l[i:]
    return l + ((k, e),)


def merge(a, b):
    out = b
    for x in reversed(a):
        out = ins(x, out)
    return out


class Fn:
    """The pass of `heapOk`: env (value -> monomial), scope (write serial -> cell), the next serial."""

    def __init__(self, key, sigs=None):
        self.key = key
        self.params, self.body = CORE[key]
        self.R = reads_of(self.params, self.body)
        self.pre = []          # cells over parameters, in order of first use
        self.wit = {}          # read atom (d, p, off) -> ('ev', n) | ('pre', k)
        self.fail = None
        self.stats = collections.Counter()
        self.nparams = len(self.params)

    def mono(self, env, v):
        return env.get(v, (((v, 1),), 0))

    def cell(self, env, p, off):
        b, o = self.mono(env, p)
        return (b, o + off)

    def witness(self, scope, c):
        for n in sorted(scope, reverse=True):
            if scope[n] == c:
                return ('ev', n)
        if all(b < self.nparams for b, _ in c[0]):
            if c not in self.pre:
                self.pre.append(c)
            return ('pre', self.pre.index(c))
        return None

    def check_read(self, scope, d, c):
        w = self.wit.get(d)
        if w is None:
            w = self.witness(scope, c)
            if w is None:
                self.stats['uncovered'] += 1
                raise Fail(('uncovered', d, c))
            self.wit[d] = w
            self.stats['read-' + w[0]] += 1
            return
        # one witness per read value: it must cover this occurrence too
        if w[0] == 'ev' and scope.get(w[1]) == c:
            return
        if w[0] == 'pre' and self.pre[w[1]] == c:
            return
        raise Fail(('read-twice', d))

    def atom(self, st, a):
        env, scope = st[0], st[1]
        k = a[0]
        if k == 'const':
            d, (l0, l1) = a[1], a[2]
            if d not in env and l1 == 0:
                e = 0 if l0 == 1 else POWS.get(l0)
                if e is not None:
                    env[d] = ((), e)
        elif k == 'mul':
            d, x, y = a[1:]
            if d not in env:
                mx, my = self.mono(env, x), self.mono(env, y)
                env[d] = (merge(mx[0], my[0]), mx[1] + my[1])
        elif k in ('copy', 'assertEq'):
            x, y = a[1:]
            if x not in env:
                env[x] = self.mono(env, y)
            elif y not in env:
                env[y] = env[x]
        elif k == 'load':
            d, p, off = a[1:]
            c = self.cell(env, p, off)
            if (d, p, off) in self.R:
                self.check_read(scope, (d, p, off), c)
            else:
                self.stats['store'] += 1
            scope[st[2]] = c
            st[2] += 1
        elif k == 'hint':
            h = a[1]
            hd = hint_heap_dest(h)
            if hd is not None:
                p, off, n = hd
                for j in range(n):
                    scope[st[2]] = self.cell(env, p, off + j)
                    st[2] += 1
                self.stats['hint-heap'] += 1
            if h[0] == 'log2Ceil' and h[1][0] == 'heap':
                raise Fail(('log2Ceil-heap',))
        elif k == 'frameAddr':
            self.stats['frameAddr'] += 1

    def block(self, st, ss):
        """`st = [env, scope, n]`; returns the state at the block's end (a `ret` ends it)."""
        for s in ss:
            k = s[0]
            if k == 'a':
                self.atom(st, s[1])
            elif k == 'ite':
                n1 = self.block([dict(st[0]), dict(st[1]), st[2]], s[2])[2]
                n2 = self.block([dict(st[0]), dict(st[1]), n1], s[3])[2]
                st = [st[0], st[1], n2]
            elif k == 'match':
                n = st[2]
                for arm in s[2]:
                    n = self.block([dict(st[0]), dict(st[1]), n], arm)[2]
                st = [st[0], st[1], n]
            elif k == 'ret':
                return st
            else:
                raise Fail(('control', k))
        return st

    def run(self):
        try:
            self.block([{}, {}, 0], self.body)
        except Fail as e:
            self.fail = e.args[0]
            if self.fail[0] == 'uncovered':
                self.fail = ('uncovered', self.origin(self.fail[2]))
        return self

    def origin(self, c):
        """The class of an uncovered cell, by what defines its bases."""
        kinds = {self.defkind().get(b, 'param' if b < self.nparams else 'other') for b, _ in c[0]}
        if not c[0]:
            return 'absolute'
        if 'load' in kinds:
            return 'pointer-from-memory'
        if kinds & {'hint', 'add', 'keccak'}:
            return 'data-index'
        if kinds & {'alloc', 'frameAddr'}:
            return 'own-buffer-unwritten'
        return 'other:' + ','.join(sorted(kinds))

    def defkind(self):
        if not hasattr(self, '_dk'):
            dk = {}

            def walk(ss):
                for s in ss:
                    if s[0] == 'a':
                        a = s[1]
                        if a[0] in ('load', 'add', 'mul', 'const', 'copy'):
                            dk.setdefault(a[1], a[0])
                        elif a[0] == 'keccak':
                            for v in a[2]:
                                dk.setdefault(v, 'keccak')
                        elif a[0] == 'frameAddr':
                            dk.setdefault(a[1], 'frameAddr')
                        elif a[0] == 'hint':
                            h = a[1]
                            for v in hint_stack_dests(h):
                                dk.setdefault(v, 'alloc' if h[0] in ('alloc', 'allocDyn') else 'hint')
                    elif s[0] == 'ite':
                        walk(s[2]); walk(s[3])
                    elif s[0] == 'match':
                        for arm in s[2]:
                            walk(arm)
            walk(self.body)
            self._dk = dk
        return self._dk


def scope_fns():
    return [k for k, (p, b) in CORE.items() if not calls_or_loops(b)]


# ---- Lean output: per pack, the certificates (`CoreMode/Gen/<pack>/Data.lean`) and their checks (`Ok.lean`)

GUEST = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'LeanVM', 'Guest'))
HEADER = genfiles.header('core-mode/heap.py --emit')


def pack_of():
    """Each function's pack and the module of it that defines its `core` (`Pack/<pack>/Core*.lean`: a split body's
    parts come first, in no order), `(pack, module)`."""
    import re
    out = {}
    for k, bs in coreir.BD.core_blocks().items():
        has = [(pack, mod) for pack, mod, text in bs if re.search(r'^noncomputable def core : Core\.Fn', text, re.M)]
        out[k] = has[0] if has else bs[0][:2]
    return out


def lean_cell(c):
    return '⟨[' + ', '.join(f'({b}, {e})' for b, e in c[0]) + f'], {c[1]}⟩'


def lean_wit(w):
    return f'.{w[0]} {w[1]}'


def wrap(items, ind='    ', width=100):
    """Comma-separated items, several to a line."""
    lines, cur = [], ''
    for it in items:
        if cur and len(ind) + len(cur) + len(it) + 2 > width:
            lines.append(cur + ',')
            cur = ''
        cur = f'{cur}, {it}' if cur else it
    if cur:
        lines.append(cur)
    return ('\n' + ind).join(lines)


def lean_cert(f, pre=None):
    by_d = collections.defaultdict(list)
    for (d, p, off), w in sorted(f.wit.items()):
        by_d[d].append(f'({p}, {off}, {lean_wit(w)})')
    reads = wrap(f'({d}, [{", ".join(rs)}])' for d, rs in sorted(by_d.items()))
    pre = wrap(lean_cell(c) for c in (f.pre if pre is None else pre))
    return (f'  sig := {{ pre := [{pre}] }}\n'
            f'  reads := [{reads}]\n'
            f'  res := []\n')


def emit(out_dir, res, check=False):
    """Each pack's `Data.lean` and `Ok.lean` under `out_dir`, a pack with no function left removed (`check`: compared,
    nothing written)."""
    import glob
    packs = collections.defaultdict(list)
    po = pack_of()
    import route
    R = route.route_sub()
    for k in sorted(res):
        if res[k].fail is None:
            packs[po[k]].append(k)
    files = {}
    for (pack, coremod), ks in sorted(packs.items()):
        d = os.path.join(out_dir, pack)
        data = HEADER(f'LeanVM.Guest.CoreMode.Gen.«{pack}».Data',
                      f'The heap certificates of `{ks[0]}` and {len(ks) - 1} more.')
        data += 'public import LeanVM.Guest.CoreMode.Defs\n\nset_option maxRecDepth 100000\nset_option linter.all false\n'
        ok = HEADER(f'LeanVM.Guest.CoreMode.Gen.«{pack}».Ok',
                    f'The kernel\'s heap checks of `{ks[0]}` and {len(ks) - 1} more.')
        ok += (f'public import LeanVM.Guest.CoreMode.Heap\npublic import LeanVM.Guest.CoreMode.Pows.«{pack}»\n'
               f'public import LeanVM.Guest.Pack.«{pack}».{coremod}\n'
               f'public import LeanVM.Guest.CoreMode.Gen.«{pack}».Data\n\nset_option Elab.async false\n')
        oks = ''
        for k in ks:
            post = ''
            if k in R:
                cells = wrap(f'({lean_cell(c)}, {lean_wit(w)})' for c, w in R[k]['post'])
                post = (f'\n'
                        f'def hpost : List (CoreMode.CCell × CoreMode.Wit) :=\n  [{cells}]\n')
            data += (f'\nnamespace LeanVM.Guest.Fn.«{k}»\n@[expose] public section\n'
                     f'def hcert : CoreMode.HCert where\n'
                     f'{lean_cert(res[k], R[k]["pre"] if k in R else None)}{post}\nend\nend LeanVM.Guest.Fn.«{k}»\n')
            oks += f'theorem Fn.«{k}».heap_ok : CoreMode.heapOk Fn.«{k}».pows (fun _ ↦ .empty) core hcert = true := by decide +kernel\n'
        ok += '\nset_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest\n\npublic section\n\n' + oks + '\nend\n\nend LeanVM.Guest\n'
        for name, text in (('Data', data), ('Ok', ok)):
            files[os.path.join(d, name + '.lean')] = text
    have = glob.glob(os.path.join(out_dir, '*', 'Data.lean')) + glob.glob(os.path.join(out_dir, '*', 'Ok.lean'))
    stale = genfiles.sync(files, have, check)
    lines = sum(t.count('\n') for t in files.values())
    if check:
        print(f'checked {len(packs)} packs: ' + (f'{len(stale)} stale: {stale[:5]}' if stale else 'up to date'))
        genfiles.fail_if_stale(stale, check)
    else:
        print(f'emitted {len(packs)} packs, {sum(len(v) for v in packs.values())} functions, {lines} lines')


def hc_fns():
    """The functions whose contract is their own heap signature: `hcFlag` true in `callc.py`'s data (checked there,
    by the check with calls, not here)."""
    import glob
    out = set()
    for f in glob.glob(os.path.join(GUEST, 'CoreMode', 'Gen', '*', 'DataC.lean')):
        for blk in open(f, encoding='utf-8').read().split('\nnamespace LeanVM.Guest.Fn.«')[1:]:
            if '\ndef hcFlag : Bool := true\n' in blk:
                out.add(blk.split('»', 1)[0])
    return out


def callc_fns():
    """The straight functions whose certificate `callc.py` writes (`DataC.lean`; there, not here)."""
    import glob
    out = set()
    for f in glob.glob(os.path.join(GUEST, 'CoreMode', 'Gen', '*', 'DataC.lean')):
        for blk in open(f, encoding='utf-8').read().split('\nnamespace LeanVM.Guest.Fn.«')[1:]:
            if '\ndef hcert : CoreMode.HCert' in blk:
                out.add(blk.split('»', 1)[0])
    return out


def main():
    only = sys.argv[sys.argv.index('--fn') + 1] if '--fn' in sys.argv else None
    ks = [only] if only else sorted(set(scope_fns()) - hc_fns() - callc_fns())
    res = {k: Fn(k).run() for k in ks}
    if '--emit' in sys.argv:
        emit(sys.argv[sys.argv.index('--emit') + 1], res, '--check' in sys.argv)
    ok = [k for k, f in res.items() if f.fail is None]
    print(f'no call, no loop: {len(ks)} of {len(CORE)}; heapOk passes: {len(ok)}')
    print('  failures by cause:', dict(collections.Counter(f.fail[0] + (':' + f.fail[1] if f.fail[0] == 'uncovered' else '')
                                                          for f in res.values() if f.fail).most_common()))
    fam = collections.Counter(k.split('__L')[0] for k, f in res.items() if f.fail)
    print('  failures by family:', dict(fam.most_common()))
    st = collections.Counter()
    for f in res.values():
        st.update(f.stats)
    print('  events:', dict(st))
    print('  preconditions:', sum(len(f.pre) for f in res.values() if f.fail is None),
          'witnesses:', sum(len(f.wit) for f in res.values() if f.fail is None))
    if '--fails' in sys.argv or only:
        for k, f in sorted(res.items()):
            if f.fail:
                print(' ', k, f.fail)
    if only:
        f = res[only]
        print(f.pre, f.wit)


if __name__ == '__main__':
    main()
