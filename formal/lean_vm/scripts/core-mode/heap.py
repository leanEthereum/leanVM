"""Heap certificates of the core IR (`formal/notes/core-mode.md`, milestone 1): inference and measurement.

For every core function with no call and no loop, the pass `CoreMode.heapOk` runs (`LeanVM/Guest/CoreMode/Heap.lean`),
mirrored here step for step, and its certificate (`HCert`) is inferred:

* the reads: the values `d` of the `load d p off` atoms whose word is not defined before them, by the executor's
  solving rules (a forward pass, scoped, met by intersection at joins, as `census.py`'s (a)); every `load` whose
  word is one of them is checked as a read, every other one is a store;
* each read's witness: the most recent write event in scope (a `load` of any kind, or a heap hint's destination
  cell) of the read's cell, or else the precondition of its cell, a cell over the parameters only;
* the cells: a value's monomial is the first of its defining atoms in scope (a constant power of `g`, a product,
  a copy or an `assert ==` either way), a value with none being its own base.

usage (from formal/lean_vm): python3 -I scripts/core-mode/heap.py [--fn NAME] [--fails] [--emit DIR]
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import coreir

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
        return self


def scope_fns():
    return [k for k, (p, b) in CORE.items() if not calls_or_loops(b)]


# ---- Lean output: per pack, the certificates (`CoreMode/Gen/<pack>/Data.lean`) and their checks (`Ok.lean`)

GUEST = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'LeanVM', 'Guest'))
HEADER = '''/-
  LeanVM.Guest.CoreMode.Gen.«{pack}».{mod}

  Generated by `scripts/core-mode/heap.py --emit`; do not edit.
  {what}
-/

module

'''


def pack_of():
    """Each function's pack (`Pack/<pack>/Core*.lean` holds its core, `Core` its definition)."""
    import re, glob
    out = {}
    for p in glob.glob(os.path.join(GUEST, 'Pack', '*', 'Core*.lean')):
        pack = os.path.basename(os.path.dirname(p))
        for m in re.finditer(r'^namespace LeanVM\.Guest\.Fn\.«([^»]+)»$', open(p, encoding='utf-8').read(), re.M):
            out.setdefault(m.group(1), (pack, 'Core'))
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


def lean_cert(f):
    by_d = collections.defaultdict(list)
    for (d, p, off), w in sorted(f.wit.items()):
        by_d[d].append(f'({p}, {off}, {lean_wit(w)})')
    reads = wrap(f'({d}, [{", ".join(rs)}])' for d, rs in sorted(by_d.items()))
    pre = wrap(lean_cell(c) for c in f.pre)
    return (f'  sig := ⟨[{pre}], [], [], [], []⟩\n'
            f'  reads := [{reads}]\n'
            f'  res := []\n')


def emit(out_dir, res):
    packs = collections.defaultdict(list)
    po = pack_of()
    for k in sorted(res):
        if res[k].fail is None:
            packs[po[k]].append(k)
    lines = 0
    mods = []
    for (pack, coremod), ks in sorted(packs.items()):
        d = os.path.join(out_dir, pack)
        os.makedirs(d, exist_ok=True)
        data = HEADER.format(pack=pack, mod='Data', what=f'The heap certificates of `{ks[0]}` and {len(ks) - 1} more.')
        data += 'public import LeanVM.Guest.CoreMode.Defs\n\nset_option maxRecDepth 100000\nset_option linter.all false\n'
        ok = HEADER.format(pack=pack, mod='Ok', what=f'The kernel\'s heap checks of `{ks[0]}` and {len(ks) - 1} more.')
        ok += (f'public import LeanVM.Guest.CoreMode.Heap\npublic import LeanVM.Guest.Data.Pows\n'
               f'public import LeanVM.Guest.Pack.«{pack}».{coremod}\n'
               f'public import LeanVM.Guest.CoreMode.Gen.«{pack}».Data\n\nset_option Elab.async false\n')
        for k in ks:
            data += (f'\nnamespace LeanVM.Guest.Fn.«{k}»\n\n@[expose] public section\n\n'
                     f'/-- `{k}`: its heap certificate. -/\ndef hcert : CoreMode.HCert where\n'
                     f'{lean_cert(res[k])}\nend\nend LeanVM.Guest.Fn.«{k}»\n')
            ok += (f'\nnamespace LeanVM.Guest.Fn.«{k}»\n\n@[expose] public section\n\n'
                   f'/-- `{k}`: the heap check. -/\n'
                   f'theorem heap_ok : CoreMode.heapOk Data.powTree (fun _ ↦ .empty) core hcert = true := by\n'
                   f'  decide +kernel\n\nend\nend LeanVM.Guest.Fn.«{k}»\n')
        for name, text in (('Data', data), ('Ok', ok)):
            with open(os.path.join(d, name + '.lean'), 'w', encoding='utf-8') as fh:
                fh.write(text)
            lines += text.count('\n')
            mods.append(f'LeanVM.Guest.CoreMode.Gen.«{pack}».{name}')
    print(f'emitted {len(packs)} packs, {sum(len(v) for v in packs.values())} functions, {lines} lines')
    return mods


def main():
    only = sys.argv[sys.argv.index('--fn') + 1] if '--fn' in sys.argv else None
    ks = [only] if only else scope_fns()
    res = {k: Fn(k).run() for k in ks}
    if '--emit' in sys.argv:
        mods = emit(sys.argv[sys.argv.index('--emit') + 1], res)
        if '--mods' in sys.argv:
            with open(sys.argv[sys.argv.index('--mods') + 1], 'w') as fh:
                fh.write('\n'.join(mods) + '\n')
    ok = [k for k, f in res.items() if f.fail is None]
    print(f'no call, no loop: {len(ks)} of {len(CORE)}; heapOk passes: {len(ok)}')
    print('  failures by cause:', dict(collections.Counter(f.fail[0] for f in res.values() if f.fail).most_common()))
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
