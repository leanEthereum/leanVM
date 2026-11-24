"""Each residual's family tag (`CoreMode.resFamFrom`, `CoreMode/ResTag.lean`): the first of `resFamG`'s families the
Python twins (`callcres.py`) find it in, `0` (all of them) when they find none or fail. A tag past the first family
that holds fails the kernel's check, never a wrong one.

`tags(k, text)`: the tags of a residual list written as `DataC.lean` writes it (`emitc.lres`)."""
import re
import callcres as CR
import fnrules as R

TOK = re.compile(r'⟨|⟩|\[|\]|\(|\)|,|\.[A-Za-z]+|\d+')


class P:
    def __init__(self, text):
        self.t = TOK.findall(text)
        self.i = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def take(self, want=None):
        x = self.t[self.i]
        if want is not None and x != want:
            raise ValueError(f'restag: {want} expected, {x} found')
        self.i += 1
        return x

    def num(self):
        return int(self.take())

    def cell(self):
        self.take('⟨'); self.take('[')
        bs = []
        while self.peek() != ']':
            self.take('('); b = self.num(); self.take(','); e = self.num(); self.take(')')
            bs.append((b, e))
            if self.peek() == ',':
                self.take(',')
        self.take(']'); self.take(','); off = self.num(); self.take('⟩')
        return (tuple(bs), off)

    def idx(self):
        self.take('(')
        k = self.take()[1:]
        v = self.cell() if k == 'mono' else self.num()
        self.take(')')
        return (k, v)

    def run(self):
        self.take('⟨'); c = self.cell(); self.take(','); s = self.num(); self.take(',')
        lo = self.idx(); self.take(','); hi = self.idx(); self.take('⟩')
        return (c, s, lo, hi)

    def cond(self):
        k = self.take()[1:]
        args = []
        while self.peek() not in (',', ']'):
            args.append(self.num())
        return (k, *args)

    def res(self):
        k = self.take()[1:]
        if k == 'under':
            self.take('[')
            cs = []
            while self.peek() != ']':
                cs.append(self.cond())
                if self.peek() == ',':
                    self.take(',')
            self.take(']'); self.take('(')
            r = self.res()
            self.take(')')
            return ('under', cs, r)
        if k == 'lt':
            return ('lt', self.idx(), self.idx())
        if k == 'sub':
            return ('sub', self.cell(), self.run())
        if k == 'subP':
            c = self.cell()
            self.take('[')
            cs = []
            while self.peek() != ']':
                cs.append(self.cell())
                if self.peek() == ',':
                    self.take(',')
            self.take(']')
            return ('subP', c, cs)
        if k == 'subR':
            return ('subR', self.run(), self.run())
        raise ValueError(f'restag: residual .{k}')

    def list(self):
        self.take('[')
        out = []
        while self.peek() != ']':
            out.append(self.res())
            if self.peek() == ',':
                self.take(',')
        self.take(']')
        return out


def tag(k, r, G):
    """`resFamFrom`'s tag of residual `r` of function `k` at its mode signature `G`."""
    try:
        if all(v < CR.I.GB for v in CR.vals(r)):
            if CR.res_fam(k, r, G):
                return 0
            if CR.rc_pts(k, r):
                return 2
            if CR.rc_tab(k, r):
                return 3
            if R.some('fam', k, r) or CR.split_fam(k, r):
                return 4
        return 5
    except Exception:
        return 0


def tags(k, text, G):
    """The tags of the residual list `text` of function `k`; `None` if it does not parse."""
    try:
        rs = P(text).list()
    except (ValueError, IndexError):
        return None
    return [tag(k, r, G) for r in rs]
