"""The guest's static count and words certificate families, generated from the guest data.

    python3 -I scripts/count/gen.py LEAN_VM CMD [--cache DIR]

`LEAN_VM` is the `lean_vm` directory; the data is read from `LeanVM/Guest/Data/` and the modules
written under `LeanVM/Guest/`. `CMD` is one of

* `report`: the coverage, per family, and the bounds of the entry function's callees and its loops';
* `callees`: `Memory/GuestCallees.lean` and `Memory/GuestCalleesOk.lean`, every function's name
  and callees' indices, which the families' checks look their call sites up by (`Memory/Family`);
* `words`: `Memory/GuestWords/` and `Memory/GuestWords.lean`, the certificates counting words at
  the deployed frame sizes `B2C.fs`, over every function;
* `cnt`: `Memory/GuestCnt/` and `Memory/GuestCnt.lean`, the certificates counting each opcode's
  instructions at `B2C.ωArm B2C.xmssArmC op` (`pathMax`, and the separately counted arms of the one
  function `Data/CplArms.lean` gives arms), one vector certificate per function (`Memory/StaticVec`),
  over the closure of the static roots and the families' roots (`vscount.roots`);
* `ratiov`: `Count/RatioVData.lean`, `Count/RatioVChk*.lean`, `Count/RatioV.lean`, the counts of
  the functions `RATIOV` lists within ratios of their words;
* `vscount`: `Count/<M>CountData.lean`, `Count/<M>CountChk*.lean`, the `V` and `W` families' counts as
  tables (`vscount.py`, used by `Budget/VsCount.lean`, `Budget/L5Count.lean`, `Budget/MvCount.lean`);
* `static`: `Count/Static.lean`, the bounds of the static roots the families give, per opcode and in words,
  and `Count/Words.lean`, every function's words by name (`wSB`, `wSK`; `Count/Instances.lean`
  instantiates the budget's hypotheses with them);
* `deployed`: `Count/Deployed*.lean`, the numbers of `Budget.deployedBudget Bv` (`deployed.py`);
* `all`: `callees`, `words`, `cnt`, `static`, `ratiov`, `vscount` and `deployed`.

The functions are named by the rule files `scripts/core-mode/fn/<f>.py` (`fnrules`, read through `vscount`), as
tables by stable name (`STATIC`: the entry function's statically bounded callees, `RATIOV`, `COUNT_SHAPE`,
`RATIO_WORDS`, `COUNT_OM`) and hooks (`count_arms`, `count_static`, `count_walk`, `count_words_by_name`,
`count_parts`); this module names none.

The checker is `checker.py`, a mirror of `Memory/Static.lean`; `--cache` keeps the parsed core IR.
"""
import sys, os, re, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core, checker, writelean, ratio, deployed, vscount, family

HERE = os.path.dirname(os.path.abspath(__file__))
# (Lean opcode, family letter, index in `Opcode`'s order)
OPS = [('xor', 'X', 0), ('mulNative', 'M', 1), ('setConstant', 'S', 2), ('deref', 'D', 3),
       ('jump', 'J', 4), ('keccak', 'K', 5)]


def static_roots():
    """The statically bounded callees of the entry function `Count/Static.lean` bounds (`STATIC`), in order, as
    `(core name, kind, Lean name)`: `const`, `loop` or a kind its rule file's `count_static` writes."""
    return vscount.ordered('STATIC')


def static_names():
    return [n for n, _, _ in static_roots()]


def ratiov_roots():
    """The functions `Count/RatioV*` counts within ratios of their words (`RATIOV`), in order, as `(Lean name, core
    name)`."""
    return [(N, n) for n, N in vscount.ordered('RATIOV')]


def fam_roots(g):
    """Every family's certificates' roots (`vscount.roots`)."""
    return [n for f in vscount.families() for n in vscount.roots(g, f)]


class G:
    def __init__(self, lv, cache):
        self.lv = lv
        self.D = os.path.join(lv, 'LeanVM', 'Guest', 'Data')
        self.LD = os.path.join(lv, 'LeanVM', 'Guest', 'Memory')
        self.fns = core.load(self.D, cache)
        checker.set_pows(core.load_pows(self.D))
        self.pm = core.load_pmax(self.D)
        self.fsz = core.load_frame_sizes(self.D)
        self.arms = core.load_cpl_arms(self.D)
        self.by = {f['name']: i for i, f in self.fns.items()}
        self.N = len(self.fns)
        assert len(self.pm) == self.N and len(self.fsz) == self.N + 1, 'data out of step'
        js = [j for j, a in enumerate(self.arms) if a]
        assert len(js) == 1, 'one function counts its arms separately, not %s' % js
        self.xj = js[0] - 1  # its core index
        self.xn = self.fns[self.xj]['name']
        self.C = [self.arm_max(k) for k in range(6)]
        lean = open(os.path.join(self.D, 'CplArms.lean'), encoding='utf-8').read()
        m = re.search(r'def armMax : List ℕ := \[([\d, ]*)\]', lean)
        assert m and [int(x) for x in m.group(1).split(',')] == self.C, \
            'Data.armMax (B2C.xmssArmC) is not %s: rerun guest-cert' % self.C
        # The entry function's frame: its cells, then the jump table `__jump_tables` writes (one `SET` per slot).
        bc = open(os.path.join(lv, '..', 'Statement', 'Data', 'Bytecode.lean'), encoding='utf-8').read()
        self.jt_sets = int(re.search(r'⟨"__jump_tables", 0, (\d+),', bc).group(1))
        self.jt_base = self.fsz[1]
        first = re.search(r'def f0c0 : List OffsetInstruction := \[\s*\.set (\d+) ',
                          open(os.path.join(lv, '..', 'Statement', 'Data', 'Bytecode00.lean'), encoding='utf-8').read())
        assert first and int(first.group(1)) == self.jt_base, \
            'the jump table does not start at the entry function\'s frame size'
        self.main_frame = self.jt_base + self.jt_sets
        frames = open(os.path.join(self.D, 'FrameSizes.lean'), encoding='utf-8').read()
        assert 'abbrev mainCells : ℕ := %d\n' % self.jt_base in frames and \
            'abbrev jtSlots : ℕ := %d\n' % self.jt_sets in frames, \
            'Data.mainCells, Data.jtSlots (B2C.mainFrame, B2C.jtSets) are not %d, %d: rerun guest-cert' % (
                self.jt_base, self.jt_sets)

    def family(self, prefix):
        """The specializations `prefix{k}...` of a function, by name."""
        return sorted(n for n in self.by if n.startswith(prefix))

    def min_open_log(self):
        """The smallest stack log the guest opens, `B1.Whir.minOpenLog` (Whir/Split.lean)."""
        m = re.search(r"^abbrev minOpenLog : ℕ := (\d+)$", open(os.path.join(self.lv, "LeanVM", "Guest", "B1", "Whir", "Split.lean"),
                      encoding="utf-8").read(), re.M)
        assert m, "no minOpenLog in Whir/Split.lean"
        return int(m.group(1))

    def os_names(self):
        """The opening arms, by stack log from the smallest (the rule files' `count_arms`)."""
        return vscount.fnrules.first('count_arms', self)

    def arm_max(self, k):
        """`B2C.costMaxW` of the separately counted function's body at opcode `k`."""
        acs = self.arms[self.xj + 1] if self.xj + 1 < len(self.arms) else []
        def key(x):
            for p in acs:
                if p[0] == x: return max([l[k] if k < len(l) else 0 for l in p[1]] + [0])
            return 0
        def m1(s):
            if s[0] == 'ite': return max(mw(s[2]), mw(s[3]))
            if s[0] == 'match': return key(s[1]) + max([mw(a) for a in s[2]] + [0])
            return 0
        def mw(ss): return sum(m1(s) for s in ss)
        return mw(self.fns[self.xj]['body'])

    def omega_cnt(self, k):
        """`B2C.ωArm B2C.xmssArmC op` by name, `op` the `k`-th opcode."""
        return {f['name']: self.pm[i + 1][k] + (self.C[k] if i == self.xj else 0)
                for i, f in self.fns.items()}

    def fs_words(self):
        """`B2C.fs` by name."""
        return {f['name']: (self.main_frame if i == 0 else max(2, self.fsz[i + 1]))
                for i, f in self.fns.items()}

    def closure(self, roots):
        S = set(); st = list(roots)
        while st:
            n = st.pop()
            if n in S: continue
            S.add(n); st += list(checker.callees(self.fns[self.by[n]]['body'], set()))
        return S

    def words_certs(self):
        return checker.gen(self.fns, self.fs_words(), alpha=True)[1]

    def cnt_certs(self, roots=None):
        S = self.closure(static_names() if roots is None else roots)
        out = []
        for lop, P, k in OPS:
            om = self.omega_cnt(k)
            cert = checker.gen(self.fns, om, only=S)[1]
            miss = sorted(S - set(cert))
            assert not miss, '%s: closure functions not certified: %s' % (lop, miss)
            out.append((lop, P, k, om, cert))
        return S, out


def write_tpl(path, text):
    open(path, 'w', encoding='utf-8').write(text)


def tpl(name):
    return open(os.path.join(HERE, 'templates', name), encoding='utf-8').read()


def fam_cost(fns, cert, i):
    """A function's check's cost if certified: a little, and its body's (`family.walk_cost`); split at a selector
    (`checker.SPLIT`), each arm's too."""
    if fns[i]['name'] not in cert: return 0.05
    sp = split_of(fns, i)
    return 0.1 + family.walk_cost(fns[i]['body']) + (sum(family.walk_cost(arm_of(fns, i, r)) for r in range(sp[1]))
                                                     if sp else 0)


def split_of(fns, i):
    return checker.SPLIT.get(fns[i]['name'])


def arm_of(fns, i, r):
    sp = checker.SPLIT[fns[i]['name']]
    return checker.sel_body(fns[i]['body'], sp[0], r)


def cmd_callees(g):
    family.write_callees(g.LD, g.fns)
    print('callees: %d functions' % g.N)


def cmd_words(g):
    fs = g.fs_words()
    cert = g.words_certs()
    lit = writelean.lean_cert
    data = family.header('LeanVM.Guest.Memory.GuestWords.Data',
                         'The certificates counting words of the guest\'s core IR by index, and the frame sizes.',
                         'public import LeanVM.Guest.Memory.Static\npublic import LeanVM.Guest.Renumber\n')
    data += '\nnamespace LeanVM.Guest.Data\n\nopen LeanVM.Guest.Memory\n\n@[expose] public section\n\n'
    data += family.tree_defs('wcertT', 'Cert', [(i, cert[g.fns[i]['name']]) for i in range(g.N) if g.fns[i]['name'] in cert],
                             lit, 'The certificates, by index.') + '\n'
    data += family.tree_defs('womegaT', 'ℕ', [(i, fs[g.fns[i]['name']]) for i in range(g.N)], str,
                             'The frame sizes, by index.') + '\n'
    data += ('/-- The certificate of function `j`. -/\ndef wcertJ (j : ℕ) : Cert := (wcertT.find j).getD .none\n\n'
             '/-- The frame size of function `j`. -/\ndef womegaJ (j : ℕ) : ℕ := (womegaT.find j).getD 0\n\n'
             'end\nend LeanVM.Guest.Data\n')
    def ctx(j):
        fn = g.fns[j]; c = cert[fn['name']]
        return checker.Ctx(cert, cert_ks(c), fn['params'], fn['name'], True, fs)
    cut = family.Cut('stepS true Data.wcertJ Data.womegaJ', 'Acc.add', 'Acc.zero', 'Acc.add_assoc', 'Data.wcertJ',
                     'chkS_of_run', lambda j: walked(g.fns[j], cert[g.fns[j]['name']]),
                     lambda j, rho, ss: checker.run_range(checker.stmt_step, checker.add, ctx(j), rho, ss),
                     writelean.lean_acc, 'chkS_of_split', lambda j: split_of(g.fns, j), lambda j, r: arm_of(g.fns, j, r))
    rs, mods = family.write_family(g.LD, g.fns, 'GuestWords', 'w', data, 'chkS true Data.wcertJ Data.womegaJ',
                                   lambda i: fam_cost(g.fns, cert, i), RB=40, MB=120,
                                   doc='Every function of the guest\'s core IR passes its check counting words.', cut=cut)
    write_tpl(os.path.join(g.LD, 'GuestWords.lean'), tpl('GuestWords.lean').replace('NFNS', str(g.N)))
    print('words: certified %d of %d; %d ranges, %d parts' % (len(cert), g.N, len(rs), len(mods)))
    return cert


vec = writelean.lean_vec


def certv(cs):
    """The vector certificate of the six opcodes' certificates `cs`, of one shape."""
    c0 = cs[0]
    if c0[0] == 'stat':
        assert all(c[0] == 'stat' and c[1] == c0[1] and c[3] == c0[3] and [k for k, _ in c[2][1]] == [k for k, _ in c0[2][1]]
                   for c in cs), cs
    else:
        assert all(c[0] == 'loop' and c[1] == c0[1] and c[2] == c0[2] and c[4] == c0[4] and
                   [k for k, _ in c[3][1]] == [k for k, _ in c0[3][1]] for c in cs), cs
    return checker.certv(cs)


def lean_certv(cs):
    """The vector certificate of the six opcodes' certificates `cs`, of one shape."""
    c = certv(cs)
    if c[0] == 'stat':
        return '.stat %s %s %s' % (writelean.lean_pairs(c[1]), writelean.lean_affv(c[2]), writelean.lean_ks(c[3]))
    endc = 'none' if c[1] is None else '(some %d)' % c[1]
    return '.loop %s %s %s %s' % (endc, writelean.lean_pairs(c[2]), writelean.lean_affv(c[3]), writelean.lean_ks(c[4]))


def cert_ks(c): return c[3] if c[0] == 'stat' else c[4]


def walked(fn, c):
    """The statements a certificate's check walks (`Cert.walk`): a loop helper's without its tail."""
    return fn['body'][:-2] if c[0] == 'loop' else fn['body']


def ntree(items, name, defs, depth=0):
    if not items: return '.leaf'
    m = len(items) // 2
    k = items[m]
    l = ntree(items[:m], name + 'l', defs, depth + 1)
    r = ntree(items[m + 1:], name + 'r', defs, depth + 1)
    s = '(.node %d %d %s %s)' % (k, k, l, r)
    if depth == 3:
        defs.append((name, s)); return name
    return s


def cmd_cnt(g):
    """The vector family counting each opcode's instructions (`Memory/GuestCnt`), over the closure
    of the static roots and the families' (`fam_roots`)."""
    S, fams = g.cnt_certs(static_names() + fam_roots(g))
    certs = [cert for _, _, _, _, cert in fams]
    oms = [om for _, _, _, om, _ in fams]
    data = family.header('LeanVM.Guest.Memory.GuestCnt.Data',
                         'The certificates counting each opcode\'s instructions of the guest\'s core IR by index, a\n'
                         '  coordinate per opcode in `Opcode`\'s order, and the frames\' weights.',
                         'public import LeanVM.Guest.Memory.StaticVec\npublic import LeanVM.Guest.Renumber\n')
    data += '\nnamespace LeanVM.Guest.Data\n\nopen LeanVM.Guest.Memory\n\n@[expose] public section\n\n'
    items = [(i, g.fns[i]['name']) for i in range(g.N) if g.fns[i]['name'] in S]
    data += family.tree_defs('cntT', 'CertV × Vec', items,
                             lambda n: '%s, %s' % (lean_certv([c[n] for c in certs]), vec([om[n] for om in oms])),
                             'The certificates and frame weights, by index.') + '\n'
    data += ('/-- The certificate of function `j`. -/\n'
             'def cntJ (j : ℕ) : CertV := ((cntT.find j).map (·.1)).getD .none\n\n'
             '/-- The frame weights of function `j`. -/\n'
             'def cntOmJ (j : ℕ) : Vec := ((cntT.find j).map (·.2)).getD []\n\nend\nend LeanVM.Guest.Data\n')
    cv = {n: certv([c[n] for c in certs]) for _, n in items}
    def ctx(j):
        fn = g.fns[j]
        return checker.Ctx(cv, cert_ks(cv[fn['name']]), fn['params'], fn['name'])
    cut = family.Cut('stepV Data.cntJ', 'AccV.add', 'AccV.zero', 'AccV.add_assoc', 'Data.cntJ', 'chkV_of_run',
                     lambda j: walked(g.fns[j], cv[g.fns[j]['name']]),
                     lambda j, rho, ss: checker.run_range(checker.stmt_stepV, checker.addv, ctx(j), rho, ss),
                     writelean.lean_accv, 'chkV_of_split', lambda j: split_of(g.fns, j), lambda j, r: arm_of(g.fns, j, r))
    rs, mods = family.write_family(g.LD, g.fns, 'GuestCnt', 'cnt', data, 'chkV Data.cntJ Data.cntOmJ',
                                   lambda i: fam_cost(g.fns, certs[0], i), RB=40, MB=120,
                                   doc='Every function of the guest\'s core IR passes its check counting instructions.', cut=cut)
    write_tpl(os.path.join(g.LD, 'GuestCnt.lean'),
              tpl('GuestCnt.lean').replace('@XJ@', str(g.xj)).replace('@XN@', g.xn).replace('@ARMS@', vec(g.C)))
    print('cnt: certified %d; %d ranges, %d parts' % (len(S), len(rs), len(mods)))
    return S, fams


def opdef(name, doc, vals):
    s = '/-- %s -/\ndef %s : Opcode → ℕ\n' % (doc, name)
    for lop, _, k in OPS: s += '  | .%s => %d\n' % (lop, vals[k])
    return s


def cmd_static(g, wcert=None, fams=None):
    if wcert is None: wcert = g.words_certs()
    if fams is None: fams = g.cnt_certs()[1]
    certs = {P: cert for _, P, _, _, cert in fams}
    lit = writelean.lean_cert
    ops = {P: lop for lop, P, _ in OPS}
    def hcf(P, n, c, pre='kw'):
        if pre == 'kw':
            return ('(by rw [cntCert_idx (op := .%s) (j := %d) (by decide +kernel)]; rfl : cntCert .%s "%s" = %s)'
                    % (ops[P], g.by[n], ops[P], n, lit(c)))
        return ('(by rw [%scertOf_of_idx (j := %d) (by decide +kernel)]; rfl : %scertOf "%s" = %s)'
                % (pre, g.by[n], pre, n, lit(c)))
    o = [tpl('Static.lean')]
    roots = static_roots()
    for n, kind, N in roots:
        if kind != 'const': continue
        vals = {}
        for lop, P, k in OPS:
            c = certs[P][n]; assert c[0] == 'stat' and c[1] == [] and c[2][1] == [], (n, c); vals[k] = c[2][0]
        o.append(opdef('kc' + N, '`%s`\'s instructions.' % n, vals))
        s = ('/-- **`%s`\'s instructions.** -/\ntheorem kc%s_weightLe (op : Opcode) :\n'
             '    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) "%s" fun _ => kc%s op := by\n  cases op\n' % (n, N, n, N))
        for lop, P, k in OPS:
            s += '  · exact cnt_weightLe %s\n' % hcf(P, n, certs[P][n])
        o.append(s)
    for n, kind, N in roots:
        if kind != 'loop': continue
        vals = {}
        for lop, P, k in OPS:
            c = certs[P][n]
            assert c[0] == 'loop' and c[1] is None and c[2] == [] and c[3][1] == [], (n, c); vals[k] = c[3][0]
        o.append(opdef('kc' + N, '`%s`\'s instructions per iteration.' % n, vals))
        s = ('/-- **`%s`\'s instructions.** -/\ntheorem kc%s_loop (op : Opcode) :\n'
             '    LoopWeightLe (B2C.ωArm B2C.xmssArmC op) "%s" (kc%s op) := by\n'
             '  intro rd t args rets a e hn hv hb ha he hae heo\n  cases op\n' % (n, N, n, N))
        for lop, P, k in OPS:
            s += ('  · exact cnt_weight_le_of_loop %s hn hv hb ha he hae heo\n'
                  '      (fun _ h => (List.not_mem_nil h).elim)\n' % hcf(P, n, certs[P][n]))
        o.append(s)
    for n, kind, N in roots:
        if kind not in ('const', 'loop'):
            o += vscount.fnrules.first('count_static', n, kind, N, certs, OPS, opdef, hcf)
    o.append('/-! ## Words at the frame sizes `B2C.fs` -/\n')
    for n, kind, N in roots:
        if kind != 'const': continue
        c = wcert.get(n)
        if c is None or not (c[0] == 'stat' and c[1] == [] and c[2][1] == []):
            o.append('-- `%s`: no constant words certificate.\n' % n); continue
        o.append('/-- **`%s`**: at most %d words. -/\ntheorem kw%s_totalLe : TotalLe coreProgram B2C.fs "%s" fun _ => %d :=\n'
                 '  fs_totalLe %s\n' % (n, c[2][0], N, n, c[2][0], hcf(None, n, c, 'w')))
    for n, kind, N in roots:
        if kind != 'loop': continue
        c = wcert.get(n)
        if c is None or not (c[0] == 'loop' and c[1] is None and c[2] == [] and c[3][1] == []):
            o.append('-- `%s`: no words certificate per iteration.\n' % n); continue
        o.append('/-- **`%s`**: at most %d words per iteration and its run\'s phantom frame. -/\n'
                 'theorem kw%s_loopRunLe : LoopRunLe B2C.fs "%s" %d :=\n'
                 '  kw_loopRunLe_of %s\n' % (n, c[3][0], N, n, c[3][0], hcf(None, n, c, 'w')))
    o.append('end\nend LeanVM.Guest.Count\n')
    path = os.path.join(g.lv, 'LeanVM', 'Guest', 'Count', 'Static.lean')
    os.makedirs(os.path.dirname(path), exist_ok=True)
    write_tpl(path, '\n'.join(o))
    print('static: wrote', path)
    cmd_words_by_name(g, wcert)


def encS(s):
    """`encS`: the name's UTF-8 bytes as digits in base `2^9`, each shifted by one."""
    k = 0
    for b in reversed(s.encode('utf-8')): k = b + 1 + 512 * k
    return k


def cmd_words_by_name(g, wcert):
    items = sorted((encS(f['name']), i) for i, f in g.fns.items())
    assert len(set(k for k, _ in items)) == len(items)
    tab = (family.tree_defs('wNameT', 'ℕ', items, str, 'Every function\'s core index, by its name\'s `encS`.') + '\n'
           + ''.join(h(g) for h in vscount.fnrules.hooks('count_words_by_name')))
    path = os.path.join(g.lv, 'LeanVM', 'Guest', 'Count', 'Words.lean')
    write_tpl(path, tpl('Words.lean').replace('@TABLES@', tab).replace('NFNS', str(g.N)))
    print('words by name: %d functions' % g.N)


def cmd_deployed(g, fams=None):
    if fams is None: fams = g.cnt_certs()[1]
    deployed.write(g, {P: c for _, P, _, _, c in fams}, OPS)


def show(c):
    if c is None: return '-'
    if c[0] == 'stat':
        b = c[2]
        return ('%d' % b[0]) + (' + %s on pre %s' % (b[1], c[1]) if b[1] or c[1] else '')
    b = c[3]
    return '%d/iter' % b[0] + (' + %s' % b[1] if b[1] else '') + ('' if c[1] is None else ' (end g^%d)' % c[1])


def calls(ss):
    """The callees of the statements `ss`, in order, each once."""
    out = []
    for st in ss:
        if st[0] == 'call': out.append(st[1])
        elif st[0] == 'callIf': out.append(st[2])
        elif st[0] == 'dispatch': out += st[2]
        elif st[0] == 'ite': out += calls(st[2]) + calls(st[3])
        elif st[0] == 'match': out += [c for a in st[2] for c in calls(a)]
    return list(dict.fromkeys(out))


def cmd_report(g):
    wcert = g.words_certs()
    print('functions', g.N, '; %s arms (B2C.xmssArmC):' % g.xn, g.C)
    print('words: certified %d of %d; not: %s' % (len(wcert), g.N,
          [f['name'] for i, f in sorted(g.fns.items()) if f['name'] not in wcert]))
    allc = []
    for lop, P, k in OPS:
        c = checker.gen(g.fns, g.omega_cnt(k))[1]
        allc.append(c)
        print('%s (whole program): certified %d of %d' % (lop, len(c), g.N))
    print('not certified (xor):', [f['name'] for i, f in sorted(g.fns.items()) if f['name'] not in allc[0]])
    S = g.closure(static_names())
    print('closure of the static roots:', len(S))
    # the entry function's callees, then its loops' callees
    body = g.fns[0]['body']
    lps = [st[2] for st in body if st[0] == 'callIf']
    for n in dict.fromkeys(calls(body) + [c for f in lps for c in calls(g.fns[g.by[f]]['body']) if c != f] + [g.xn]):
        print('  %-26s' % n, ' | '.join('%s %s' % (lop[:3], show(allc[k].get(n))) for lop, P, k in OPS),
              '| words', show(wcert.get(n)))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('lean_vm')
    ap.add_argument('cmd', choices=['report', 'callees', 'words', 'cnt', 'static', 'ratiov', 'vscount', 'deployed',
                                    'all'])
    ap.add_argument('--cache', default=None)
    a = ap.parse_args()
    g = G(a.lean_vm, a.cache)
    if a.cmd == 'report': cmd_report(g)
    elif a.cmd == 'words': cmd_words(g)
    elif a.cmd == 'callees': cmd_callees(g)
    elif a.cmd == 'cnt': cmd_cnt(g)
    elif a.cmd == 'static': cmd_static(g)
    elif a.cmd == 'ratiov': ratio.write(g, ratiov_roots(), opdef, fam='RatioV', CH=24, W=450, two=True)
    elif a.cmd == 'vscount':
        vscount.write(g, OPS)
    elif a.cmd == 'deployed': cmd_deployed(g)
    else:
        cmd_callees(g)
        w = cmd_words(g)
        cmd_cnt(g)
        fams = g.cnt_certs()[1]
        cmd_static(g, w, fams)
        ratio.write(g, ratiov_roots(), opdef, fam='RatioV', CH=24, W=450, two=True)
        vscount.write(g, OPS)
        cmd_deployed(g, fams)


if __name__ == '__main__':
    main()
