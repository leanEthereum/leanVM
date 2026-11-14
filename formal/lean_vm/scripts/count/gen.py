"""The guest's static count and words certificate families, generated from the guest data.

    python3 -I scripts/count/gen.py LEAN_VM CMD [--cache DIR]

`LEAN_VM` is the `lean_vm` directory; the data is read from `LeanVM/Guest/Data/` and the modules
written under `LeanVM/Guest/`. `CMD` is one of

* `report`: the coverage, per family, and the bounds of `main`'s callees;
* `callees`: `Memory/GuestCallees.lean` and `Memory/GuestCalleesOk.lean`, every function's name
  and callees' indices, which the families' checks look their call sites up by (`Memory/Family`);
* `words`: `Memory/GuestWords/` and `Memory/GuestWords.lean`, the certificates counting words at
  the deployed frame sizes `B2C.fs`, over every function;
* `cnt`: `Memory/GuestCnt/` and `Memory/GuestCnt.lean`, the certificates counting each opcode's
  instructions at `B2C.ωArm B2C.xmssArmC op` (`pathMax`, and `__loop2`'s separately counted arms),
  one vector certificate per function (`Memory/StaticVec`), over the closure of `ROOTS` (`main`'s
  statically bounded callees), `VROOTS` (`verify_sub`'s, each child's opening arm among them, and
  `child_claim_list_digest`'s callees) and `WROOTS` (`verify_tables`' and
  `check_opening_terminal`'s);
* `ratiov`: `Count/RatioVData.lean`, `Count/RatioVChk*.lean`, `Count/RatioV.lean`, the counts of
  `RATIOV_ROOTS` (`verify_sub`'s callees with no static bound but `verify_tables` and the terminal,
  and the terminal's `__loop14` and `ring_switch_weight`) within ratios of their words;
* `vscount`: `Count/VsCountData.lean`, `Count/VsCountChk*.lean`, the `V` families' counts as tables
  (`vscount.py`, used by `Budget/VsCount.lean`, `Budget/L5Count.lean`), and
  `Count/MvCountData.lean`, `Count/MvCountChk*.lean`, those of `main`'s `claim_list_digest` and
  `da_verify` (used by `Budget/MvCount.lean`);
* `static`: `Count/Static.lean`, the bounds of `ROOTS` the families give, per opcode and in words,
  and `Count/Words.lean`, every function's words by name (`wSB`, `wSK`; `Count/Instances.lean`
  instantiates the budget's hypotheses with them);
* `deployed`: `Count/Deployed*.lean`, the numbers of `Budget.deployedBudget Bv` (`deployed.py`);
* `all`: `callees`, `words`, `cnt`, `static`, `ratiov`, `vscount` and `deployed`.

The checker is `checker.py`, a mirror of `Memory/Static.lean`; `--cache` keeps the parsed core IR.
"""
import sys, os, re, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core, checker, writelean, ratio, deployed, vscount, family
from core import L

HERE = os.path.dirname(os.path.abspath(__file__))
# (Lean opcode, family letter, index in `Opcode`'s order)
OPS = [('xor', 'X', 0), ('mulNative', 'M', 1), ('setConstant', 'S', 2), ('deref', 'D', 3),
       ('jump', 'J', 4), ('keccak', 'K', 5)]
XMSS = L('main_loop2')  # leanXMSS's check, inline in __loop2 (lean_ethereum.py)
# `main`'s statically bounded callees: the exponent tables, the statement's digest, and its four
# loops (the two duplicate-claim regions, the raw leanXMSS and leanSPHINCS signatures).
CONST_ROOTS = [('Exp', 'exponent_tables'), ('Sd', 'statement_digest')]
LOOP_ROOTS = [('L1', L('main_loop0')), ('L2', L('main_loop1')), ('L3', L('main_loop2')), ('L4', L('main_loop3'))]
AGG = 'aggregate_claims'
ROOTS = [n for _, n in CONST_ROOTS] + [n for _, n in LOOP_ROOTS] + [AGG]
# `verify_sub`'s statically bounded callees (each child's opening arm among them),
# `child_claim_list_digest`'s callees (its two walks' loops and last digests), and the statically bounded callees of `main`'s
# `claim_list_digest` and `da_verify`, whose trees' shapes count them (`vscount.MV_*`).
def VROOTS(g):
    return (g.os_names() + vscount.vs_st(g) + ['list_split'] + g.family('log2_ceil_in_the_exponent__L') +
            vscount.CC_LP + vscount.CCL + vscount.CCM + vscount.MV_ST + vscount.MV_LP + [vscount.MV_DL] +
            vscount.MV_CL + vscount.CL_LP)
# `verify_tables`' and `check_opening_terminal`'s statically bounded callees, `verify_tables`' rounds
# loop, `shared_selector_tables`' callees and the terminal's `__loop14`, which bound those two
# callees of `verify_sub` by their trees' shapes.
def WROOTS(g):
    return ([n for p in ['block_selector__L', 'block_selector_tab__L', 'eq_prefix_run__L', 'index_mle__L',
                         'padding_weight__L', 'plus_one_run__L', 'sel_partial_nibble__L', 'column_selector__L']
             for n in g.family(p)] +
            ['eq_prefix_chain', 'sumcheck_round4', L('verify_tables_loop0'), L('shared_selector_tables_loop0'), L('check_opening_terminal_loop0'), 'selector_tables',
             'opening_tail_round'])
# `verify_sub`'s callees with no static bound, and the terminal's `__loop14` and
# `ring_switch_weight` (`verify_tables` and the terminal are bounded by their trees' shapes, the `W`
# families), within ratios of their words (`Count/RatioV*`).
RATIOV_ROOTS = [('Vbg', 'verify_bus_gkr'), ('Vk', 'verify_keccak'), ('Vl15', L('check_opening_terminal_loop0')),
                ('Vrsw', 'ring_switch_weight')]
# `verify_tables`' callees `Count/VsWords` bounds apart from the others (`vtPairs`).
VT_APART = [L('verify_tables_loop0'), L('shared_selector_tables_loop0'), 'shared_selector_tables']
MAIN_CALLEES = ['exponent_tables', 'claim_list_digest', L('main_loop0'), L('main_loop1'), L('main_loop2'), L('main_loop3'),
                'da_verify', L('main_loop4'), AGG, 'statement_digest']


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
        self.xj = self.by[XMSS]
        for j, a in enumerate(self.arms):
            assert not a or j == self.xj + 1, 'only __loop2 counts arms separately'
        self.C = [self.arm_max(k) for k in range(6)]
        lean = open(os.path.join(self.D, 'CplArms.lean'), encoding='utf-8').read()
        m = re.search(r'def armMax : List ℕ := \[([\d, ]*)\]', lean)
        assert m and [int(x) for x in m.group(1).split(',')] == self.C, \
            'Data.armMax (B2C.xmssArmC) is not %s: rerun guest-cert' % self.C
        # `main`'s frame: its cells, then the jump table `__jump_tables` writes (one `SET` per slot).
        bc = open(os.path.join(lv, '..', 'Statement', 'Data', 'Bytecode.lean'), encoding='utf-8').read()
        self.jt_sets = int(re.search(r'⟨"__jump_tables", 0, (\d+),', bc).group(1))
        self.jt_base = self.fsz[1]
        first = re.search(r'def f0c0 : List OffsetInstruction := \[\s*\.set (\d+) ',
                          open(os.path.join(lv, '..', 'Statement', 'Data', 'Bytecode00.lean'), encoding='utf-8').read())
        assert first and int(first.group(1)) == self.jt_base, 'the jump table does not start at main\'s frame size'
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
        """The opening arms `open_stacked__L{m}`, `m` from `0`."""
        ns = [n for n in self.by if re.fullmatch(r'open_stacked__L\d+', n)]
        out = ['open_stacked__L%d' % m for m in range(len(ns))]
        assert sorted(out) == sorted(ns), ns
        return out

    def arm_max(self, k):
        """`B2C.costMaxW` of `__loop2`'s body at opcode `k`."""
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
        S = self.closure(ROOTS if roots is None else roots)
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
    """A function's check's cost if certified: a little, and its body's (`family.walk_cost`)."""
    if fns[i]['name'] not in cert: return 0.05
    return 0.1 + family.walk_cost(fns[i]['body'])


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
                     writelean.lean_acc)
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
    of `ROOTS`, `VROOTS` and `WROOTS`."""
    S, fams = g.cnt_certs(ROOTS + VROOTS(g) + WROOTS(g))
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
                     writelean.lean_accv)
    rs, mods = family.write_family(g.LD, g.fns, 'GuestCnt', 'cnt', data, 'chkV Data.cntJ Data.cntOmJ',
                                   lambda i: fam_cost(g.fns, certs[0], i), RB=40, MB=120,
                                   doc='Every function of the guest\'s core IR passes its check counting instructions.', cut=cut)
    write_tpl(os.path.join(g.LD, 'GuestCnt.lean'),
              tpl('GuestCnt.lean').replace('@XJ@', str(g.xj)).replace('@ARMS@', vec(g.C)))
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
    for N, n in CONST_ROOTS:
        vals = {}
        for lop, P, k in OPS:
            c = certs[P][n]; assert c[0] == 'stat' and c[1] == [] and c[2][1] == [], (n, c); vals[k] = c[2][0]
        o.append(opdef('kc' + N, '`%s`\'s instructions.' % n, vals))
        s = ('/-- **`%s`\'s instructions.** -/\ntheorem kc%s_weightLe (op : Opcode) :\n'
             '    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) "%s" fun _ => kc%s op := by\n  cases op\n' % (n, N, n, N))
        for lop, P, k in OPS:
            s += '  · exact cnt_weightLe %s\n' % hcf(P, n, certs[P][n])
        o.append(s)
    for N, n in LOOP_ROOTS:
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
    cv, dv = {}, {}
    for lop, P, k in OPS:
        c = certs[P][AGG]
        assert c[0] == 'stat' and c[1] == [(0, 0)] and all(q == 0 for q, _ in c[2][1]), c
        cv[k] = c[2][0]; dv[k] = sum(a for _, a in c[2][1])
    o.append(opdef('kcAggC', '`aggregate_claims`\' instructions: the constant.', cv))
    o.append(opdef('kcAggD', '`aggregate_claims`\' instructions: per unit of `n`.', dv))
    s = '''/-- **`aggregate_claims`' instructions** on `g^n`. -/
theorem kcAgg_le (op : Opcode) : ∀ (rd : Reader) (t : Tree) (args rets : List E) (n : ℕ),
    t.name = "aggregate_claims" → t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      args.getD 0 0 = ofK (addressOfIndex n) → 0 < n → n < 2 ^ 64 - 1 →
        t.weight (B2C.ωArm B2C.xmssArmC op) ≤ kcAggC op + kcAggD op * n := by
  intro rd t args rets n hn hv hb ha h0 h1
  have hpre : ArgsPre [(0, 0)] args := by
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨n, h0, h1, ha⟩
  have hx : argExp args 0 = n := by rw [argExp, ha, logG_ofK h1]
  cases op
'''
    for lop, P, k in OPS:
        s += '  · have := cnt_weight_le_of_stat %s hn hv hb hpre\n' % hcf(P, AGG, certs[P][AGG])
        s += '    simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hx] at this\n'
        s += '    simp only [kcAggC, kcAggD]; omega\n'
    o.append(s)
    o.append('/-! ## Words at the frame sizes `B2C.fs` -/\n')
    for N, n in CONST_ROOTS:
        c = wcert.get(n)
        if c is None or not (c[0] == 'stat' and c[1] == [] and c[2][1] == []):
            o.append('-- `%s`: no constant words certificate.\n' % n); continue
        o.append('/-- **`%s`**: at most %d words. -/\ntheorem kw%s_totalLe : TotalLe coreProgram B2C.fs "%s" fun _ => %d :=\n'
                 '  fs_totalLe %s\n' % (n, c[2][0], N, n, c[2][0], hcf(None, n, c, 'w')))
    for N, n in LOOP_ROOTS:
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
    # `verify_tables`' callees, directly or not, but those `Count/VsWords` bounds apart, by name
    vt = sorted(g.closure(['verify_tables']) - {'verify_tables'} - set(VT_APART))
    tab = (family.tree_defs('wNameT', 'ℕ', items, str, 'Every function\'s core index, by its name\'s `encS`.') + '\n'
           + '/-- `verify_tables`\' callees, directly or not, with their core indices, but those\n'
           + '`Count/VsWords` bounds apart (`VT_APART`). -/\n'
           + ratio.wrap('def vtPairs : List (String × ℕ) := [', ['("%s", %d)' % (n, g.by[n]) for n in vt]) + '\n')
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


def cmd_report(g):
    wcert = g.words_certs()
    print('functions', g.N, '; __loop2 arms (B2C.xmssArmC):', g.C)
    print('words: certified %d of %d; not: %s' % (len(wcert), g.N,
          [f['name'] for i, f in sorted(g.fns.items()) if f['name'] not in wcert]))
    allc = []
    for lop, P, k in OPS:
        c = checker.gen(g.fns, g.omega_cnt(k))[1]
        allc.append(c)
        print('%s (whole program): certified %d of %d' % (lop, len(c), g.N))
    print('not certified (xor):', [f['name'] for i, f in sorted(g.fns.items()) if f['name'] not in allc[0]])
    S = g.closure(ROOTS)
    print('closure of ROOTS:', len(S))
    for n in MAIN_CALLEES + ['verify_sub', 'child_claim_list_digest', XMSS, 'verify_sig_lean_sphincs']:
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
    elif a.cmd == 'ratiov': ratio.write(g, RATIOV_ROOTS, opdef, fam='RatioV', CH=24, W=450, two=True)
    elif a.cmd == 'vscount':
        vscount.write(g, OPS)
        vscount.write_main(g, OPS)
    elif a.cmd == 'deployed': cmd_deployed(g)
    else:
        cmd_callees(g)
        w = cmd_words(g)
        cmd_cnt(g)
        fams = g.cnt_certs()[1]
        cmd_static(g, w, fams)
        ratio.write(g, RATIOV_ROOTS, opdef, fam='RatioV', CH=24, W=450, two=True)
        vscount.write(g, OPS)
        vscount.write_main(g, OPS)
        cmd_deployed(g, fams)


if __name__ == '__main__':
    main()
