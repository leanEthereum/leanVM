"""The guest's static count and words certificate families, generated from the guest data.

    python3 -I scripts/count/gen.py LEAN_VM CMD [--cache DIR]

`LEAN_VM` is the `lean_vm` directory; the data is read from `LeanVM/Guest/Data/` and the modules
written under `LeanVM/Guest/`. `CMD` is one of

* `report`: the coverage, per family, and the bounds of `main`'s callees;
* `words`: `Memory/GuestWords/` and `Memory/GuestWords.lean`, the certificates counting words at
  the deployed frame sizes `B2C.fs`, over every function;
* `cnt`: `Memory/GuestCnt{X,M,S,D,J,K}/`, their tops and `Memory/GuestCntPm.lean`, the
  certificates counting each opcode's instructions at `B2C.ωArm B2C.xmssArmC op` (`pathMax`, and
  `__loop2`'s separately counted arms), over the closure of `ROOTS`;
* `cntv`: `Memory/GuestCntV{X,M,S,D,J,K}/`, their tops and `Memory/GuestCntVPm.lean`, the same
  over the closure of `VROOTS` (`verify_sub`'s statically bounded callees, each child's opening arm
  among them, and `child_claim_list_digest`'s callees);
* `cntw`: `Memory/GuestCntW{X,M,S,D,J,K}/`, their tops and `Memory/GuestCntWPm.lean`, the same
  over the closure of `WROOTS` (`verify_tables`' and `check_opening_terminal`'s statically bounded
  callees, the rounds loop `__loop9`, `shared_selector_tables`' callees and `__loop14`);
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
* `all`: `words`, `cnt`, `static`, `cntv`, `cntw`, `ratiov`, `vscount` and `deployed`.

The checker is `checker.py`, a mirror of `Memory/Static.lean`; `--cache` keeps the parsed core IR.
Build the families' parts one module at a time (each is a few GB)."""
import sys, os, re, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core, checker, writelean, ratio, deployed, vscount

HERE = os.path.dirname(os.path.abspath(__file__))
# (Lean opcode, family letter, index in `Opcode`'s order)
OPS = [('xor', 'X', 0), ('mulNative', 'M', 1), ('setConstant', 'S', 2), ('deref', 'D', 3),
       ('jump', 'J', 4), ('keccak', 'K', 5)]
XMSS = '__loop2'  # leanXMSS's check, inline in __loop2 (lean_ethereum.py:4469-4474)
MAIN_FRAME = 445 + 16322  # B2C.mainFrame
# `main`'s statically bounded callees: the exponent tables, the statement's digest, and its four
# loops (the two duplicate-claim regions, the raw leanXMSS and leanSPHINCS signatures).
CONST_ROOTS = [('Exp', 'exponent_tables'), ('Sd', 'statement_digest')]
LOOP_ROOTS = [('L1', '__loop0'), ('L2', '__loop1'), ('L3', '__loop2'), ('L4', '__loop3')]
AGG = 'aggregate_claims'
ROOTS = [n for _, n in CONST_ROOTS] + [n for _, n in LOOP_ROOTS] + [AGG]
# `verify_sub`'s statically bounded callees (each child's opening arm among them),
# `child_claim_list_digest`'s callees (its two walks' loops and last digests), and the statically bounded callees of `main`'s
# `claim_list_digest` and `da_verify`, whose trees' shapes count them (`vscount.MV_*`): the `V`
# count families (`Memory/GuestCntV*`), apart from `main`'s static callees' so that neither
# family's change rebuilds the other's dependents.
VROOTS = (['open_stacked__L%d' % c for c in range(28)] +
          vscount.VS_ST + ['list_split'] + vscount.CC_LP + ['child_claim_list_last__L%d' % k for k in range(17)] +
          ['child_claim_list_mono_last__L%d' % k for k in range(17)] +
          vscount.MV_ST + vscount.MV_LP + vscount.MV_DL + vscount.MV_CL + vscount.CL_LP)
# `verify_tables`' and `check_opening_terminal`'s statically bounded callees, `verify_tables`' rounds
# loop, `shared_selector_tables`' callees and the terminal's `__loop14`: the `W` count families
# (`Memory/GuestCntW*`), which bound those two callees of `verify_sub` by their trees' shapes.
WROOTS = (['block_selector__L%d' % k for k in range(34)] + ['block_selector_tab__L%d' % k for k in range(34)] +
          ['eq_prefix_run__L%d' % k for k in range(41)] + ['index_mle__L%d' % k for k in range(34)] +
          ['padding_weight__L%d' % k for k in range(29)] + ['plus_one_run__L%d' % k for k in range(34)] +
          ['sel_partial_nibble__L%d' % k for k in range(4)] + ['column_selector__L%d' % k for k in range(29)] +
          ['eq_prefix_chain', 'sumcheck_round4', '__loop9', '__loop8', '__loop14', 'selector_tables',
           'opening_tail_round'])
# `verify_sub`'s callees with no static bound, and the terminal's `__loop14` and
# `ring_switch_weight` (`verify_tables` and the terminal are bounded by their trees' shapes, the `W`
# families), within ratios of their words (`Count/RatioV*`).
RATIOV_ROOTS = [('Vbg', 'verify_bus_gkr'), ('Vk', 'verify_keccak'), ('Vl15', '__loop14'),
                ('Vrsw', 'ring_switch_weight')]
MAIN_CALLEES = ['exponent_tables', 'claim_list_digest', '__loop0', '__loop1', '__loop2', '__loop3',
                'da_verify', '__loop4', AGG, 'statement_digest']


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
        lean = open(os.path.join(lv, 'LeanVM', 'Guest', 'B2C', 'ArmBound.lean'), encoding='utf-8').read()
        m = re.search(r'def xmssArmC \(op : Opcode\) : ℕ := \[([\d, ]*)\]', lean)
        assert m and [int(x) for x in m.group(1).split(',')] == self.C, \
            'B2C.xmssArmC is not %s: update B2C/ArmBound.lean' % self.C
        # `main`'s frame: its cells, then the jump table `__jump_tables` writes (one `SET` per slot).
        bc = open(os.path.join(lv, '..', 'Statement', 'Data', 'Bytecode.lean'), encoding='utf-8').read()
        self.jt_sets = int(re.search(r'⟨"__jump_tables", 0, (\d+),', bc).group(1))
        self.jt_base = self.fsz[1]
        first = re.search(r'def f0c0 : List OffsetInstruction := \[\s*\.set (\d+) ',
                          open(os.path.join(lv, '..', 'Statement', 'Data', 'Bytecode00.lean'), encoding='utf-8').read())
        assert first and int(first.group(1)) == self.jt_base, 'the jump table does not start at main\'s frame size'
        self.main_frame = self.jt_base + self.jt_sets
        defs = open(os.path.join(lv, 'LeanVM', 'Guest', 'B2C', 'Defs.lean'), encoding='utf-8').read()
        assert 'def mainFrame : ℕ := %d + %d\n' % (self.jt_base, self.jt_sets) in defs, \
            'B2C.mainFrame is not %d + %d: update B2C/Defs.lean' % (self.jt_base, self.jt_sets)
        assert 'if op = .setConstant then %d else 0' % self.jt_sets in defs, \
            'B2C.jtSets is not %d: update B2C/Defs.lean' % self.jt_sets

    def family(self, prefix):
        """The specializations `prefix{k}...` of a function, by name."""
        return sorted(n for n in self.by if n.startswith(prefix))

    def min_open_log(self):
        """The smallest stack log the guest opens, `B1.Whir.minOpenLog` (Whir/Interface.lean)."""
        m = re.search(r"^abbrev minOpenLog : ℕ := (\d+)$", open(os.path.join(self.lv, "LeanVM", "Guest", "B1", "Whir", "Interface.lean"),
                      encoding="utf-8").read(), re.M)
        assert m, "no minOpenLog in Whir/Interface.lean"
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


def cmd_words(g):
    fs = g.fs_words()
    cert = g.words_certs()
    gr, mods = writelean.write_lean(g.LD, g.fns, cert, fs, B=1200, alpha=True, fam='GuestWords',
                                    mem=(700, 1500),
                                    pre='w')
    t = tpl('GuestWords.lean').replace('NFNS', str(g.N))
    write_tpl(os.path.join(g.LD, 'GuestWords.lean'), t)
    print('words: certified %d of %d; %d ranges, %d parts' % (len(cert), g.N, len(gr), len(mods)))
    return cert


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


def cmd_cnt(g, V=''):
    """The count families of `main`'s static callees (`V = ''`: `GuestCnt*`, `kw*`, `kc*`), of
    `verify_sub`'s (`V = 'V'`: `GuestCntV*`, `kv*`, `kcv*`) or of `verify_tables`' and the
    terminal's (`V = 'W'`: `GuestCntW*`, `ku*`, `kcu*`)."""
    S, fams = g.cnt_certs({'': None, 'V': VROOTS(g), 'W': WROOTS(g)}[V])
    w = {'': 'kw', 'V': 'kv', 'W': 'ku'}[V]
    kc = {'': 'kc', 'V': 'kcv', 'W': 'kcu'}[V]
    rk = (lambda t: re.sub(r'\bkc(?=[A-Z_])', kc, t)) if V else (lambda t: t)
    for lop, P, k, om, cert in fams:
        gr, mods = writelean.write_lean(g.LD, g.fns, cert, om, B=1200, alpha=False, fam='GuestCnt' + V + P,
                                        pre=w + P.lower(), mem=(700, 1500))
        print('cnt%s %s: certified %d (closure %d); %d ranges, %d parts' % (V, lop, len(cert), len(S), len(gr), len(mods)))
        H = '.'.join(['2'] * k + ['1']) if k < 5 else '.'.join(['2'] * 5)
        t = (tpl('GuestCnt.lean').replace('GuestCnt@P@', 'GuestCnt' + V + '@P@').replace('GuestCntPm', 'GuestCnt' + V + 'Pm')
             .replace('kw@p@', w + '@p@').replace('@P@', P).replace('@p@', P.lower()).replace('@OP@', lop)
             .replace('@K@', str(k)).replace('@H@', H))
        write_tpl(os.path.join(g.LD, 'GuestCnt%s%s.lean' % (V, P)), rk(t))
    defs = []
    top = ntree(sorted(g.by[n] for n in S), 'kcST', defs)
    trees = ''.join('/-- A subtree. -/\ndef %s : NTree ℕ := %s\n\n' % d for d in defs)
    imports = ''.join('public import LeanVM.Guest.Memory.GuestCnt%s%s.Data\n' % (V, P) for _, P, _ in OPS)
    pmat = ' &&\n    '.join('%s%somegaJ j == (B2C.plumbOf (j + 1)).pmax.getD %d 0 + kcArmJ j %d' % (w, P.lower(), k, k)
                           for _, P, k in OPS)
    pmeq = ' ∧\n      '.join('%s%somegaJ j = (B2C.plumbOf (j + 1)).pmax.getD %d 0 + kcArmJ j %d' % (w, P.lower(), k, k)
                             for _, P, k in OPS)
    t = (tpl('GuestCntPm.lean').replace('@IMPORTS@', imports).replace('@TREES@', trees)
         .replace('@KCST@', top).replace('@PMAT@', pmat).replace('@PMEQ@', pmeq)
         .replace('@XJ@', str(g.xj)).replace('@ARMS@', '[' + ', '.join(map(str, g.C)) + ']'))
    if V:
        t = t.replace('LeanVM.Guest.Memory.GuestCntPm', 'LeanVM.Guest.Memory.GuestCnt%sPm' % V).replace(
            "the closure of `main`'s statically bounded callees",
            "the closure of `verify_sub`'s statically bounded callees" if V == 'V' else
            "the closure of `verify_tables`' and `check_opening_terminal`'s statically bounded callees")
    write_tpl(os.path.join(g.LD, 'GuestCnt%sPm.lean' % V), rk(t))
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
    def hcf(P, n, c, pre='kw'):
        p = pre + P.lower() if pre == 'kw' else pre
        return ('(by rw [%scertOf_of_idx (j := %d) (by decide +kernel)]; rfl : %scertOf "%s" = %s)'
                % (p, g.by[n], p, n, lit(c)))
    o = [tpl('Static.lean')]
    for N, n in CONST_ROOTS:
        vals = {}
        for lop, P, k in OPS:
            c = certs[P][n]; assert c[0] == 'stat' and c[1] == [] and c[2][1] == [], (n, c); vals[k] = c[2][0]
        o.append(opdef('kc' + N, '`%s`\'s instructions.' % n, vals))
        s = ('/-- **`%s`\'s instructions.** -/\ntheorem kc%s_weightLe (op : Opcode) :\n'
             '    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) "%s" fun _ => kc%s op := by\n  cases op\n' % (n, N, n, N))
        for lop, P, k in OPS:
            s += '  · exact kw%s_weightLe %s\n' % (P.lower(), hcf(P, n, certs[P][n]))
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
            s += ('  · exact kw%s_weight_le_of_loop %s hn hv hb ha he hae heo\n'
                  '      (fun _ h => (List.not_mem_nil h).elim)\n' % (P.lower(), hcf(P, n, certs[P][n])))
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
        s += '  · have := kw%s_weight_le_of_stat %s hn hv hb hpre\n' % (P.lower(), hcf(P, AGG, certs[P][AGG]))
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


# Functions the words tables index by name (`Count/Words.lean`, `wIdxN`): open_stacked's named
# callees (`B1.osKindTable`) and the static callees of main's non-static ones.
WORDS_PREFIXES = ('opening_round', 'opening_tail_round', 'opening_message__L', 'squeeze_point__L',
                  'squeeze_point_from__L', 'grind_check__L', 'verify_merkle_cap__L',
                  'fold_final_msg__L', 'claim_list_last__L', 'da_levels__L', 'list_split',
                  'batch_sumcheck__L', 'statement_digest', 'exponent_tables', 'gkr_rounds__L',
                  'sel_partial_nibble__L', 'g_power_of_word', 'eq_prefix_chain', 'selector_tables')


def cmd_words_by_name(g, wcert):
    names = sorted(n for n in g.by if n.startswith(WORDS_PREFIXES) and n in wcert)
    loops = sorted((int(n[6:]), g.by[n]) for n in g.by if re.fullmatch(r'__loop\d+', n) and n in wcert)
    tab = ('/-- The core indices of the functions the checks name, by name. -/\n'
           + ratio.wrap('def wIdxN : List (String × ℕ) := [', ['("%s", %d)' % (n, g.by[n]) for n in names]) + '\n\n'
           + '/-- The core indices of the loop helpers `__loop{n}`, by `n`. -/\n'
           + ratio.wrap('def wIdxLoop : List (ℕ × ℕ) := [', ['(%d, %d)' % q for q in loops]) + '\n')
    path = os.path.join(g.lv, 'LeanVM', 'Guest', 'Count', 'Words.lean')
    write_tpl(path, tpl('Words.lean').replace('@TABLES@', tab))
    print('words by name: %d names, %d loops' % (len(names), len(loops)))


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
    ap.add_argument('cmd', choices=['report', 'words', 'cnt', 'cntv', 'cntw', 'static', 'ratiov', 'vscount', 'deployed',
                                    'all'])
    ap.add_argument('--cache', default=None)
    a = ap.parse_args()
    g = G(a.lean_vm, a.cache)
    if a.cmd == 'report': cmd_report(g)
    elif a.cmd == 'words': cmd_words(g)
    elif a.cmd == 'cnt': cmd_cnt(g)
    elif a.cmd == 'cntv': cmd_cnt(g, 'V')
    elif a.cmd == 'cntw': cmd_cnt(g, 'W')
    elif a.cmd == 'static': cmd_static(g)
    elif a.cmd == 'ratiov': ratio.write(g, RATIOV_ROOTS, opdef, fam='RatioV', CH=24, W=450, two=True)
    elif a.cmd == 'vscount':
        vscount.write(g, OPS)
        vscount.write_main(g, OPS)
    elif a.cmd == 'deployed': cmd_deployed(g)
    else:
        w = cmd_words(g)
        _, fams = cmd_cnt(g)
        cmd_static(g, w, fams)
        cmd_cnt(g, 'V')
        cmd_cnt(g, 'W')
        ratio.write(g, RATIOV_ROOTS, opdef, fam='RatioV', CH=24, W=450, two=True)
        vscount.write(g, OPS)
        vscount.write_main(g, OPS)
        cmd_deployed(g, fams)


if __name__ == '__main__':
    main()
