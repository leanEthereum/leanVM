"""`main`'s rules: its long loop `main_loop2` checked in windows of its own sizes (`windows.py`)."""

# instructions per code window (`core.py`), per pairing window (`pair.py`), per frame walk window (`frame_gen.py`)
CORE_WIN = {'main_loop2': 6144}
PAIR_WIN = {'main_loop2': 2048}
FRAME_WIN = {'main_loop2': 4000}


# ---- its counts (`scripts/count`)

# its loops `Count/Static.lean` bounds per iteration: order, kind, Lean name (`gen.py static`)
STATIC = {'main_loop0': (2, 'loop', 'L1'), 'main_loop1': (3, 'loop', 'L2'), 'main_loop2': (4, 'loop', 'L3'),
          'main_loop3': (5, 'loop', 'L4')}
# `main_loop4`'s frame weight in `VsCountData`: module, order (`vscount.om_names`)
COUNT_OM = {'main_loop4': ('VsCountData', 2)}


def l5_parts(C, k):
    """At the opcode index `k`: `main_loop4`'s frame weight, `Budget.ccA` and `Budget.ccS` (its children's claim
    lists', `child_claim_list_digest`'s `cc_aff`) and `vsCountT` (`verify_sub`'s `vs_counts`), from the `V` counts."""
    import fnrules, vscount
    R = fnrules.MODS
    return ((C.om[k][vscount.L('main_loop4')],) + R['child_claim_list_digest'].cc_aff(C, k)
            + (R['verify_sub'].vs_counts(C, k),))


def count_parts(g, OPS):
    """The heads of the modules of `main_loop4`'s callees' counts (`VsCountData`) and of its `da_verify`'s and
    `claim_list_digest`'s (`MvCountData`), their frame weights, and the latter's report."""
    import fnrules, vscount
    C, L, lst = vscount.cnt(g, 'V'), vscount.L, vscount.lst
    vs = vscount.om_names('VsCountData')
    vsJ = [L(n) for n in vs]
    mvJ = [L(n) for n in vscount.om_names('MvCountData')]

    def out():
        dv, cl = fnrules.MODS['da_verify'], fnrules.MODS['claim_list_digest']
        rows = dv.da_rows()
        for lop, _, k in OPS:
            A, R, P = dv.dv_aff(C, k); cA, cS = cl.cl_aff(C, k)
            print('mvcount %s: da_verify %d + %d/row + %d/padded row (16 rows: %d of exact %d; 32: %d of %d); '
                  'claim list %d + %d/claim' % (lop, A, R, P, A + 16 * R + rows * P, dv.dvW(C, k, 16),
                                               A + 32 * R + rows * P, dv.dvW(C, k, 32), cA, cS))
    return [
        dict(mod='VsCountData', key=2,
             head=(0, 'The instruction counts of `verify_sub`\'s and `child_claim_list_digest`\'s static callees, per opcode.',
                   'public import LeanVM.Guest.Count.StaticV\npublic import LeanVM.Guest.B1.Whir.Names\n'),
             names=['/-- The core indices of %s. -/\ndef omJ : List ℕ := %s\n'
                    % (', '.join('`%s`' % n for n in vs), lst(g.by[n] for n in vsJ)),
                    '/-- Their names. -/\ndef omNames : List String := [%s]\n' % ', '.join('"%s"' % n for n in vsJ)],
             tables=[vscount.opdefl(OPS, 'omT', 'The frame weights of `omNames`.', lambda k: [C.om[k][n] for n in vsJ])],
             check=['  (List.range %d).all (fun i => decide ((coreProgram[omJ.getD i 0]?).map Fn.name = some (omNames.getD i "")) &&\n'
                    '    (B2C.plumbOf (omJ.getD i 0 + 1)).pmax.getD (B2C.opIdx op) 0 == (omT op).getD i 0)' % len(vsJ)]),
        dict(mod='MvCountData', key=2, out=out,
             head=(1, 'The instruction counts of `main`\'s `da_verify`\'s and `claim_list_digest`\'s callees, per opcode.',
                   'public import LeanVM.Guest.Count.StaticV\npublic import LeanVM.Guest.B1.Da.VerifyDefs\n'
                   'public import LeanVM.Guest.B1.Digest.ClaimList\n'),
             names=['/-- The functions whose frames the counts weigh. -/\ndef mvOmNames : List String := %s\n'
                    % vscount.names(mvJ),
                    '/-- Their core indices. -/\ndef mvOmJ : List ℕ := %s\n' % lst(g.by[n] for n in mvJ)],
             tables=[vscount.opdefl(OPS, 'mvOmT', 'The frame weights of `mvOmNames`.', lambda k: [C.om[k][n] for n in mvJ])],
             check=['  (List.range %d).all (fun i => decide ((coreProgram[mvOmJ.getD i 0]?).map Fn.name = some (mvOmNames.getD i "")) &&\n'
                    '    (B2C.plumbOf (mvOmJ.getD i 0 + 1)).pmax.getD (B2C.opIdx op) 0 == (mvOmT op).getD i 0)' % len(mvJ)])]


# ---- its deployed words and instructions (`scripts/count/deployed.py`, `B1.Main.mainWords`, `Budget.mainInstrs`)

def tail_words(W, stable):
    """`B2C.tailN` of `stable`: its header, parameters and self cell and its self frame pointer cells (its bundle's
    `env`), within its frame."""
    import glob, os, re
    n = W.L(stable)
    np_ = len(W.g.fns[W.g.by[n]]['params'])
    for b in sorted(glob.glob(os.path.join(W.g.lv, 'LeanVM', 'Guest', 'Pack', '*', 'Bundle.lean'))):
        parts = open(b, encoding='utf-8').read().split('\nnamespace LeanVM.Guest.Fn.')
        for blk in parts[1:]:
            if blk.split('\n', 1)[0].strip().strip('«»') == stable:
                env = re.search(r'env := \[(.*?)\], fpOne', blk).group(1)
                offs = [int(x) for x in re.findall(r'\((\d+), \(', env)]
                return min(W.fs(n), max([np_ + 3] + [o + 1 for o in offs]))
    raise SystemExit('main.py: no bundle of %s' % stable)


def deployed_value(W, name):
    """`main_loop4`'s parts (`B1.Main.l5A0`, `l5A1`, `l5A2`): its untaken tail's words, and per child its frame, two
    claim lists' constants and the statement's digest, and two claim lists' slopes."""
    if name == 'l5A0':
        return tail_words(W, 'main_loop4')
    if name == 'l5A1':
        return W.fs(W.L('main_loop4')) + 2 * W.v('ccC') + W.SB('statement_digest')
    if name == 'l5A2':
        return W.v('ccS')
    return None


def _deployed(W):
    """`mainWords`' fields and, per opcode, `mainInstrs`' with `verify_sub`'s at each opening arm."""
    import fnrules
    L, fs, SB, SKt, v = W.L, W.fs, W.SB, W.SKt, W.v
    lp = [L('main_loop%d' % i) for i in range(5)]
    # `main`'s frame and buffers (`283` words), `exponent_tables`' (its table's size its own, `B1.expTabN`) and each
    # callee's frame and bound
    base = (fs('main') + 283 + fs('exponent_tables') + fnrules.lean_def_at('B1/Bits/Tables.lean', 'expTabN')
            + 2 * (v('clC') + fs('claim_list_digest')) + fs(lp[0]) + fs(lp[1]) + fs(lp[2]) + fs(lp[3])
            + (v('l5A0') + fs(lp[4])) + (v('agA0') + fs('aggregate_claims'))
            + SB('statement_digest') + fs('statement_digest'))
    # its own loops at `B1.Main.iterK`, their runs' phantoms in the base
    words = [base, v('clS'), 5 + SKt(lp[0]) + SKt(lp[1]), SKt(lp[2]), SKt(lp[3]), v('dvC') + fs('da_verify'),
             v('dvS'), v('dvP'), 53 + v('l5A1') + v('agA1'), v('l5A2')]
    R = fnrules.MODS
    instrs = {}
    for lop, P, k in W.OPS:
        c = W.certs[P]
        st = lambda n: c[n][2][0]
        lpc = lambda n: c[n][3][0]
        agg = c['aggregate_claims']
        aggC, aggD = agg[2][0], sum(a for _, a in agg[2][1])
        jt = W.jt_sets if lop == 'setConstant' else 0
        clA, clS = R['claim_list_digest'].cl_aff(W.C, k)
        dvA, dvR, dvP = R['da_verify'].dv_aff(W.C, k)
        om5, ccA, ccS, vst = l5_parts(W.C, k)
        # `Budget.l5C`: `main_loop4`'s frame, two claim lists' constants, the statement's digest.
        l5C = om5 + 2 * ccA + st('statement_digest')
        instrs[lop] = ([W.g.pm[1][k] + st('exponent_tables') + st('statement_digest') + jt + 2 * clA, clS,
                        lpc(lp[0]) + lpc(lp[1]), lpc(lp[2]), lpc(lp[3]), dvA, dvR, dvP, l5C + aggC + aggD, ccS], vst)
    return words, instrs


def deployed_parts(W):
    """`DeployedC`'s head and `main_loop4`'s parts, and `Deployed`: `deployedBudget`'s words and instructions."""
    import fnrules
    g = W.g
    words, instrs = _deployed(W)
    wlit = '⟨%s, Bvf⟩' % ', '.join(str(x) for x in words)
    body = '''/-- **The deployed budget's words**, `Bvf μ r` for `verify_sub` on a child of announced stack log
`μ` and rate `r`. -/
def deployedWords (Bvf : ℕ → ℕ → ℕ) : End.Linear := %s

/-- **The deployed budget's instructions of each opcode**, `verify_sub`'s on a child of announced
stack log `μ` at its arm `μ - %d` (`Budget.vsCnt`). -/
def deployedInstrs : Opcode → End.Linear
''' % (wlit, g.min_open_log())
    for lop, P, k in W.OPS:
        f, vst = instrs[lop]
        body += '  | .%s => ⟨%s,\n    fun μ _ => [%s].getD (μ - %d) 0⟩\n' % (
            lop, ', '.join(str(x) for x in f), ', '.join(str(x) for x in vst), g.min_open_log())
    body += '''
set_option maxRecDepth 100000 in
/-- **`deployedBudget`'s words.** -/
theorem deployedBudget_words (Bvf : ℕ → ℕ → ℕ) :
    (Budget.deployedBudget Bvf).words = deployedWords Bvf := by
  simp only [Budget.deployedBudget, Budget.mainBudget, mainWords, B1.Main.iterK, deployedWords]
  rw [clC_eq, clS_eq, dvC_eq, dvS_eq, dvP_eq, l5A0_eq, l5A1_eq, l5A2_eq, agA0_eq, agA1_eq]
  congr 1

set_option maxRecDepth 100000 in
/-- **`deployedBudget`'s instructions.** -/
theorem deployedBudget_instrs (Bvf : ℕ → ℕ → ℕ) (op : Opcode) :
    (Budget.deployedBudget Bvf).instrs op = deployedInstrs op := by
  simp only [Budget.deployedBudget, Budget.mainBudget, Budget.mainInstrs]
  cases op <;> simp only [deployedInstrs, mainCounts, kcExp, kcSd, kcL1, kcL2, kcL3, kcL4, kcAggC, kcAggD, kcClA, kcClS, kcDvA, kcDvR, kcDvP, B2C.jtSets] <;> congr 1
'''

    def out():
        print('deployed: words', words, 'l5A1', W.v('l5A1'))
        for lop, _, _ in W.OPS: print('  ', lop, instrs[lop])
    l4 = W.L('main_loop4')
    return [
        dict(mod='DeployedC', key=2,
             head=(3, 'The claim lists\', the children\'s loop\'s and `aggregate_claims`\' words.',
                   'public import LeanVM.Guest.Count.DeployedA2\n'),
             items=[W.thm('l5A0_eq', 'l5A0 B2C.fs', W.v('l5A0'), 'l5A0',
                          ['B2C.fs_tailKey (j := %d) (f := "%s") (by decide +kernel)' % (g.by[l4] + 1, l4)])]),
        dict(mod='DeployedC', key=4, items=[
            W.thm('l5A1_eq', 'l5A1 B2C.fs wSB', W.v('l5A1'), 'l5A1', ['ccC_eq'], fs=[l4], sb=['statement_digest'])]),
        dict(mod='DeployedC', key=5, items=[W.thm('l5A2_eq', 'l5A2 B2C.fs', W.v('l5A2'), 'l5A2 ccS', [],
                                                  fs=fnrules.MODS['child_claim_list_digest'].walk_loops())]),
        dict(mod='Deployed', key=0, out=out,
             head=(4, 'The numbers of the deployed budget: `deployedBudget_words`, `deployedBudget_instrs`.',
                   'public import LeanVM.Guest.Count.DeployedB\npublic import LeanVM.Guest.Count.DeployedC\n'),
             items=[body])]

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = [
    'LeanVM/Guest/B1/Main/**',
    'LeanVM/Guest/Budget/Main.lean',
    'LeanVM/Guest/Budget/MainCount.lean',
    'LeanVM/Guest/Budget/MainExact.lean',
    'LeanVM/Guest/Budget/Instrs.lean',
    'LeanVM/Guest/Budget/Closed.lean',
    'LeanVM/Guest/Budget/ClosedN.lean',
    'LeanVM/Guest/Budget/ClosedP.lean',
    'LeanVM/Guest/Budget/ClosedPE.lean',
    'LeanVM/Guest/Budget/Final.lean',
    'LeanVM/Guest/Budget/FinalP.lean',
    'LeanVM/Guest/Budget/FinalPE.lean',
    'LeanVM/Guest/Budget/Deployed.lean',
    'LeanVM/Guest/Budget/DeployedBudget.lean',
    'LeanVM/Guest/Budget/End.lean',
    'LeanVM/Guest/Budget/L5Count.lean',
    'LeanVM/Guest/Budget/MvCount.lean',
    'LeanVM/Guest/Count/Instances.lean',
]
