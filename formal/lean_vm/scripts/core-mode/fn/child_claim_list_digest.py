"""`child_claim_list_digest`'s rules: its count by its walks' shapes (`scripts/count`, `Budget/L5Count.lean`)."""

# ---- its counts (`scripts/count`)

# counted by its tree's shape in the `V` family; its frame weight in `VsCountData`: module, order
COUNT_SHAPE = {'child_claim_list_digest': 'V'}
COUNT_OM = {'child_claim_list_digest': ('VsCountData', 1)}


def _lists():
    """Its walks' loops (`child_claim_list_any`'s per `CLAIM_BIG` and per `CLAIM_GROUP` claims,
    `child_claim_list_mono`'s), and their last digests by the claims left."""
    import fnrules, vscount
    L, group = vscount.L, fnrules.guest_const('CLAIM_GROUP')
    lp = [L('child_claim_list_any_loop0'), L('child_claim_list_any_loop1'), L('child_claim_list_mono_loop0'),
          L('child_claim_list_mono_loop1')]
    return (lp, ['child_claim_list_last__L%d' % k for k in range(group)],
            ['child_claim_list_mono_last__L%d' % k for k in range(group)])


def cc_aff(C, k):
    """At the opcode index `k`: `Budget.ccA` and `Budget.ccS`, the children's claim lists' digests' constant and
    per-claim slope on either walk, the larger of `child_claim_list_any`'s and `child_claim_list_mono`'s
    (`B1.Main.ccHonest`): the loop per `136` claims by the claims, the loop per `17` at most `7` times and the last
    digest in the constant."""
    import fnrules, vscount
    L = vscount.L
    big, group = fnrules.guest_const('CLAIM_BIG'), fnrules.guest_const('CLAIM_GROUP')
    lp, ccl, ccm = _lists()
    om = C.om[k]
    ccA = (om[L('child_claim_list_digest')] + C.stat(k, 'list_split')
           + max(om[L('child_claim_list_any')], om[L('child_claim_list_mono')])
           + (big // group - 1) * max(C.loop(k, lp[1]), C.loop(k, lp[3]))
           + max(max(C.stat(k, n) for n in ccl), max(C.stat(k, n) for n in ccm)))
    return ccA, -(-max(C.loop(k, lp[0]), C.loop(k, lp[2])) // big)


def count_parts(g, OPS):
    """`VsCountData`'s tables of its callees."""
    import fnrules, vscount
    C, lst, opdef, opdefl = vscount.cnt(g, 'V'), vscount.lst, vscount.opdef, vscount.opdefl
    big, group = fnrules.guest_const('CLAIM_BIG'), fnrules.guest_const('CLAIM_GROUP')
    lp, ccl, ccm = _lists()
    return [
        dict(mod='VsCountData', key=1,
             names=['/-- The core indices of `child_claim_list_last__L{k}`, `k < %d`. -/\ndef cclJ : List ℕ := %s\n'
                    % (group, lst(g.by[n] for n in ccl)),
                    '/-- The core indices of `child_claim_list_mono_last__L{k}`, `k < %d`. -/\ndef ccmJ : List ℕ := %s\n'
                    % (group, lst(g.by[n] for n in ccm)),
                    '/-- The core index of `list_split`. -/\ndef lsJ : ℕ := %d\n' % g.by['list_split'],
                    '/-- The children\'s claim lists\' loops: `child_claim_list_any`\'s per `%d` and per `%d` claims, '
                    '`child_claim_list_mono`\'s. -/\ndef ccLpNames : List String := [%s]\n'
                    % (big, group, ', '.join('"%s"' % n for n in lp)),
                    '/-- Their core indices. -/\ndef ccLpJ : List ℕ := %s\n' % lst(g.by[n] for n in lp)],
             tables=[opdefl(OPS, 'kcCclT', '`child_claim_list_last__L{k}`\'s instructions, by `k`.',
                            lambda k: [C.stat(k, n) for n in ccl]),
                     opdefl(OPS, 'kcCcmT', '`child_claim_list_mono_last__L{k}`\'s instructions, by `k`.',
                            lambda k: [C.stat(k, n) for n in ccm]),
                     opdef(OPS, 'kcLs', '`list_split`\'s instructions.', lambda k: C.stat(k, 'list_split')),
                     opdefl(OPS, 'kcCcLpT', 'The instructions of `ccLpNames` per iteration.',
                            lambda k: [C.loop(k, n) for n in lp])],
             check=['  (List.range %d).all (fun k => kvOkB op (cclJ.getD k 0) ("child_claim_list_last__L" ++ B1.Whir.natStr k) &&\n'
                    '    kvSBJ op (cclJ.getD k 0) == (kcCclT op).getD k 0)' % len(ccl),
                    '  (List.range %d).all (fun k => kvOkB op (ccmJ.getD k 0) ("child_claim_list_mono_last__L" ++ B1.Whir.natStr k) &&\n'
                    '    kvSBJ op (ccmJ.getD k 0) == (kcCcmT op).getD k 0)' % len(ccm),
                    '  kvOkB op lsJ "list_split" && kvSBJ op lsJ == kcLs op',
                    '  (List.range %d).all (fun i => kvOkK op (ccLpJ.getD i 0) (ccLpNames.getD i "") &&\n'
                    '    kvSKJ op (ccLpJ.getD i 0) == (kcCcLpT op).getD i 0)' % len(lp)])]


# ---- its deployed words (`scripts/count/deployed.py`, `B1.Main.mainWords`)

def walk_loops():
    """Its walks' loops, the two per `CLAIM_BIG` claims then the two per `CLAIM_GROUP`."""
    lp = _lists()[0]
    return [lp[0], lp[2], lp[1], lp[3]]


def deployed_value(W, name):
    """A child's claim list (`B1.Main.ccC`, `ccS`), on either walk (the honest prover takes the gap walk when the
    list's slots increase): `ccC`, the larger walk's frame, its chain's first record (`15` words at most), the larger
    loops' frames twice and the larger last digests' frames (`ccl`, `ccm`); `ccS`, per claim a record and the larger
    loops' frames per `136` and per `17` claims."""
    import fnrules
    L, fs = W.L, W.fs
    lp, ccl, ccm = _lists()
    if name == 'ccl':
        for n in ccl: assert n in W.g.by, n
        return sum(fs(n) for n in ccl)
    if name == 'ccm':
        return sum(fs(n) for n in ccm)
    if name == 'ccC':
        return (fs(L('child_claim_list_digest')) + 15 + W.SB('list_split')
                + max(fs(L('child_claim_list_any')), fs(L('child_claim_list_mono')))
                + 2 * max(fs(lp[0]), fs(lp[2])) + 2 * max(fs(lp[1]), fs(lp[3])) + max(W.v('ccl'), W.v('ccm')))
    if name == 'ccS':
        big, group = fnrules.guest_const('CLAIM_BIG'), fnrules.guest_const('CLAIM_GROUP')
        return 1 + -(-max(fs(lp[0]), fs(lp[2])) // big) + -(-max(fs(lp[1]), fs(lp[3])) // group)
    return None


def deployed_parts(W):
    """`DeployedA2` (its last digests' frames) and `DeployedC`'s `ccC_eq`."""
    import fnrules
    L = W.L
    group = fnrules.guest_const('CLAIM_GROUP')
    return [
        dict(mod='DeployedA2', key=0,
             head=(1, 'The children\'s claim lists\' last digests\' words over the name lists of `B1.Main.ccC`.',
                   'public import LeanVM.Guest.Budget.DeployedBudget\n'),
             items=['/-- The children\'s claim lists\' last digests\' frames. -/\n'
                    'theorem ccl_sum : nameSum (fun g => B2C.fs g) B1.Digest.cclNames %d = %d := by decide +kernel\n'
                    % (group, W.v('ccl')),
                    '/-- The gap walk\'s last digests\' frames. -/\n'
                    'theorem ccm_sum : nameSum (fun g => B2C.fs g) B1.Digest.mlNames %d = %d := by decide +kernel\n'
                    % (group, W.v('ccm'))]),
        dict(mod='DeployedC', key=1, items=[W.thm(
            'ccC_eq', 'ccC B2C.fs wSB', W.v('ccC'), 'ccC', ['ccl_sum', 'ccm_sum'],
            fs=[L('child_claim_list_digest'), L('child_claim_list_any'), L('child_claim_list_mono')] + walk_loops(),
            sb=['list_split'])])]

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
