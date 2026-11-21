"""`da_verify`'s rules."""
import fnrules

# runs made up for its reads and its callees' runs (`der`)
FEATURES = {'da_verify': [{'der'}]}

CAPE = 2 ** 62


def sel_bound(k, x):
    """`CoreMode.daGap`: its blob count `n_blob_g`, at most `g^DA_MAX_ROWS`, and gap `gap_g`, below it
    (`EndExec.daV_inst`)."""
    import infer as I
    nb, gap = fnrules.val('da_verify', 'n_blob_g'), fnrules.val('da_verify', 'gap_g')
    if I.callee(k) == 'da_verify' and x in (nb, gap):
        return fnrules.guest_const('DA_MAX_ROWS') + (1 if x == nb else 0)
    return None


def fam(k, r):
    """`CoreMode.daGap`: a residual `e(x) < m`, `sel_bound(k, x) <= m`, under branch conditions."""
    if r[0] == 'under':
        return fam(k, r[2])
    if not (r[0] == 'lt' and r[1][0] == 'val' and r[2][0] == 'num'):
        return False
    B = sel_bound(k, r[1][1])
    return B is not None and B <= r[2][1] < CAPE


# ---- its counts (`scripts/count`)

# counted by its tree's shape in the `V` family (`Budget/MvCount.lean`); its frame weight in `MvCountData`
COUNT_SHAPE = {'da_verify': 'V'}
COUNT_OM = {'da_verify': ('MvCountData', 0)}


def da_rows():
    """The matrix's rows, padding included."""
    return fnrules.guest_const('DA_MAX_ROWS')


def da_levels():
    """The tree over the blob roots."""
    return 'da_levels__L%d_L%d' % (da_rows(), fnrules.guest_const('DA_LOG_MAX_ROWS'))


_ST = ['da_padding', 'da_vector', 'da_weights']


def _dv(C, k):
    """At the opcode index `k`: its constant (its frame, its statically bounded callees but the tree, `da_pad`'s
    frame), its blob loop's and the padding loop's iterations, the tree's instructions."""
    import vscount
    L = vscount.L
    return (C.om[k][L('da_verify')] + sum(C.stat(k, n) for n in _ST) + C.om[k][L('da_pad')],
            [C.loop(k, n) for n in _lp()], C.stat(k, da_levels()))


def _lp():
    import vscount
    return [vscount.L('da_verify_loop0'), vscount.L('da_pad_loop0')]


def dvW(C, k, r):
    """Its instructions on `r` rows, exactly."""
    c, lp, dl = _dv(C, k)
    return c + r * lp[0] + (da_rows() - r) * lp[1] + dl


def dv_aff(C, k):
    """`dvW` within `C + R · r + P · DA_MAX_ROWS` on `r ≤ DA_MAX_ROWS` rows: the constant, the blob loop per row past
    the padding loop, the padding loop and `⌈levels / DA_MAX_ROWS⌉` per row of the padded matrix."""
    c, lp, dl = _dv(C, k)
    # The padding loop runs `DA_MAX_ROWS - r` times: `r · (a - b) + DA_MAX_ROWS · b` charges it exactly.
    return c, max(0, lp[0] - lp[1]), lp[1] + -(-dl // da_rows())


def count_parts(g, OPS):
    """`MvCountData`'s tables of its callees and its affine bound."""
    import vscount
    C, lst, names, opdef, opdefl = vscount.cnt(g, 'V'), vscount.lst, vscount.names, vscount.opdef, vscount.opdefl
    rows, LP, DL = da_rows(), _lp(), da_levels()
    for k in range(6):
        A, R, P = dv_aff(C, k)
        assert all(dvW(C, k, r) <= A + R * r + P * rows for r in range(1, rows + 1))
    return [
        dict(mod='MvCountData', key=0,
             names=['/-- `da_verify`\'s statically bounded callees but the tree over the blob roots. -/\n'
                    'def dvStNames : List String := %s\n' % names(_ST),
                    '/-- Their core indices. -/\ndef dvStJ : List ℕ := %s\n' % lst(g.by[n] for n in _ST),
                    '/-- `da_verify`\'s blob loop and the padding loop. -/\ndef dvLpNames : List String := %s\n' % names(LP),
                    '/-- Their core indices. -/\ndef dvLpJ : List ℕ := %s\n' % lst(g.by[n] for n in LP),
                    '/-- The core index of the tree over the blob roots, `B1.Da.dlTop`. -/\ndef dlJ : ℕ := %d\n' % g.by[DL]],
             tables=[opdefl(OPS, 'kcDvStT', 'The instructions of `dvStNames`.', lambda k: [C.stat(k, n) for n in _ST]),
                     opdefl(OPS, 'kcDvLpT', 'The instructions of `dvLpNames` per iteration.',
                            lambda k: [C.loop(k, n) for n in LP]),
                     opdef(OPS, 'kcDl', 'The instructions of the tree over the blob roots.', lambda k: C.stat(k, DL))],
             check=['  (List.range %d).all (fun i => kvOkB op (dvStJ.getD i 0) (dvStNames.getD i "") &&\n'
                    '    kvSBJ op (dvStJ.getD i 0) == (kcDvStT op).getD i 0)' % len(_ST),
                    '  (List.range %d).all (fun i => kvOkK op (dvLpJ.getD i 0) (dvLpNames.getD i "") &&\n'
                    '    kvSKJ op (dvLpJ.getD i 0) == (kcDvLpT op).getD i 0)' % len(LP),
                    '  (kvOkB op dlJ B1.Da.dlTop && kvSBJ op dlJ == kcDl op)']),
        dict(mod='MvCountData', key=3,
             tables=[opdef(OPS, 'kcDvA', '`da_verify`\'s instructions on `r` rows padded to `DA_MAX_ROWS` within '
                           '`kcDvA + kcDvR · r + kcDvP · DA_MAX_ROWS`: the constant.', lambda k: dv_aff(C, k)[0]),
                     opdef(OPS, 'kcDvR', '`da_verify`\'s instructions: per row.', lambda k: dv_aff(C, k)[1]),
                     opdef(OPS, 'kcDvP', '`da_verify`\'s instructions: per padded row.', lambda k: dv_aff(C, k)[2])])]


# ---- its deployed words (`scripts/count/deployed.py`, `B1.Main.mainWords`)

def deployed_value(W, name):
    """`dlK`: the tree over the blob roots' words per row of the padded matrix; `dvC`: its frame, `da_padding`'s,
    `da_vector`'s and `da_weights`' words, the blob loop's phantom, `da_pad`'s and its loop's phantom (its frame when
    it does not run); `dvS`: per blob, the blob loop's iteration past the padding loop's; `dvP`: per row of the
    padded matrix, the roots (`4`), the padding loop and the tree: each static loop's iteration at `SKt`, its run's
    phantom in the constant."""
    L = W.L
    lp, pad = L('da_verify_loop0'), L('da_pad_loop0')
    if name == 'dlK':
        assert da_levels() in W.g.by, da_levels()
        return -(-W.SB(da_levels()) // da_rows())
    if name == 'dvC':
        return (W.fs(L('da_verify')) + W.fs('da_padding') + W.SB('da_vector') + W.SB('da_weights') + W.fs(lp)
                + W.fs(L('da_pad')) + W.fs(pad))
    if name == 'dvS':
        return max(0, W.SKt(lp) - W.SKt(pad))
    if name == 'dvP':
        return 4 + W.SKt(pad) + W.v('dlK')
    return None


def deployed_parts(W):
    """`DeployedA` (`dlK`) and `DeployedB` (its words)."""
    L = W.L
    lp, pad = L('da_verify_loop0'), L('da_pad_loop0')
    imp0 = 'public import LeanVM.Guest.Budget.DeployedBudget\n'
    return [
        dict(mod='DeployedA', key=0, head=(0, 'The tree over the blob roots\' words per padded row (`B1.Main.dlK`).', imp0),
             items=['/-- The words of the tree over the blob roots, per row of the padded matrix. -/\n'
                    'theorem dlK_eq : dlK wSB = %d := by decide +kernel\n' % W.v('dlK')]),
        dict(mod='DeployedB', key=0, head=(2, '`da_verify`\'s words: its constant, per row and per padded row.',
                                           'public import LeanVM.Guest.Count.DeployedA\n'),
             items=['/-- **`da_verify`\'s constant words.** -/\n'
                    + W.thm('dvC_eq', 'dvC B2C.fs wSB', W.v('dvC'), 'dvC', [],
                            fs=[L('da_verify'), 'da_padding', lp, L('da_pad'), pad], sb=['da_vector', 'da_weights']),
                    '/-- **`da_verify`\'s words per row.** -/\n'
                    + W.thm('dvS_eq', 'dvS B2C.fs wSK', W.v('dvS'), 'dvS B1.Main.iterK', [], fs=[lp, pad], sk=[lp, pad]),
                    '/-- **`da_verify`\'s words per padded row.** -/\n'
                    + W.thm('dvP_eq', 'dvP B2C.fs wSB wSK', W.v('dvP'), 'dvP B1.Main.iterK', ['dlK_eq'], fs=[pad],
                            sk=[pad])])]

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
