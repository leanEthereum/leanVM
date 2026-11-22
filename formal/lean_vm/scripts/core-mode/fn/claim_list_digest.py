"""`claim_list_digest`'s rules: its count by its tree's shape (`scripts/count`, `Budget/MvCount.lean`)."""

# ---- its counts (`scripts/count`)

# counted by its tree's shape in the `V` family; its frame weight in `MvCountData`: module, order
COUNT_SHAPE = {'claim_list_digest': 'V'}
COUNT_OM = {'claim_list_digest': ('MvCountData', 2)}

_TAIL = 'claim_list_tail'


def _lp():
    """Its loops, per `CLAIM_BIG` and per `CLAIM_GROUP` claims."""
    import vscount
    return [vscount.L('claim_list_chain_loop0'), vscount.L('claim_list_chain_loop1')]


def _cl(C, k):
    """Its frame's weight and `claim_list_chain`'s, `list_split`'s, its loops' per iteration, `claim_list_tail`'s."""
    import vscount
    om = C.om[k]
    return (om[vscount.L('claim_list_digest')], om[vscount.L('claim_list_chain')], C.stat(k, 'list_split'),
            [C.loop(k, n) for n in _lp()], C.stat(k, _TAIL))


def cl_aff(C, k):
    """Its instructions on `n` claims (`136·bigs + 17·groups + rest`, `list_split`, `groups < 8`) within `A + S · n`:
    the loop per `17` claims at most `7` times and the last digest in the constant, the loop per `136` claims by the
    claims."""
    import fnrules
    big, group = fnrules.guest_const('CLAIM_BIG'), fnrules.guest_const('CLAIM_GROUP')
    om, oc, ls, lp, cl = _cl(C, k)
    return om + ls + oc + (big // group - 1) * lp[1] + cl, -(-lp[0] // big)


def count_parts(g, OPS):
    """`MvCountData`'s tables of its callees and its affine bound."""
    import fnrules, vscount
    C, lst, names, opdef, opdefl = vscount.cnt(g, 'V'), vscount.lst, vscount.names, vscount.opdef, vscount.opdefl
    big, group = fnrules.guest_const('CLAIM_BIG'), fnrules.guest_const('CLAIM_GROUP')
    LP = _lp()
    for k in range(6):
        om, oc, ls, lp, cl = _cl(C, k)
        A, S = cl_aff(C, k)
        assert all(om + (0 if n == 0 else ls + oc + n // big * lp[0] + n % big // group * lp[1] + cl) <= A + S * n
                   for n in range(0, 2 ** 17))
    return [
        dict(mod='MvCountData', key=1,
             names=['/-- The core index of `claim_list_tail`. -/\ndef clTJ : ℕ := %d\n' % g.by[_TAIL],
                    '/-- `claim_list_digest`\'s loops, per `%d` and per `%d` claims. -/\ndef clLpNames : List String := %s\n'
                    % (big, group, names(LP)),
                    '/-- Their core indices. -/\ndef clLpJ : List ℕ := %s\n' % lst(g.by[n] for n in LP)],
             tables=[opdef(OPS, 'kcClT', '`claim_list_tail`\'s instructions.', lambda k: _cl(C, k)[4]),
                     opdefl(OPS, 'kcClLpT', 'The instructions of `clLpNames` per iteration.', lambda k: _cl(C, k)[3])],
             check=['  (kvOkB op clTJ "claim_list_tail" && kvSBJ op clTJ == kcClT op)',
                    '  (List.range %d).all (fun i => kvOkK op (clLpJ.getD i 0) (clLpNames.getD i "") &&\n'
                    '    kvSKJ op (clLpJ.getD i 0) == (kcClLpT op).getD i 0)' % len(LP)]),
        dict(mod='MvCountData', key=4,
             tables=[opdef(OPS, 'kcClA', '`claim_list_digest`\'s instructions on `n` claims within `kcClA + kcClS · n`: '
                           'the constant.', lambda k: cl_aff(C, k)[0]),
                     opdef(OPS, 'kcClS', '`claim_list_digest`\'s instructions: per claim.', lambda k: cl_aff(C, k)[1])])]


# ---- its deployed words (`scripts/count/deployed.py`, `B1.Main.mainWords`)

def deployed_value(W, name):
    """A list of `n = 136·bigs + 17·groups + rest` claims (`groups < 8`), as `B1.Main.clC`/`clS`: `clC`, `claim_list_chain`'s
    frame, the loops' frames (a run's phantom or an untaken call's) and the last digest in the constant; `clS`, per claim a chain record
    (`KECCAK_STATE` words) and a loop iteration per `136` claims, another per `17`."""
    import fnrules
    lp = _lp()
    if name == 'cl':
        assert _TAIL in W.g.by, _TAIL
        return W.SB(_TAIL)
    if name == 'clC':
        return (W.fs(W.L('claim_list_digest')) + fnrules.guest_const('KECCAK_STATE') + W.SB('list_split')
                + W.fs(W.L('claim_list_chain')) + W.fs(lp[0]) + W.fs(lp[1]) + W.v('cl'))
    if name == 'clS':
        big, group = fnrules.guest_const('CLAIM_BIG'), fnrules.guest_const('CLAIM_GROUP')
        return 1 + -(-W.SKt(lp[0]) // big) + -(-W.SKt(lp[1]) // group)
    return None


def deployed_parts(W):
    """`DeployedC`'s `clC_eq` and `clS_eq`."""
    lp = _lp()
    return [dict(mod='DeployedC', key=0, items=[W.thm('clC_eq', 'clC B2C.fs wSB', W.v('clC'), 'clC', [],
                                                      fs=[W.L('claim_list_digest'), W.L('claim_list_chain')] + lp, sb=['list_split', _TAIL])]),
            dict(mod='DeployedC', key=3, items=[W.thm('clS_eq', 'clS B2C.fs wSK', W.v('clS'), 'clS B1.Main.iterK', [],
                                                      fs=lp, sk=lp)])]

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
