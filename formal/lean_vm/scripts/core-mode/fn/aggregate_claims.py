"""`aggregate_claims`' rules: its count, affine in its children (`scripts/count`)."""

# its bound in `Count/Static.lean`, a constant and a slope in `n` (`count_static`): order, kind, Lean name
STATIC = {'aggregate_claims': (6, 'agg', 'Agg')}


def count_static(n, kind, N, certs, OPS, opdef, hcf):
    """`Count/Static.lean`'s `kcAggC`, `kcAggD` and `kcAgg_le`: its instructions on `g^n` within `C + D · n`, from its
    certificates (`certs`, by opcode letter) on the precondition `(0, 0)`."""
    if n != 'aggregate_claims':
        return None
    cv, dv = {}, {}
    for lop, P, k in OPS:
        c = certs[P][n]
        assert c[0] == 'stat' and c[1] == [(0, 0)] and all(q == 0 for q, _ in c[2][1]), c
        cv[k] = c[2][0]; dv[k] = sum(a for _, a in c[2][1])
    o = [opdef('kcAggC', '`aggregate_claims`\' instructions: the constant.', cv),
         opdef('kcAggD', '`aggregate_claims`\' instructions: per unit of `n`.', dv)]
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
    exact ⟨n, preLt_of_lt (by unfold gT; omega) h0, h1, ha⟩
  have hx : argExp args 0 = n := by rw [argExp, ha, logG_spec h1]
  cases op
'''
    for lop, P, k in OPS:
        s += '  · have := cnt_weight_le_of_stat %s hn hv hb hpre\n' % hcf(P, n, certs[P][n])
        s += '    simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hx] at this\n'
        s += '    simp only [kcAggC, kcAggD]; omega\n'
    return o + [s]


# ---- its deployed words (`scripts/count/deployed.py`, `B1.Main.mainWords`)

def _lps():
    import vscount
    return [vscount.L('aggregate_claims_loop%d' % i) for i in range(3)]


def deployed_value(W, name):
    """`agA0`: its frame, `109` words and its callees' words, without a child; `agA1`: its loops' phantoms per child
    (`SKt + fs`), as the base is charged without a child."""
    if name == 'agA0':
        return W.fs(W.L('aggregate_claims')) + 109 + W.SB('batch_sumcheck__L23')
    if name == 'agA1':
        return 18 + sum(W.SK(n) for n in _lps())
    return None


def deployed_parts(W):
    """`DeployedC`'s `agA0_eq` and `agA1_eq`."""
    return [dict(mod='DeployedC', key=6, items=[
        W.thm('agA0_eq', 'agA0 B2C.fs wSB', W.v('agA0'), 'agA0', [], fs=[W.L('aggregate_claims')],
              sb=['batch_sumcheck__L23']),
        W.thm('agA1_eq', 'agA1 B2C.fs wSK', W.v('agA1'), 'agA1 B1.Main.iterK', [], fs=_lps(), sk=_lps())])]

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
