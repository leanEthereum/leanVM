module

public import LeanXmss.Statement

@[expose] public section

/-! # The adversary's budget counts every path

`LeanXmss.Security.AdversaryHashQueryBound` bounds the adversary's own hash calls with
`IsQueryBoundP`, on every path of its computation, the paths a consistent oracle never takes
included. `inconsistentBranch` makes two calls on every run (a random oracle answers `[]` the same
twice), yet a third call sits on the branch where the answers differ: it is not bounded by `2`. -/

open OracleComp OracleSpec LeanXmss HashSig

namespace XmssSecurity.QueryBudgetChecks

def inconsistentBranch : OracleComp OracleWorld Unit := do
  let a ← liftM (OracleWorld.query (.inr []))
  let b ← liftM (OracleWorld.query (.inr []))
  if a = b then return ()
  else
    let _ ← liftM (OracleWorld.query (.inr [1]))
    return ()

example : ¬ inconsistentBranch.IsQueryBoundP (fun _ : OracleWorld.Domain => True) 2 := by
  intro h
  have h0 := (isQueryBoundP_query_bind_iff _ _ _ _).mp h
  have h1 := (isQueryBoundP_query_bind_iff _ _ _ _).mp (h0.2 (0 : HashOutput))
  have h2 := h1.2 (1 : HashOutput)
  have hne : (0 : HashOutput) ≠ 1 := by
    intro heq
    have hn := congrArg BitVec.toNat heq
    change 0 = 1 at hn
    omega
  simp only [ite_eq_right hne, ite_true, Nat.reduceSub] at h2
  have h3 := (isQueryBoundP_query_bind_iff _ _ _ _).mp h2
  exact h3.1.elim (fun hfalse => hfalse (by decide)) (Nat.not_lt_zero _)

end XmssSecurity.QueryBudgetChecks
