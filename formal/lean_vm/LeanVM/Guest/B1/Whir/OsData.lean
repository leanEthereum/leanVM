/-
  LeanVM.Guest.B1.Whir.OsData

  The tail of the stacked opening's run, inverted.
-/

module

public import LeanVM.Guest.B1.Whir.OsBody

/-!
# The tail's data (TRIAGE #36)

`os_tailOpen_inv`: the tail's run is `ml - 1` fold rounds from the state's claim and quadratic,
then a closing challenge; the end it returns is the rotated point, the glued weight, the
residual's value and the final claim.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- **The tail, inverted.** -/
theorem os_tailOpen_inv {ml lane : ℕ} (hml : 1 ≤ ml) {s : WhirState} {res : List E} {st : St} {e : WhirEnd}
    {st' : St} (h : Runs (osTailOpen ml lane s res) st e st') :
    ∃ (w1 : WhirState) (chs : List E) (st1 : St),
      Runs (foldRounds (ml - 1) ⟨s.target, s.quad, [], []⟩ []) st (w1, chs) st1 ∧
      e = ⟨(s.folds ++ (chs ++ [challengeOf (sqCv st1.cv)])).drop lane ++
          (s.folds ++ (chs ++ [challengeOf (sqCv st1.cv)])).take lane,
        s.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt (s.folds.drop c.foldStart ++
          (chs ++ [challengeOf (sqCv st1.cv)]))) 0,
        multilinearEval res (chs ++ [challengeOf (sqCv st1.cv)]),
        polyEval w1.quad (challengeOf (sqCv st1.cv))⟩ ∧
      st' = { st1 with cv := sqCv st1.cv } := by
  unfold osTailOpen at h
  obtain ⟨⟨tf, tg⟩, st2, h1, h2⟩ := os_inv_bind h
  obtain ⟨rfl, rfl⟩ := os_inv_ret h2
  rw [show ml = ml - 1 + 1 by omega] at h1
  obtain ⟨w1, chs, st1, hr, he, hs⟩ := os_tail_inv (ml - 1) _ _ _ _ _ h1 ⟨s.target, s.quad, [], []⟩ [] rfl
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨w1, chs, st1, by simpa using hr, rfl, hs⟩

end
end LeanVM.Guest.B1
