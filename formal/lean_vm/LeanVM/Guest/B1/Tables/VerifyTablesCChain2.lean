/-
  LeanVM.Guest.B1.Tables.VerifyTablesCChain2

  `verify_tables`' completeness: the column evaluations and the constraint windows chained.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCChain

/-!
# The evaluations and the tables' terms

`vt_ev_run`: a run of one table's column evaluations, the state absorbing each word in turn
(`cvE`). `vt_phaseD`: statements `4374 ..< 7854`, the first table's `g^τ`, then per table its
evaluations and its constraint window.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- The state before evaluation `j`: the words before it absorbed. -/
def cvE (cv0 : Digest) (ws : ℕ → E) (j : ℕ) : Digest := obsAll cv0 ((List.range j).map ws)

theorem cvE_succ (cv0 : Digest) (ws : ℕ → E) (j : ℕ) : cvE cv0 ws (j + 1) = obsCv (cvE cv0 ws j) (ws j) := by
  rw [cvE, cvE, List.range_succ, List.map_append, List.map_cons, List.map_nil, obsAll_append_one']

/-- The cell holding the state before evaluation `j`. -/
def evSt (j : ℕ) : ℕ := if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13

set_option maxRecDepth 100000 in
theorem ev_nb0 : ∀ j < 26, numBelowB (evVal.getD (0 + j) 0 + 16)
    (Stmt.valsList ((vtPre.drop (evStmt.getD (0 + j) 0)).take 16)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ev_nb1 : ∀ j < 26, numBelowB (evVal.getD (26 + j) 0 + 16)
    (Stmt.valsList ((vtPre.drop (evStmt.getD (26 + j) 0)).take 16)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ev_nb2 : ∀ j < 26, numBelowB (evVal.getD (52 + j) 0 + 16)
    (Stmt.valsList ((vtPre.drop (evStmt.getD (52 + j) 0)).take 16)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ev_nb3 : ∀ j < 26, numBelowB (evVal.getD (78 + j) 0 + 16)
    (Stmt.valsList ((vtPre.drop (evStmt.getD (78 + j) 0)).take 16)) = true := by decide +kernel

theorem ev_nb (j : ℕ) (hj : j < 104) : numBelowB (evVal.getD j 0 + 16)
    (Stmt.valsList ((vtPre.drop (evStmt.getD j 0)).take 16)) = true := by
  rcases (show j < 26 ∨ (26 ≤ j ∧ j < 52) ∨ (52 ≤ j ∧ j < 78) ∨ 78 ≤ j by omega) with h | h | h | h
  · simpa using ev_nb0 j h
  · simpa [show 26 + (j - 26) = j by omega] using ev_nb1 (j - 26) (by omega)
  · simpa [show 52 + (j - 52) = j by omega] using ev_nb2 (j - 52) (by omega)
  · simpa [show 78 + (j - 78) = j by omega] using ev_nb3 (j - 78) (by omega)

theorem ev_tau_lt : ∀ j < 104, evTau.getD j 0 < evVal.getD j 0 ∧ 13 < evTau.getD j 0 ∧
    evSt j + 1 < evVal.getD j 0 ∧ 4651 < evVal.getD j 0 := by decide +kernel

section
variable {rd : Reader}

/-- **A run of one table's evaluations**, from evaluation `j0`, its `g^τ` at `evTau j0`. -/
theorem vt_ev_run (hEv : VtEvComplete) {cur pool cplen g : E} {ws : ℕ → E} {cv0 : Digest}
    (hmem : ∀ j < 104, LoadHolds rd cur j (ws j) ∧ LoadHolds rd pool (5 + j) (ws j)) :
    ∀ (d j0 : ℕ), j0 + d ≤ 104 → (∀ j < d, evStmt.getD (j0 + j) 0 = evStmt.getD j0 0 + 16 * j ∧
      evVal.getD (j0 + j) 0 = evVal.getD j0 0 + 16 * j ∧ evTau.getD (j0 + j) 0 = evTau.getD j0 0) →
    (∀ j < d, LoadHolds rd cplen (5 + (j0 + j)) g) →
    ∀ σ : Val, σ (.n 4651) = cur → σ (.n 13) = pool → σ (.n 14) = cplen → σ (.n (evTau.getD j0 0)) = g →
      (σ (.n (evSt j0)), σ (.n (evSt j0 + 1))) = digestScalars (cvE cv0 ws j0) →
      Completes (coreProgram.Rel rd) rd (evVal.getD j0 0) (evVal.getD j0 0 + 16 * d)
        ((vtPre.drop (evStmt.getD j0 0)).take (16 * d)) σ (fun σ' =>
          (∀ j < d, σ' (.n (evVal.getD (j0 + j) 0)) = ws (j0 + j)) ∧
            (0 < d → (σ' (.n (evVal.getD (j0 + d - 1) 0 + 13)), σ' (.n (evVal.getD (j0 + d - 1) 0 + 14))) =
              digestScalars (cvE cv0 ws (j0 + d))))
  | 0, j0, _, _, _, σ, _, _, _, _, _ => by
    simp only [Nat.mul_zero, Nat.add_zero, List.take_zero]
    exact completes_nil _ _ σ ⟨fun j hj => absurd hj (Nat.not_lt_zero j), fun h => absurd h (Nat.lt_irrefl 0)⟩
  | d + 1, j0, hjd, hcon, hcpl, σ, h4651, h13, h14, htau, hst => by
    have hj0 : j0 < 104 := by omega
    obtain ⟨ht0, -, hst0, hc0⟩ := ev_tau_lt j0 hj0
    have hc1 := hcon 1
    have hs : ∀ j < d, evStmt.getD (j0 + 1 + j) 0 = evStmt.getD (j0 + 1) 0 + 16 * j ∧
        evVal.getD (j0 + 1 + j) 0 = evVal.getD (j0 + 1) 0 + 16 * j ∧
        evTau.getD (j0 + 1 + j) 0 = evTau.getD (j0 + 1) 0 := fun j hj => by
      obtain ⟨a1, b1, c1⟩ := hcon 1 (by omega)
      obtain ⟨a2, b2, c2⟩ := hcon (1 + j) (by omega)
      rw [show j0 + 1 + j = j0 + (1 + j) by omega, a2, b2, c2, a1, b1, c1]
      exact ⟨by omega, by omega, rfl⟩
    have hunit : Completes (coreProgram.Rel rd) rd (evVal.getD j0 0) (evVal.getD j0 0 + 16)
        ((vtPre.drop (evStmt.getD j0 0)).take 16) σ (fun σ' =>
          σ' (.n (evVal.getD j0 0)) = ws j0 ∧ σ' (.n (evVal.getD j0 0 + 15)) = ws j0 ∧
            (σ' (.n (evVal.getD j0 0 + 13)), σ' (.n (evVal.getD j0 0 + 14))) =
              digestScalars (obsCv (cvE cv0 ws j0) (ws j0))) :=
      hEv j0 hj0 rd σ cur pool cplen (ws j0) g (cvE cv0 ws j0) h4651 h13 h14 htau hst (hmem j0 hj0).1
        (hmem j0 hj0).2 (by simpa using hcpl 0 (by omega))
    have IH := vt_ev_run (cplen := cplen) (g := g) (cv0 := cv0) hEv hmem d (j0 + 1)
    rcases d with _ | d
    · rw [show 16 * (0 + 1) = 16 from rfl]
      refine hunit.mono le_rfl le_rfl fun σ' q => ⟨fun j hj => ?_, fun _ => ?_⟩
      · obtain rfl : j = 0 := by omega
        simpa using q.1
      · simpa [cvE_succ] using q.2.2
    obtain ⟨a1, b1, c1⟩ := hc1 (by omega)
    simp only [Nat.mul_one] at a1 b1
    rw [show 16 * (d + 1 + 1) = 16 + 16 * (d + 1) by ring]
    refine (vt_cons (Q := fun σ'' => (∀ j < d + 1, σ'' (.n (evVal.getD (j0 + 1 + j) 0)) = ws (j0 + 1 + j)) ∧
        (0 < d + 1 → (σ'' (.n (evVal.getD (j0 + 1 + (d + 1) - 1) 0 + 13)),
          σ'' (.n (evVal.getD (j0 + 1 + (d + 1) - 1) 0 + 14))) = digestScalars (cvE cv0 ws (j0 + 1 + (d + 1)))))
      (by omega) (by omega) (numBelow_of_B (ev_nb j0 hj0)) hunit
      (fun σ1 σ2 hag hp => by simp +contextual (disch := omega) only [hag]; exact hp)
      fun σ' e p => ?_).mono le_rfl le_rfl ?_
    · rw [← a1, ← b1]
      have hr := IH (by omega) hs
        (fun j hj => by rw [show j0 + 1 + j = j0 + (j + 1) by omega]; exact hcpl (j + 1) (by omega)) σ'
        (by rw [Ext.app' e _ (by omega), h4651]) (by rw [Ext.app' e _ (by omega), h13])
        (by rw [Ext.app' e _ (by omega), h14])
        (by rw [c1, Ext.app' e _ (by omega), htau])
        (by
          simp only [evSt, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, cvE_succ]
          rw [show evVal.getD j0 0 + 13 + 1 = evVal.getD j0 0 + 14 by omega]
          exact p.2.2)
      rw [show evVal.getD (j0 + 1) 0 + 16 * (d + 1) = evVal.getD j0 0 + (16 + 16 * (d + 1)) by omega] at hr
      exact hr
    · rintro σ'' ⟨⟨q0, -⟩, qr, qs⟩
      refine ⟨fun j hj => ?_, fun _ => ?_⟩
      · rcases j with _ | j
        · simpa using q0
        · rw [show j0 + (j + 1) = j0 + 1 + j by omega]; exact qr j (by omega)
      · rw [show j0 + (d + 1 + 1) - 1 = j0 + 1 + (d + 1) - 1 by omega,
          show j0 + (d + 1 + 1) = j0 + 1 + (d + 1) by omega]
        exact qs (by omega)

end

end
end LeanVM.Guest.B1.VerifySub
