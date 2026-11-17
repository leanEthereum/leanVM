module

public import Quantum.StdModel.Qrom.EncSaltAmort
public import Quantum.StdModel.Qrom.LiveDet

@[expose] public section

/-!
# EncTCR$: the budget measure along live runs

Generic facts about the live runs of a reduction's algorithm in the EncTCR$ game
(`Quantum.StdModel.Qrom.EncSalt`), stated for any salted encoding so that instances apply them in
one step.

* `βS_mem0`: the budget measure starts at `0`.
* `liveRedRun_βS_le`: an algorithm without challenger queries raises the budget measure by at most
  its reads of encoding cells (`costR`).
* `liveRun_βS_eq`: a classical algorithm reading no encoding cell keeps the budget measure, with
  the reduction's policy; the challenger's answers keep it with any reads.
-/

open OracleComp OracleSpec

namespace Quantum.StdModel.Qrom.EncSalt.Live

open Quantum Quantum.Qrom HashSig Props Common
open Tcr (Mem IsG rl uRed)

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

open scoped Classical in
/-- A read of the reduction raises the budget measure by at most its cost. -/
theorem βS_stepRd_red_le (z : HashDomain) (μ : Option Mem) (v : HashOutput) :
    (stepRd rl (upd e .red z) z μ v).elim 0 (βS e) ≤
      μ.elim 0 (βS e) + costR e (.inl (.inr z) :
        (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Domain) := by
  rcases μ with _ | m
  · exact Nat.zero_le _
  rcases hs : stepRd rl (upd e .red z) z (some m) v with _ | m'
  · exact Nat.zero_le _
  obtain ⟨rfl, -⟩ := stepRd_some hs
  change βS e (uRed z m (some v)) ≤ βS e m + costR e (.inl (.inr z))
  by_cases hz : IsG e.hash G z
  · have hc : costR e (.inl (.inr z) :
        (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Domain) = 1 := by
      simp [costR, hz]
    rw [hc]
    exact (βS_uRed z m (some v)).2
  · rw [βS_uRed_eq (Or.inl hz)]
    exact Nat.le_add_right _ _

open scoped Classical in
/-- **The budget measure starts at `0`.** -/
theorem βS_mem0 : βS e mem0 = 0 := by
  unfold βS
  have hc : (Finset.univ.filter fun z ↦ IsG e.hash G z ∧ mem0.seen z = true) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun _ _ h ↦ Bool.false_ne_true h.2
  rw [hc, Finset.card_empty, zero_add]
  exact ite_eq_left_iff.mpr fun h ↦ absurd rfl h

/-- **An algorithm without challenger queries raises the budget measure by at most its reads of
encoding cells.** -/
theorem liveRedRun_βS_le (ans : (q' : Tw × Msg) → OracleComp romWorld.Oracles (Option (Salt × Dig)))
    {α : Type} (oa : OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) α)
    {k : ℕ} (hk : QueryCostAtMost oa (costR e) k)
    (hna : QueryCostAtMost oa
      (Quantum.StdModel.Qrom.ansCost (R' := Tw × Msg →ₒ Option (Salt × Dig))) 0)
    {log : QueryLog (Tw × Msg →ₒ Option (Salt × Dig))} {μ : Option Mem}
    {a : α × QueryLog (Tw × Msg →ₒ Option (Salt × Dig))} {μ' : Option Mem}
    (h : LiveRedRun rl (upd e) ans oa log μ a μ') :
    ∀ m m', μ = some m → μ' = some m' → βS e m' ≤ βS e m + k := by
  intro m m' hm hm'
  have := (liveRedRun_count (upd e) rl ans (costR e) (fun μ ↦ μ.elim 0 (βS e))
    (βS_stepRd_red_le e) oa hk hna h).1
  rw [hm, hm'] at this
  exact this

end Quantum.StdModel.Qrom.EncSalt.Live

end
