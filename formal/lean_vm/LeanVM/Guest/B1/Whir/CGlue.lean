/-
  LeanVM.Guest.B1.Whir.CGlue

  The query weights and a level's glue, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFold
public import LeanVM.Guest.B1.Whir.CSqLoop
public import LeanVM.Guest.B1.Whir.LamPows
public import LeanVM.Guest.B1.Whir.Glue

/-!
# The query weights and the glue, honestly

`osLamPow_complete`: `λ^n` by square and multiply, `μ = λ⁻¹` stored in `level_mus`.
`osOodGlue_complete`: the out-of-domain value and intro in `ood` (and the slot of `λ`), the claim
glued with `λ`. `osGlue_complete`: the level's batch glued with `β`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The values of `osLamPow`'s block: the square-and-multiply chain of `λ^n`, then `1` and
`μ = λ⁻¹`. -/
def lamPowVals (X : E) (n k i : ℕ) : E :=
  if i < k + osPowLen n then (powVals X (osPowDigits n) 1).getD (i - k) 0
  else if i = k + osPowLen n then 1 else X⁻¹

/-- **`λ^n` and `level_mus[lvl] = 1/λ`, honestly**: `λ ≠ 0`, `μ = λ⁻¹` in `level_mus`. -/
theorem osLamPow_complete {lvl lam n k : ℕ} (hd : digitsVal (osPowDigits n) 1 = n) (σ : Val)
    (hl : lam < k) (hmu : osMus < k) (h0 : σ (.n lam) ≠ 0)
    (hmem : LoadHolds rd (σ (.n osMus)) lvl (σ (.n lam))⁻¹) :
    BlkF C rd σ k (k + osPowLen n + 2) (lamPowVals (σ (.n lam)) n k) (osLamPow lvl lam n k).1
      (fun σ' ↦ σ' (.n (osLamPow lvl lam n k).2.1) = σ (.n lam) ^ n ∧ AgreeBelow k σ σ') := by
  intro σ' ha hv
  have el : σ' (.n lam) = σ (.n lam) := ha _ hl
  have em : σ' (.n osMus) = σ (.n osMus) := ha _ hmu
  have hp := osPowSteps_complete (C := C) (rd := rd) (σ := σ') lam (osPowDigits n) lam k 1
    (by rw [pow_one]) (fun j hj ↦ by
      rw [powVals_length] at hj
      rw [hv (k + j) (by omega) (by unfold osPowLen; omega), el]
      simp only [lamPowVals, show k + j < k + osPowLen n by unfold osPowLen; omega, ↓reduceIte,
        Nat.add_sub_cancel_left])
  set k' := k + osPowLen n
  have v0 : σ' (.n k') = 1 := by
    rw [hv k' (by omega) (by omega)]; simp [lamPowVals, k']
  have v1 : σ' (.n (k' + 1)) = (σ (.n lam))⁻¹ := by
    rw [hv (k' + 1) (by omega) (by omega)]; simp [lamPowVals, k']
  refine ⟨?_, ?_, ha⟩
  · simp only [osLamPow, allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    refine ⟨hp.1, by rw [v0, word_one], by rw [v0, v1, el, inv_mul_cancel₀ h0], by rw [v1, em]; exact hmem⟩
  · simp only [osLamPow]
    rw [hp.2, hd, el]

theorem osPowSteps_lt (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ), acc < k →
    (osPowSteps x ds acc k).2 < k + ds.length + (ds.filter id).length
  | [], _, _, h => by simp [osPowSteps]; omega
  | true :: ds, acc, k, _ => by
    have := osPowSteps_lt x ds (k + 1) (k + 2) (by omega)
    simp only [osPowSteps, ↓reduceIte, List.length_cons, List.filter_cons_of_pos (show id true = true from rfl)]
    omega
  | false :: ds, acc, k, _ => by
    have := osPowSteps_lt x ds k (k + 1) (by omega)
    simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte, List.length_cons,
      List.filter_cons_of_neg (show ¬ id false = true by decide)]
    omega

/-- `λ^n`'s value lies below the block's `1`. -/
theorem osLamPow_lt {lvl lam n k : ℕ} (h : lam < k) : (osLamPow lvl lam n k).2.1 < k + osPowLen n := by
  have := osPowSteps_lt lam (osPowDigits n) lam k h
  simp only [osLamPow, osPowLen]
  omega

/-- **`β·λ^n` stored in `level_betas`, honestly.** -/
theorem osBeta_complete {σ : Val} {bk beta lamN lvl : ℕ} (hbe : beta < bk) (hn : lamN < bk)
    (hB : osBetas < bk) (hmem : LoadHolds rd (σ (.n osBetas)) lvl (σ (.n beta) * σ (.n lamN))) :
    BlkF C rd σ bk (bk + 1) (fun _ ↦ σ (.n beta) * σ (.n lamN))
      [.atom (.mul (.n bk) (.n beta) (.n lamN)), .atom (.load (.n bk) (.n osBetas) lvl)]
      (fun σ' ↦ AgreeBelow bk σ σ') := by
  intro σ' ha hv
  have v := hv bk le_rfl (by omega)
  refine ⟨?_, ha⟩
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  exact ⟨by rw [v, ha _ hbe, ha _ hn], by rw [v, ha _ hB]; exact hmem⟩

/-- The out-of-domain glue's values. -/
def oodGlueVals (σ : Val) (s : OsSt) (lam : ℕ) (y c0 c2 : E) : List E :=
  let l := σ (.n lam)
  [y, c2, c0, l * c0, σ (.n s.c) + l * c0, y + c2, l * (y + c2), σ (.n s.b) + l * (y + c2),
    l * c2, σ (.n s.a) + l * c2, l * y, σ (.n s.t) + l * y, l * l]

/-- **The out-of-domain claim glued, honestly.** -/
theorem osOodGlue_complete {lvl lam : ℕ} {s : OsSt} (σ : Val) (hb : s.Below) (hl : lam < s.k)
    (hk : 164 ≤ s.k) {y c0 c2 : E}
    (hy : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 1) y)
    (hc0 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 2) c0)
    (hc2 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 3) c2)
    (hlam : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots) (σ (.n lam))) :
    BlkF C rd σ s.k (osOodGlue lvl lam s).2.k
      (fun i ↦ (oodGlueVals σ s lam y c0 c2).getD (i - s.k) 0) (osOodGlue lvl lam s).1
      (fun σ' ↦ (osOodGlue lvl lam s).2.quad σ' =
          [σ (.n s.c) + σ (.n lam) * c0, σ (.n s.b) + σ (.n lam) * (y + c2),
            σ (.n s.a) + σ (.n lam) * c2] ∧
        σ' (.n (osOodGlue lvl lam s).2.t) = σ (.n s.t) + σ (.n lam) * y ∧
        σ' (.n (s.k + 12)) = σ (.n lam) * σ (.n lam) ∧ (osOodGlue lvl lam s).2.Below ∧
        AgreeBelow s.k σ σ') := by
  intro σ' ha hv
  have V : ∀ j < 13, σ' (.n (s.k + j)) = (oodGlueVals σ s lam y c0 c2).getD j 0 := fun j hj ↦ by
    rw [hv _ (by omega) (by simp [osOodGlue]; omega)]
    simp only [Nat.add_sub_cancel_left]
  have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
  have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
  have v6 := V 6 (by omega); have v7 := V 7 (by omega); have v8 := V 8 (by omega)
  have v9 := V 9 (by omega); have v10 := V 10 (by omega); have v11 := V 11 (by omega)
  have v12 := V 12 (by omega)
  simp only [oodGlueVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  have eo : σ' (.n osOod) = σ (.n osOod) := ha _ (by unfold osOod; omega)
  have el : σ' (.n lam) = σ (.n lam) := ha _ hl
  have ec := ha _ hb.c; have eb := ha _ hb.b; have ea := ha _ hb.a; have et := ha _ hb.t
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ha⟩⟩
  · simp only [osOodGlue, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    refine ⟨by rw [v0, eo]; exact hy, by rw [v1, eo]; exact hc2, by rw [el, eo]; exact hlam,
      by rw [v2, eo]; exact hc0, by rw [v3, el, v2], by rw [v4, ec, v3], by rw [v5, v0, v1],
      by rw [v6, el, v5], by rw [v7, eb, v6], by rw [v8, el, v1], by rw [v9, ea, v8],
      by rw [v10, el, v0], by rw [v11, et, v10], by rw [v12, el]⟩
  · simp only [OsSt.quad, osOodGlue]; rw [v4, v7, v9]
  · simp only [osOodGlue]; rw [v11]
  · exact v12
  · have := hb.w0; have := hb.w1; have := hb.cb
    refine ⟨fun f hf ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [osOodGlue] at *
    all_goals first | omega | exact Nat.lt_add_right _ (hb.fs f hf)

/-- The values of the level's glue. -/
def glueVals (σ : Val) (s : OsSt) (beta v c0 c1 c2 : ℕ) : List E :=
  [σ (.n beta) * σ (.n c0), σ (.n s.c) + σ (.n beta) * σ (.n c0),
    σ (.n beta) * σ (.n c1), σ (.n s.b) + σ (.n beta) * σ (.n c1), σ (.n beta) * σ (.n c2),
    σ (.n s.a) + σ (.n beta) * σ (.n c2), σ (.n beta) * σ (.n v),
    σ (.n s.t) + σ (.n beta) * σ (.n v)]

/-- **The level's batch glued, honestly.** -/
theorem osGlue_complete {beta v c0 c1 c2 : ℕ} {s : OsSt} (σ : Val) (hb : s.Below)
    (hv0 : beta < s.k ∧ v < s.k ∧ c0 < s.k ∧ c1 < s.k ∧ c2 < s.k) :
    BlkF C rd σ s.k (osGlue beta v c0 c1 c2 s).2.k
      (fun i ↦ (glueVals σ s beta v c0 c1 c2).getD (i - s.k) 0) (osGlue beta v c0 c1 c2 s).1
      (fun σ' ↦ (osGlue beta v c0 c1 c2 s).2.quad σ' =
          [σ (.n s.c) + σ (.n beta) * σ (.n c0), σ (.n s.b) + σ (.n beta) * σ (.n c1),
            σ (.n s.a) + σ (.n beta) * σ (.n c2)] ∧
        σ' (.n (osGlue beta v c0 c1 c2 s).2.t) = σ (.n s.t) + σ (.n beta) * σ (.n v) ∧
        (osGlue beta v c0 c1 c2 s).2.Below ∧ AgreeBelow s.k σ σ') := by
  obtain ⟨hbe, hvv, h0, h1, h2⟩ := hv0
  set vals := glueVals σ s beta v c0 c1 c2 with hvals
  intro σ' ha hv
  have V : ∀ j < 8, σ' (.n (s.k + j)) = vals.getD j 0 := fun j hj ↦ by
    rw [hv _ (by omega) (by simp [osGlue]; omega)]
    simp only [Nat.add_sub_cancel_left]
  have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
  have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
  have v6 := V 6 (by omega); have v7 := V 7 (by omega)
  simp only [hvals, glueVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7
  have eb := ha _ hbe; have evv := ha _ hvv; have e0 := ha _ h0; have e1 := ha _ h1
  have e2 := ha _ h2
  have ec := ha _ hb.c; have ebb := ha _ hb.b; have ea := ha _ hb.a; have et := ha _ hb.t
  refine ⟨?_, ⟨?_, ?_, ?_, ha⟩⟩
  · simp only [osGlue, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    exact ⟨by rw [v0, eb, e0], by rw [v1, ec, v0], by rw [v2, eb, e1], by rw [v3, ebb, v2],
      by rw [v4, eb, e2], by rw [v5, ea, v4], by rw [v6, eb, evv], by rw [v7, et, v6]⟩
  · simp only [OsSt.quad, osGlue]; rw [v1, v3, v5]
  · simp only [osGlue]; rw [v7]
  · have := hb.w0; have := hb.w1; have := hb.cb
    refine ⟨fun f hf ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [osGlue] at *
    all_goals first | omega | exact Nat.lt_add_right _ (hb.fs f hf)

end
end LeanVM.Guest.B1.Whir
