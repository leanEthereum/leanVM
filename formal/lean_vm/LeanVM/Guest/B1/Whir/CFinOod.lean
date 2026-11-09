/-
  LeanVM.Guest.B1.Whir.CFinOod

  The out-of-domain weights, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFinRes
public import LeanVM.Guest.B1.Whir.OodW

/-!
# The out-of-domain weights, honestly

`osOodFacs_complete`: the factors `sc·Π_t (1 + z_t + c_t)`. `osOodWeight_complete`: one weight,
its scalar read. `osOodWeights_complete`: the weights summed onto the running sum.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- One factor's values. -/
def oodFacVals (z y scv : E) : List E :=
  [word 1 0 0, z, word 1 0 0 + z, y, word 1 0 0 + z + y, scv * (word 1 0 0 + z + y)]

/-- The values of the factors. -/
def oodFacsF (Z Y : ℕ → E) : List (ℕ × ℕ × ℕ) → ℕ → ℕ → Val → ℕ → E
  | [], _, _, _ => fun _ ↦ 0
  | _ :: rest, sc, k, σ =>
    seqF σ k (k + 6) (fun j ↦ (oodFacVals (Z 0) (Y 0) (σ (.n sc))).getD (j - k) 0)
      fun σ1 ↦ oodFacsF (fun t ↦ Z (t + 1)) (fun t ↦ Y (t + 1)) rest (k + 5) (k + 6) σ1

theorem osOodFacs_k : ∀ (cs : List (ℕ × ℕ × ℕ)) (sc k : ℕ),
    (osOodFacs sc cs k).2.2 = k + 6 * cs.length ∧
      (sc < k → (osOodFacs sc cs k).2.1 < (osOodFacs sc cs k).2.2)
  | [], sc, k => ⟨by simp [osOodFacs], fun h ↦ by simp [osOodFacs]; omega⟩
  | _ :: rest, sc, k => by
    have := osOodFacs_k rest (k + 5) (k + 6)
    simp only [osOodFacs, List.length_cons]
    exact ⟨by rw [this.1]; ring, fun _ ↦ this.2 (by omega)⟩

/-- **The factors, honestly.** -/
theorem osOodFacs_complete : ∀ (cs : List (ℕ × ℕ × ℕ)) (sc k : ℕ) (σ : Val) (Z Y : ℕ → E),
    sc < k → osOodz < k →
    (∀ t < cs.length, (cs.getD t oodD).2.1 < k ∧
      LoadHolds rd (σ (.n osOodz)) (cs.getD t oodD).1 (Z t) ∧
      LoadHolds rd (σ (.n (cs.getD t oodD).2.1)) (cs.getD t oodD).2.2 (Y t)) →
    BlkF C rd σ k (osOodFacs sc cs k).2.2 (oodFacsF Z Y cs sc k σ) (osOodFacs sc cs k).1
      (fun σ' ↦ σ' (.n (osOodFacs sc cs k).2.1) =
        σ (.n sc) * ∏ t ∈ Finset.range cs.length, (1 + Z t + Y t) ∧ AgreeBelow k σ σ')
  | [], sc, k, σ, Z, Y, hsc, _, _ => by
    simp only [osOodFacs, oodFacsF]
    exact BlkF.nil fun σ' ha ↦ ⟨by simp [ha sc hsc], ha⟩
  | (zo, src) :: rest, sc, k, σ, Z, Y, hsc, hz, h => by
    obtain ⟨h1, h2, h3⟩ := h 0 (by simp)
    simp only [List.getD_cons_zero] at h1 h2 h3
    have hblk : BlkF C rd σ k (k + 6) (fun j ↦ (oodFacVals (Z 0) (Y 0) (σ (.n sc))).getD (j - k) 0)
        [.atom (.const (.n k) (word 1 0 0)), .atom (.load (.n (k + 1)) (.n osOodz) zo),
          .atom (.add (.n (k + 2)) (.n k) (.n (k + 1))), .atom (.load (.n (k + 3)) (.n src.1) src.2),
          .atom (.add (.n (k + 4)) (.n (k + 2)) (.n (k + 3))),
          .atom (.mul (.n (k + 5)) (.n sc) (.n (k + 4)))]
        (fun σ' ↦ σ' (.n (k + 5)) = σ (.n sc) * (1 + Z 0 + Y 0) ∧ AgreeBelow k σ σ') := by
      intro σ' ha hr
      have V : ∀ j < 6, σ' (.n (k + j)) = (oodFacVals (Z 0) (Y 0) (σ (.n sc))).getD j 0 :=
        fun j hj ↦ by rw [hr _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
      have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
      have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
      simp only [oodFacVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5
      refine ⟨?_, by rw [v5, word_one], ha⟩
      simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact ⟨v0, by rw [v1, ha _ hz]; exact h2, by rw [v2, v0, v1], by rw [v3, ha _ h1]; exact h3,
        by rw [v4, v2, v3], by rw [v5, ha _ hsc, v4]⟩
    simp only [osOodFacs, oodFacsF]
    have hk := (osOodFacs_k rest (k + 5) (k + 6)).1
    refine BlkF.then (k1 := k + 6) (by omega) (by omega) hblk fun σ1 _ ⟨h5, ha1⟩ ↦ ?_
    refine BlkF.mono (osOodFacs_complete rest (k + 5) (k + 6) σ1 (fun t ↦ Z (t + 1))
      (fun t ↦ Y (t + 1)) (by omega) (by omega) fun t ht ↦ ?_) fun σ' ⟨hv, ha2⟩ ↦ ⟨?_,
        fun i hi ↦ (ha2 i (by omega)).trans (ha1 i hi)⟩
    · obtain ⟨g1, g2, g3⟩ := h (t + 1) (by simp; omega)
      simp only [List.getD_cons_succ] at g1 g2 g3
      exact ⟨by omega, by rw [ha1 _ hz]; exact g2, by rw [ha1 _ g1]; exact g3⟩
    · rw [hv, h5, List.length_cons, Finset.prod_range_succ']
      ring

theorem oodSrc_lt {tch zf k t : ℕ} {lv : OsLv} (htch : tch < k) (hk : 164 ≤ k) :
    (oodSrc tch zf lv t).1 < k := by
  unfold oodSrc; split_ifs <;> simp only <;> first | (unfold osFch; omega) | omega

theorem oodAll_transfer {c : OsCfg} {tch : ℕ} {Λ : ℕ → E} {Z Y : ℕ → ℕ → E} {σ σ' : Val} {k : ℕ}
    (htch : tch < k) (hk : 164 ≤ k) (ha : AgreeBelow k σ σ') :
    ∀ (levels : List OsLv) (prevCols ol : ℕ), OodAll rd σ c tch Λ Z Y prevCols ol levels →
      OodAll rd σ' c tch Λ Z Y prevCols ol levels
  | [], _, _, _ => trivial
  | lv :: rest, prevCols, ol, ⟨⟨h1, h2⟩, hr⟩ => by
    refine ⟨⟨by rw [ha _ (show osOod < k by unfold osOod; omega)]; exact h1, fun t ht ↦ ?_⟩,
      oodAll_transfer htch hk ha rest _ _ hr⟩
    obtain ⟨g1, g2⟩ := h2 t ht
    exact ⟨by rw [ha _ (show osOodz < k by unfold osOodz; omega)]; exact g1,
      by rw [ha _ (oodSrc_lt htch hk)]; exact g2⟩

/-- The values of one weight. -/
def oodWeightF (c : OsCfg) (tch prevCols ol : ℕ) (lv : OsLv) (k : ℕ) (σ : Val) (lam : E)
    (Z Y : ℕ → E) : ℕ → E :=
  seqF σ k (k + 1) (fun _ ↦ lam) fun σ1 ↦
    oodFacsF Z Y ((List.range (prevCols - c.yrLog + c.yrLog)).map fun t ↦
      (ol * ligColsCap + t, if t < prevCols - c.yrLog then (osFch, lv.foldsOff + t)
        else (tch, t - (prevCols - c.yrLog)))) k (k + 1) σ1

theorem osOodWeight_k (c : OsCfg) (tch prevCols ol : ℕ) (lv : OsLv) (k : ℕ) :
    k + 1 ≤ (osOodWeight c tch prevCols ol lv k).2.2 ∧
      (osOodWeight c tch prevCols ol lv k).2.1 < (osOodWeight c tch prevCols ol lv k).2.2 := by
  simp only [osOodWeight]
  have := osOodFacs_k ((List.range (prevCols - c.yrLog + c.yrLog)).map fun t ↦
    (ol * ligColsCap + t, if t < prevCols - c.yrLog then (osFch, lv.foldsOff + t)
      else (tch, t - (prevCols - c.yrLog)))) k (k + 1)
  exact ⟨by omega, this.2 (by omega)⟩

/-- **One weight, honestly.** -/
theorem osOodWeight_complete {c : OsCfg} {tch prevCols ol : ℕ} {lv : OsLv} {k : ℕ} (σ : Val)
    (hk : 164 ≤ k) (htch : tch < k) {lam : E} {Z Y : ℕ → E}
    (hin : OodIn rd σ c tch prevCols ol lv lam Z Y) :
    BlkF C rd σ k (osOodWeight c tch prevCols ol lv k).2.2
      (oodWeightF c tch prevCols ol lv k σ lam Z Y) (osOodWeight c tch prevCols ol lv k).1
      (fun σ' ↦ σ' (.n (osOodWeight c tch prevCols ol lv k).2.1) =
        lam * ∏ t ∈ Finset.range (prevCols - c.yrLog + c.yrLog), (1 + Z t + Y t) ∧
        AgreeBelow k σ σ') := by
  set cs := (List.range (prevCols - c.yrLog + c.yrLog)).map fun t ↦
    (ol * ligColsCap + t, if t < prevCols - c.yrLog then (osFch, lv.foldsOff + t)
      else (tch, t - (prevCols - c.yrLog))) with hcs
  have hlen : cs.length = prevCols - c.yrLog + c.yrLog := by simp [hcs]
  have e : osOodWeight c tch prevCols ol lv k =
      ([.atom (.load (.n k) (.n osOod) (ol * oodSlots))] ++ (osOodFacs k cs (k + 1)).1,
        (osOodFacs k cs (k + 1)).2) := rfl
  rw [e]
  dsimp only
  unfold oodWeightF
  rw [← hcs]
  have hk2 := (osOodFacs_k cs k (k + 1)).1
  refine BlkF.then (k1 := k + 1) (by omega) (by omega)
    (load_complete σ (show osOod < k by unfold osOod; omega) hin.1) fun σ1 _ ⟨h1, ha1⟩ ↦ ?_
  refine BlkF.mono (osOodFacs_complete cs k (k + 1) σ1 Z Y (by omega)
    (by unfold osOodz; omega) fun t ht ↦ ?_) fun σ' ⟨hv, ha2⟩ ↦ ⟨by rw [hv, h1, hlen],
      fun i hi ↦ (ha2 i (by omega)).trans (ha1 i hi)⟩
  rw [hlen] at ht
  have hg : cs.getD t oodD = (ol * ligColsCap + t, oodSrc tch (prevCols - c.yrLog) lv t) := by
    simp [hcs, List.getD_eq_getElem?_getD, ht, oodSrc]
  rw [hg]
  obtain ⟨g1, g2⟩ := hin.2 t ht
  exact ⟨oodSrc_lt (by omega) (by omega), by rw [ha1 _ (show osOodz < k by unfold osOodz; omega)]; exact g1,
    by rw [ha1 _ (oodSrc_lt htch hk)]; exact g2⟩

/-- The running sum's step after a weight. -/
def accStep (acc : Option ℕ) (w : ℕ × ℕ) : Option ℕ × ℕ :=
  match acc with
  | none => (some w.1, w.2)
  | some _ => (some w.2, w.2 + 1)

/-- The values of the weights. -/
def oodWeightsF (c : OsCfg) (tch : ℕ) (Λ : ℕ → E) (Z Y : ℕ → ℕ → E) :
    ℕ → ℕ → List OsLv → Option ℕ → ℕ → Val → ℕ → E
  | prevCols, ol, lv :: rest, acc, k, σ =>
    let w := osOodWeight c tch prevCols ol lv k
    seqF σ k w.2.2 (oodWeightF c tch prevCols ol lv k σ (Λ ol) (Z ol) (Y ol)) fun σ1 ↦
    seqF σ1 w.2.2 (accStep acc w.2).2
      (match acc with
        | none => fun _ ↦ 0
        | some x => fun _ ↦ σ1 (.n x) + σ1 (.n w.2.1)) fun σ2 ↦
    oodWeightsF c tch Λ Z Y lv.logCols (ol + 1) rest (accStep acc w.2).1 (accStep acc w.2).2 σ2
  | _, _, [], _, _, _ => fun _ ↦ 0

theorem accStep_k (acc : Option ℕ) (w : ℕ × ℕ) (h : w.1 < w.2) :
    w.2 ≤ (accStep acc w).2 ∧ ∀ y, (accStep acc w).1 = some y → y < (accStep acc w).2 := by
  rcases acc with _ | x <;> simp only [accStep, Option.some.injEq] <;>
    exact ⟨by omega, fun y hy ↦ by omega⟩

theorem osOodWeights_k (c : OsCfg) (tch : ℕ) : ∀ (levels : List OsLv) (prevCols ol : ℕ)
    (acc : Option ℕ) (k : ℕ), k ≤ (osOodWeights c tch prevCols ol levels acc k).2.2
  | [], _, _, _, _ => le_rfl
  | lv :: rest, prevCols, ol, acc, k => by
    have hw := osOodWeight_k c tch prevCols ol lv k
    have hs := accStep_k acc (osOodWeight c tch prevCols ol lv k).2 hw.2
    have hr := osOodWeights_k c tch rest lv.logCols (ol + 1)
      (accStep acc (osOodWeight c tch prevCols ol lv k).2).1
      (accStep acc (osOodWeight c tch prevCols ol lv k).2).2
    have e : (osOodWeights c tch prevCols ol (lv :: rest) acc k).2.2 =
        (osOodWeights c tch lv.logCols (ol + 1) rest
          (accStep acc (osOodWeight c tch prevCols ol lv k).2).1
          (accStep acc (osOodWeight c tch prevCols ol lv k).2).2).2.2 := by
      rcases acc with _ | x <;> rfl
    rw [e]; omega

/-- **The weights, honestly**, summed onto the running sum. -/
theorem osOodWeights_complete {c : OsCfg} {tch : ℕ} (Λ : ℕ → E) (Z Y : ℕ → ℕ → E) :
    ∀ (levels : List OsLv) (prevCols ol : ℕ) (acc : Option ℕ) (k : ℕ) (σ : Val), 164 ≤ k →
      tch < k → (∀ x, acc = some x → x < k) → OodAll rd σ c tch Λ Z Y prevCols ol levels →
      BlkF C rd σ k (osOodWeights c tch prevCols ol levels acc k).2.2
        (oodWeightsF c tch Λ Z Y prevCols ol levels acc k σ)
        (osOodWeights c tch prevCols ol levels acc k).1
        (fun σ' ↦ ((acc ≠ none ∨ levels ≠ []) →
          σ' (.n ((osOodWeights c tch prevCols ol levels acc k).2.1.getD 0)) =
            accVal σ acc + oodSum c Λ Z Y prevCols ol levels) ∧ AgreeBelow k σ σ')
  | [], prevCols, ol, acc, k, σ, _, _, hacc, _ => by
    simp only [osOodWeights, oodWeightsF]
    refine BlkF.nil fun σ' ha ↦ ⟨fun h ↦ ?_, ha⟩
    rcases acc with _ | x
    · simp at h
    · simp [accVal, oodSum, ha x (hacc x rfl)]
  | lv :: rest, prevCols, ol, acc, k, σ, hk, htch, hacc, ⟨h1, hrest⟩ => by
    set w := osOodWeight c tch prevCols ol lv k with hw
    have hwk1 : k + 1 ≤ w.2.2 := (osOodWeight_k c tch prevCols ol lv k).1
    have hwk2 : w.2.1 < w.2.2 := (osOodWeight_k c tch prevCols ol lv k).2
    obtain ⟨hs1, hs2⟩ := accStep_k acc w.2 hwk2
    have e : osOodWeights c tch prevCols ol (lv :: rest) acc k =
        (w.1 ++ ((match acc with
          | none => []
          | some x => [.atom (.add (.n w.2.2) (.n x) (.n w.2.1))]) ++
          (osOodWeights c tch lv.logCols (ol + 1) rest (accStep acc w.2).1 (accStep acc w.2).2).1),
          (osOodWeights c tch lv.logCols (ol + 1) rest (accStep acc w.2).1 (accStep acc w.2).2).2) := by
      rcases acc with _ | x <;> simp [osOodWeights, accStep, hw, List.append_assoc]
    rw [e]
    dsimp only
    simp only [oodWeightsF]
    rw [← hw]
    have hrk := osOodWeights_k c tch rest lv.logCols (ol + 1) (accStep acc w.2).1 (accStep acc w.2).2
    have hA := osOodWeight_complete (C := C) (rd := rd) (c := c) (tch := tch) (prevCols := prevCols)
      (ol := ol) (lv := lv) (k := k) σ hk htch h1
    rw [← hw] at hA
    refine BlkF.then (k1 := w.2.2) (by omega) (by omega) hA fun σ1 _ ⟨hw1, ha1⟩ ↦ ?_
    refine BlkF.then (k1 := (accStep acc w.2).2) hs1 hrk
      (OutA := fun σ' ↦ (∀ y, (accStep acc w.2).1 = some y →
        σ' (.n y) = accVal σ acc + Λ ol *
          ∏ t ∈ Finset.range (prevCols - c.yrLog + c.yrLog), (1 + Z ol t + Y ol t)) ∧
        AgreeBelow w.2.2 σ1 σ') ?_ fun σ2 _ ⟨hy, ha2⟩ ↦ ?_
    · rcases acc with _ | x
      · simp only [accStep]
        refine BlkF.nil fun σ' ha ↦ ⟨fun y hy ↦ ?_, ha⟩
        simp only [Option.some.injEq] at hy
        subst hy
        rw [ha _ hwk2, hw1]; simp [accVal]
      · simp only [accStep]
        have hx := hacc x rfl
        intro σ' ha hr
        have v0 := hr w.2.2 le_rfl (by omega)
        refine ⟨allOk_cons.mpr ⟨?_, allOk_nil⟩, ⟨fun y hy ↦ ?_, ha⟩⟩
        · show σ' (.n w.2.2) = σ' (.n x) + σ' (.n w.2.1)
          rw [v0, ha x (by omega), ha w.2.1 hwk2]
        · simp only [Option.some.injEq] at hy
          subst hy
          rw [v0, hw1, ha1 x hx]
          simp [accVal]
    · have hag : AgreeBelow k σ σ2 := fun i hi ↦ (ha2 i (by omega)).trans (ha1 i hi)
      have hall := oodAll_transfer (rd := rd) (k := k) htch hk hag rest lv.logCols (ol + 1) hrest
      obtain ⟨y, hy0⟩ : ∃ y, (accStep acc w.2).1 = some y := by
        rcases acc with _ | x <;> simp [accStep]
      refine BlkF.mono (osOodWeights_complete Λ Z Y rest lv.logCols (ol + 1) (accStep acc w.2).1
        (accStep acc w.2).2 σ2 (by omega) (by omega) (fun x hx ↦ hs2 x hx) hall)
        fun σ' ⟨hv, ha3⟩ ↦ ⟨fun _ ↦ ?_, fun i hi ↦ (ha3 i (by omega)).trans (hag i hi)⟩
      rw [hv (Or.inl (by rw [hy0]; simp)), hy0, show accVal σ2 (some y) = σ2 (.n y) from rfl,
        hy y hy0, oodSum]
      ring

end
end LeanVM.Guest.B1.Whir
