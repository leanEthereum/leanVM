/-
  LeanVM.Guest.B1.VsC.Os.LeftRes

  `open_stacked`'s `level_residual` and `level_residual_slow` calls at the helpers' honest values.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftLevels
public import LeanVM.Guest.B1.VsC.LrA
public import LeanVM.Guest.B1.VsC.SlowA

/-!
# A non-final level's residuals in the node

`OsResOk`: at every arm, rate and non-final level, `level_residual`'s and `level_residual_slow`'s
specializations are in `lrTable` and `lrsTable`, and what they read fits the buffers (one kernel
decision, `osRes`). `readsAt_seg`: a segment of a run.

`osLrEntry`: a non-final level's `level_residual` (`lrA_complete`) completes placed at
`OsHelperVals`' arguments and returns (`osLrRetA` is `lrPair` over the buffers' words), on every
memory holding the buffers. `osLrsEntry`: its `level_residual_slow` (`lrsA_complete`) likewise
(`osSlowRetA` is `slowVal`, the flag `osZA` in `K`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- What a non-final level's residuals need of the tables and the buffers. -/
def osResOk1 (c : OsCfg) (l : ℕ) : Bool :=
  decide (LrOk (osLvA c l)) && decide ((osLvA c l).queries < 2 ^ 30) &&
    decide (l * ligColsCap + (osLvA c l).logCols ≤ (osSizesL c).getD (osIxBdA c) 0) &&
    decide (l * hsStride + (osLvA c l).folds ≤ (osSizesL c).getD osIxHsA 0) &&
    decide ((osLvA c l).posOff + (osLvA c l).queries ≤ (osSizesL c).getD osIxQposA 0) &&
    decide ((osLvA c l).resFoldOff + (osLvA c l).prefixLen ≤ (osSizesL c).getD osIxFchA 0) &&
    decide (c.yrLog ≤ (osSizesL c).getD (osIxTchA c) 0) &&
    decide (osIxBdA c < (osSizesL c).length) && decide (osIxTchA c < (osSizesL c).length) &&
    lrsTable.any (fun e => e.1 == osSlowName c (osLvA c l) && e.2.1 == (osLvA c l).queries &&
      e.2.2.1 == (osLvA c l).prefixLen && e.2.2.2.1 == c.yrLog && e.2.2.2.2.1 == (osLvA c l).vanish)

/-- Every arm's non-final levels' residuals' facts. -/
def OsResOk (m : ℕ) : Bool :=
  (List.range 4).all fun ri => (List.range (osCfgR m ri).yrLevel).all fun l => osResOk1 (osCfgR m ri) l

set_option maxRecDepth 100000 in
theorem osResOk_all : (List.range 15).all OsResOk = true := by decide +kernel

theorem osRes {m ri l : ℕ} (hm : m < 15) (hri : ri < 4) (hl : l < (osCfgR m ri).yrLevel) :
    LrOk (osLvA (osCfgR m ri) l) ∧ (osLvA (osCfgR m ri) l).queries < 2 ^ 30 ∧
    l * ligColsCap + (osLvA (osCfgR m ri) l).logCols ≤ (osSizesL (osCfgR m ri)).getD (osIxBdA (osCfgR m ri)) 0 ∧
    l * hsStride + (osLvA (osCfgR m ri) l).folds ≤ (osSizesL (osCfgR m ri)).getD osIxHsA 0 ∧
    (osLvA (osCfgR m ri) l).posOff + (osLvA (osCfgR m ri) l).queries ≤ (osSizesL (osCfgR m ri)).getD osIxQposA 0 ∧
    (osLvA (osCfgR m ri) l).resFoldOff + (osLvA (osCfgR m ri) l).prefixLen ≤
      (osSizesL (osCfgR m ri)).getD osIxFchA 0 ∧
    (osCfgR m ri).yrLog ≤ (osSizesL (osCfgR m ri)).getD (osIxTchA (osCfgR m ri)) 0 ∧
    osIxBdA (osCfgR m ri) < (osSizesL (osCfgR m ri)).length ∧
    osIxTchA (osCfgR m ri) < (osSizesL (osCfgR m ri)).length ∧
    ∃ e ∈ lrsTable, e.1 = osSlowName (osCfgR m ri) (osLvA (osCfgR m ri) l) ∧
      e.2.1 = (osLvA (osCfgR m ri) l).queries ∧ e.2.2.1 = (osLvA (osCfgR m ri) l).prefixLen ∧
      e.2.2.2.1 = (osCfgR m ri).yrLog ∧ e.2.2.2.2.1 = (osLvA (osCfgR m ri) l).vanish := by
  have h := List.all_eq_true.mp osResOk_all m (List.mem_range.mpr hm)
  simp only [OsResOk, List.all_eq_true, List.mem_range] at h
  have h1 := h ri hri l hl
  simp only [osResOk1, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, e, he, ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩⟩ := h1
  exact ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7, h8, h9, h10, e, he, e1, e2, e3, e4, e5⟩

/-- **A segment of a run.** -/
theorem readsAt_seg {rd : Reader} {p : E} {ws : List E} (h : ReadsAt rd p ws) {off n : ℕ}
    (hn : off + n ≤ ws.length) : ReadsAt rd (p * gen ^ off) ((List.range n).map fun i => ws.getD (off + i) 0) := by
  intro k hk
  simp only [List.length_map, List.length_range] at hk
  simp only [List.getElem_map, List.getElem_range]
  rw [loadHolds_mul_gen_pow, List.getD_eq_getElem _ _ (by omega)]
  exact h _ (by omega)

/-- The buffer `j`'s words' count. -/
theorem osOwnA_length {c : OsCfg} {own : List (List E)}
    (hown : List.Forall₂ (fun w s ↦ w.length = s) own (osSizesL c)) (j : ℕ) :
    (osOwnA own j).length = (osSizesL c).getD j 0 := forall₂_getD hown j

section
variable {al : String → Bool} {k m ri : ℕ} (hm : m < 15) (hri : ri < 4)
include hm hri

/-- **A non-final level's `level_residual` in `open_stacked`'s node**, at the helpers' honest values. -/
theorem osLrEntry {l : ℕ} (hl : l < (osCfgR m ri).yrLevel) (b : ℕ) {own : List (List E)}
    (hown : List.Forall₂ (fun w s ↦ w.length = s) own (osSizesL (osCfgR m ri))) (mu : E) (Rg : ℕ → Prop)
    (hRb : ∀ j < (osSizesL (osCfgR m ri)).length, ∀ i < (osSizesL (osCfgR m ri)).getD j 0,
      Rg ((bases b (osSizesL (osCfgR m ri))).getD j 0 + i))
    (fp cc : ℕ) (hfc : fp + B2C.fs (osResidualName (osLvA (osCfgR m ri) l)) ≤ cc) :
    ∃ e, (∀ F, (∀ f, B2C.fs f ≤ F) → e ≤ cc + ((osLvA (osCfgR m ri) l).queries + 4) * (F + 32)) ∧ CallAtA B2C.fs al B2C.cert k (osResidualName (osLvA (osCfgR m ri) l))
      [osPtrA (osCfgR m ri) b osIxQposA * gen ^ (osLvA (osCfgR m ri) l).posOff,
        osPtrA (osCfgR m ri) b (osIxBdA (osCfgR m ri)) * gen ^ (l * ligColsCap),
        osPtrA (osCfgR m ri) b osIxHsA * gen ^ (l * hsStride), mu,
        gen ^ ((osLvA (osCfgR m ri) l).queries / resBatch), gen ^ ((osLvA (osCfgR m ri) l).queries % resBatch)]
      [(osLrRetA (osCfgR m ri) own l mu).1, (osLrRetA (osCfgR m ri) own l mu).2] Rg (fun _ => False) (fun _ => True)
      (fun rd => OsMemA rd (osCfgR m ri) b own) PostQuiet (B2C.fs (osResidualName (osLvA (osCfgR m ri) l))) fp cc e := by
  obtain ⟨hLr, hq30, hbd, hhs, hqp, -, -, hbdl, -, -⟩ := osRes hm hri hl
  have hS := honStatic_all m ri hm hri
  have hlen := hS.len
  have hyl : (osCfgR m ri).yrLevel + 1 = (osCfgR m ri).levels.length := hS.yr
  have hqpl : osIxQposA < (osSizesL (osCfgR m ri)).length := by rw [hlen]; simp only [osIxQposA]; omega
  have hhsl : osIxHsA < (osSizesL (osCfgR m ri)).length := by rw [hlen]; simp only [osIxHsA]; omega
  have hA : LrAE B2C.fs al B2C.cert k (osResidualName (osLvA (osCfgR m ri) l)) (osLvA (osCfgR m ri) l).logCols
      (osLvA (osCfgR m ri) l).folds (osLvA (osCfgR m ri) l).highBits := lrAE_complete k _ hLr.1
  set B : ℕ → ℕ := fun j => (bases b (osSizesL (osCfgR m ri))).getD j 0
  obtain ⟨e, hbe, he⟩ := hA (osLvA (osCfgR m ri) l).queries (B osIxQposA + (osLvA (osCfgR m ri) l).posOff)
    (B (osIxBdA (osCfgR m ri)) + l * ligColsCap) (B osIxHsA + l * hsStride) mu
    (fun s => (osOwnA own (osIxBdA (osCfgR m ri))).getD (l * ligColsCap + s) 0)
    (fun k => (osOwnA own osIxQposA).getD ((osLvA (osCfgR m ri) l).posOff + k) 0)
    ((List.range (osLvA (osCfgR m ri) l).folds).map fun i => (osOwnA own osIxHsA).getD (l * hsStride + i) 0) Rg
    hLr.2.1 hq30 (by simp)
    (fun i hi => by rw [Nat.add_assoc]; exact hRb _ hqpl _ (by omega))
    (fun i hi => by rw [Nat.add_assoc]; exact hRb _ hbdl _ (by omega))
    (fun i hi => by rw [Nat.add_assoc]; exact hRb _ hhsl _ (by omega)) fp cc hfc
  have e1 : osPtrA (osCfgR m ri) b osIxQposA * gen ^ (osLvA (osCfgR m ri) l).posOff =
      ptrAt (B osIxQposA + (osLvA (osCfgR m ri) l).posOff) := ptrAt_mul_gen _ _
  have e2 : osPtrA (osCfgR m ri) b (osIxBdA (osCfgR m ri)) * gen ^ (l * ligColsCap) =
      ptrAt (B (osIxBdA (osCfgR m ri)) + l * ligColsCap) := ptrAt_mul_gen _ _
  have e3 : osPtrA (osCfgR m ri) b osIxHsA * gen ^ (l * hsStride) = ptrAt (B osIxHsA + l * hsStride) :=
    ptrAt_mul_gen _ _
  rw [← e1, ← e2, ← e3] at he
  refine ⟨e, hbe, he.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd hmem => ?_) (fun _ _ _ h => h)⟩
  refine ⟨readsAt_seg (hmem _ hqpl (by decide)) ?_, readsAt_seg (hmem _ hbdl (by simp only [osIxBdA, osIxQbpA]; omega)) ?_,
    readsAt_seg (hmem _ hhsl (by decide)) ?_⟩
  · rw [osOwnA_length hown]; omega
  · rw [osOwnA_length hown]; omega
  · rw [osOwnA_length hown]; omega

/-- **A non-final level's `level_residual_slow` in `open_stacked`'s node**, at the helpers' honest
values. -/
theorem osLrsEntry {l : ℕ} (hl : l < (osCfgR m ri).yrLevel) (b : ℕ) {own : List (List E)}
    (hown : List.Forall₂ (fun w s ↦ w.length = s) own (osSizesL (osCfgR m ri))) (lam : E) (Rg : ℕ → Prop)
    (hRb : ∀ j < (osSizesL (osCfgR m ri)).length, ∀ i < (osSizesL (osCfgR m ri)).getD j 0,
      Rg ((bases b (osSizesL (osCfgR m ri))).getD j 0 + i))
    (fp cc : ℕ) (hfc : fp + B2C.fs (osSlowName (osCfgR m ri) (osLvA (osCfgR m ri) l)) ≤ cc) :
    ∃ e, (∀ F, (∀ f, B2C.fs f ≤ F) → e ≤ cc + ((osLvA (osCfgR m ri) l).queries + 3) * (2 * F + 32)) ∧ CallAtA B2C.fs al B2C.cert k (osSlowName (osCfgR m ri) (osLvA (osCfgR m ri) l))
      [osPtrA (osCfgR m ri) b osIxQposA * gen ^ (osLvA (osCfgR m ri) l).posOff,
        osPtrA (osCfgR m ri) b osIxFchA * gen ^ (osLvA (osCfgR m ri) l).resFoldOff,
        osPtrA (osCfgR m ri) b (osIxTchA (osCfgR m ri)), lam, osZA (osCfgR m ri) own l]
      [osSlowRetA (osCfgR m ri) own l lam (osZA (osCfgR m ri) own l)] Rg (fun _ => False) (fun _ => True)
      (fun rd => OsMemA rd (osCfgR m ri) b own) PostQuiet
      (B2C.fs (osSlowName (osCfgR m ri) (osLvA (osCfgR m ri) l))) fp cc e := by
  obtain ⟨-, -, -, -, hqp, hfch, htch, -, htchl, ent, hent, en1, en2, en3, en4, en5⟩ := osRes hm hri hl
  have hS := honStatic_all m ri hm hri
  have hlen := hS.len
  have hqpl : osIxQposA < (osSizesL (osCfgR m ri)).length := by rw [hlen]; simp only [osIxQposA]; omega
  have hfcl : osIxFchA < (osSizesL (osCfgR m ri)).length := by rw [hlen]; simp only [osIxFchA]; omega
  have hA := (lrsAE_complete (fs := B2C.fs) (al := al) (cert := B2C.cert) k ent hent).1
  rw [en1, en2, en3, en4, en5] at hA
  set B : ℕ → ℕ := fun j => (bases b (osSizesL (osCfgR m ri))).getD j 0
  have hz : IsInK (osZA (osCfgR m ri) own l) := by
    unfold osZA zeroOf
    split_ifs
    · exact isInK_one
    · exact isInK_zero
  obtain ⟨e, hbe, he⟩ := hA (B osIxQposA + (osLvA (osCfgR m ri) l).posOff)
    (B osIxFchA + (osLvA (osCfgR m ri) l).resFoldOff) (B (osIxTchA (osCfgR m ri))) lam (osZA (osCfgR m ri) own l)
    (fun k => (osOwnA own osIxQposA).getD ((osLvA (osCfgR m ri) l).posOff + k) 0)
    (fun t => if t < (osLvA (osCfgR m ri) l).prefixLen then
      (osOwnA own osIxFchA).getD ((osLvA (osCfgR m ri) l).resFoldOff + t) 0
      else (osOwnA own (osIxTchA (osCfgR m ri))).getD (t - (osLvA (osCfgR m ri) l).prefixLen) 0) Rg hz
    (fun i hi => by rw [Nat.add_assoc]; exact hRb _ hqpl _ (by omega))
    (fun i hi => by rw [Nat.add_assoc]; exact hRb _ hfcl _ (by omega))
    (fun i hi => hRb _ htchl _ (by omega)) fp cc hfc
  have e1 : osPtrA (osCfgR m ri) b osIxQposA * gen ^ (osLvA (osCfgR m ri) l).posOff =
      ptrAt (B osIxQposA + (osLvA (osCfgR m ri) l).posOff) := ptrAt_mul_gen _ _
  have e2 : osPtrA (osCfgR m ri) b osIxFchA * gen ^ (osLvA (osCfgR m ri) l).resFoldOff =
      ptrAt (B osIxFchA + (osLvA (osCfgR m ri) l).resFoldOff) := ptrAt_mul_gen _ _
  rw [← e1, ← e2] at he
  refine ⟨e, hbe, he.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd hmem => ?_) (fun _ _ _ h => h)⟩
  have hq := hmem _ hqpl (by decide)
  have hf := hmem _ hfcl (by decide)
  have ht := hmem _ htchl (by simp only [osIxTchA, osIxQbpA]; omega)
  refine ⟨readsAt_seg hq (by rw [osOwnA_length hown]; omega), fun t htl => ?_, fun j hj => ?_⟩
  · simp only [htl, ↓reduceIte]
    rw [loadHolds_mul_gen_pow]
    have hb : (osLvA (osCfgR m ri) l).resFoldOff + t < (osOwnA own osIxFchA).length := by
      rw [osOwnA_length hown]; omega
    rw [List.getD_eq_getElem _ _ hb]
    exact hf _ hb
  · simp only [show ¬ ((osLvA (osCfgR m ri) l).prefixLen + j < (osLvA (osCfgR m ri) l).prefixLen) by omega,
      ↓reduceIte, Nat.add_sub_cancel_left]
    have hb : j < (osOwnA own (osIxTchA (osCfgR m ri))).length := by rw [osOwnA_length hown]; omega
    rw [List.getD_eq_getElem _ _ hb]
    exact ht _ hb

end

end
end LeanVM.Guest.B1.VsC
