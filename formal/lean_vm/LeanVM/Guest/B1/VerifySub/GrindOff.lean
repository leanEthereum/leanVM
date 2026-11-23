/-
  LeanVM.Guest.B1.VerifySub.GrindOff

  `grind_check` inlined on constant tables, its table reads at an offset: its blocks, soundness and completeness.
-/

module

public import LeanVM.Guest.B1.Bits.GrindFwd
public import LeanVM.Guest.B1.Common.Atoms

/-!
# `grind_check` inlined, its tables folded into the reads

Where the tables are a constant `t·g^off` (`verify_sub`'s `g_squares·g^WIN_TAB_AT`), the compiler multiplies each window into `t` and reads at offset `off`: `gcInlineOT b o off w t` is `gcInlineT b o w t` with its table reads at `off`. Its blocks (`holds_gcInlineOT`) are the plain ones on the valuation with `t` and the table reads' pointers times `g^off` (`gcShift`), so soundness (`gcInlineO_sound`) and completeness (`gcInlineO_complete_of`) follow from `Bits/Grind`'s with the tables at `t·g^off`. The expansion is `Bits/GrindFwd`'s, where a caller's evaluated valuation holds `gcVals` at `t` on its own values (`gcInlineO_vals_of_good`); so it holds there (`gcInlineO_holds_of_good`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## Its blocks -/

/-- `GcIterOk`, the table read at `off`. -/
def GcIterOkO (rd : Reader) (off : ℕ) (σ : Val) (W i : ℕ) : Prop :=
  σ (.n (W + 9 * i)) = wBound 11 ∧
    (LoadHolds rd (σ (.n (W + 2 - i))) 0 (σ (.n (W + 9 * i + 2))) ∧
      σ (.n (W + 9 * i)) = σ (.n (W + 2 - i)) * σ (.n (W + 9 * i + 1)) ∧
      LoadHolds rd (σ (.n (W + 9 * i + 1))) 0 (σ (.n (W + 9 * i + 3)))) ∧
    σ (.n (W + 9 * i + 4)) = word 2048 0 ∧
    σ (.n (W + 9 * i + 5)) = σ (.n (W + 9 * i - 1)) * σ (.n (W + 9 * i + 4)) ∧
    σ (.n (W + 9 * i + 6)) = σ (.n 1) * σ (.n (W + 2 - i)) ∧
    LoadHolds rd (σ (.n (W + 9 * i + 6))) off (σ (.n (W + 9 * i + 7))) ∧
    σ (.n (W + 9 * i + 8)) = σ (.n (W + 9 * i + 5)) + σ (.n (W + 9 * i + 7))

/-- `GcHeadOk`, the table read at `off`. -/
def GcHeadOkO (rd : Reader) (off : ℕ) (σ : Val) (W T : ℕ) : Prop :=
  σ (.n (W + 3)) = wBound T ∧
    (LoadHolds rd (σ (.n (W + 2))) 0 (σ (.n (W + 5))) ∧
      σ (.n (W + 3)) = σ (.n (W + 2)) * σ (.n (W + 4)) ∧
      LoadHolds rd (σ (.n (W + 4))) 0 (σ (.n (W + 6)))) ∧
    σ (.n (W + 7)) = σ (.n 1) * σ (.n (W + 2)) ∧
    LoadHolds rd (σ (.n (W + 7))) off (σ (.n (W + 8)))

theorem holds_gcIterAtO {C : CallRel} {rd : Reader} {σ : Val} (W i off : ℕ) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gcIterAtO W i off) next kret ↔ GcIterOkO rd off σ W i ∧ next := by
  simp only [gcIterAtO, GcIterOkO, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_assoc]

theorem holds_gcPreO {C : CallRel} {rd : Reader} {σ : Val} (b off : ℕ) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gcPreO b off) next kret ↔
      GcHeadOkO rd off σ (gcW b) (gcTop b) ∧
        (∀ i < gcW b, GcIterOkO rd off σ (gcW b) (i + 1)) ∧ GcTailOk σ (gcW b) b ∧ next := by
  rw [gcPreO, holdsList_append, holdsList_append,
    holdsList_range_flatten _ _ (fun i => rfl)]
  simp only [gcHeadO, gcTailPre, GcHeadOkO, GcTailOk, holds_gcIterAtO, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, true_and, and_true, and_assoc]

/-! ## The shift to the plain blocks -/

/-- The tables' value and the table reads' pointers, which the shift multiplies by `g^off`. -/
def GcPtrIdx (W k : ℕ) : Prop := k = 1 ∨ k = W + 7 ∨ ∃ i, 1 ≤ i ∧ i ≤ W ∧ k = W + 9 * i + 6

open Classical in
/-- The valuation with the tables and the table reads' pointers times `g^off`. -/
noncomputable def gcShift (W off : ℕ) (τ : Val) : Val := fun v =>
  if GcPtrIdx W v.idx then τ v * gen ^ off else τ v

variable {W off : ℕ} {τ : Val}

/-- Discharges `¬ GcPtrIdx W k` for a `k` that is none of the pointers. -/
local macro "gc_np" : tactic => `(tactic| (rintro (h | h | ⟨_, _, _, h⟩) <;> omega))

theorem gcShift_of {k : ℕ} (h : GcPtrIdx W k) : gcShift W off τ (.n k) = τ (.n k) * gen ^ off := by
  unfold gcShift; rw [ite_eq_left h]

theorem gcShift_not {k : ℕ} (h : ¬ GcPtrIdx W k) : gcShift W off τ (.n k) = τ (.n k) := by
  unfold gcShift; rw [ite_eq_right h]

theorem gcMulShift_iff {a b c : E} : a * gen ^ off = b * gen ^ off * c ↔ a = b * c := by
  rw [mul_right_comm b, mul_left_inj' (pow_ne_zero _ gen_ne_zero)]

theorem gcLoadShift_iff {rd : Reader} {p v : E} : LoadHolds rd (p * gen ^ off) 0 v ↔ LoadHolds rd p off v := by
  rw [loadHolds_mul_gen_pow, Nat.add_zero]

theorem gcHeadOkO_iff {rd : Reader} {T : ℕ} : GcHeadOkO rd off τ W T ↔ GcHeadOk rd (gcShift W off τ) W T := by
  unfold GcHeadOkO GcHeadOk
  rw [gcShift_not (k := W + 3) (by gc_np),
    gcShift_not (k := W + 2) (by gc_np),
    gcShift_not (k := W + 4) (by gc_np),
    gcShift_not (k := W + 5) (by gc_np),
    gcShift_not (k := W + 6) (by gc_np),
    gcShift_not (k := W + 8) (by gc_np),
    gcShift_of (k := W + 7) (Or.inr (Or.inl rfl)), gcShift_of (k := 1) (Or.inl rfl),
    gcMulShift_iff, gcLoadShift_iff]

theorem gcIterOkO_iff {rd : Reader} {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ W) :
    GcIterOkO rd off τ W i ↔ GcIterOk rd (gcShift W off τ) W i := by
  unfold GcIterOkO GcIterOk
  rw [gcShift_not (k := W + 9 * i) (by gc_np),
    gcShift_not (k := W + 2 - i) (by gc_np),
    gcShift_not (k := W + 9 * i + 1) (by gc_np),
    gcShift_not (k := W + 9 * i + 2) (by gc_np),
    gcShift_not (k := W + 9 * i + 3) (by gc_np),
    gcShift_not (k := W + 9 * i + 4) (by gc_np),
    gcShift_not (k := W + 9 * i + 5) (by gc_np),
    gcShift_not (k := W + 9 * i - 1) (by gc_np),
    gcShift_not (k := W + 9 * i + 7) (by gc_np),
    gcShift_not (k := W + 9 * i + 8) (by gc_np),
    gcShift_of (k := W + 9 * i + 6) (Or.inr (Or.inr ⟨i, h1, h2, rfl⟩)), gcShift_of (k := 1) (Or.inl rfl),
    gcMulShift_iff, gcLoadShift_iff]

theorem gcTailOk_shift {b : ℕ} (hW : W = gcW b) : GcTailOk τ W b ↔ GcTailOk (gcShift W off τ) W b := by
  unfold GcTailOk
  rw [gcShift_not (k := 0) (by gc_np),
    gcShift_not (k := 10 * W + 8) (by gc_np),
    gcShift_not (k := 10 * W + 9) (by gc_np),
    gcShift_not (k := 10 * W + 10) (by gc_np),
    gcShift_not (k := 10 * W + 11) (by gc_np),
    gcShift_not (k := 10 * W + 12) (by gc_np),
    gcShift_not (k := 10 * W + 13) (by gc_np),
    gcShift_not (k := 10 * W + 14) (by gc_np),
    gcShift_not (k := 10 * W + 15) (by gc_np)]

/-- **Inlined, its reads at `off`**: the plain blocks on the shifted valuation. -/
theorem holds_gcInlineOT {C : CallRel} {rd : Reader} {σ : Val} (b o off : ℕ) (w tabs : V) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gcInlineOT b o off w tabs) next kret ↔
      GcHeadOk rd (gcShift (gcW b) off (σ ∘ gcRen o w tabs)) (gcW b) (gcTop b) ∧
        (∀ i < gcW b, GcIterOk rd (gcShift (gcW b) off (σ ∘ gcRen o w tabs)) (gcW b) (i + 1)) ∧
          GcTailOk (gcShift (gcW b) off (σ ∘ gcRen o w tabs)) (gcW b) b ∧ next := by
  rw [gcInlineOT, Stmt.holdsList_rename, holds_gcPreO, gcHeadOkO_iff, gcTailOk_shift rfl]
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  exact forall_congr' fun i ↦ imp_congr_right fun hi ↦ gcIterOkO_iff (by omega) (by omega)

/-- **Inlined, its reads at `off`, sound**: on a memory image of `2^κ ≥ 2^11` words holding the
windows at `t·g^off`, the word passes the proof of work. -/
theorem gcInlineO_sound {C : CallRel} {κ : ℕ} (hκ : κ ≤ 32) (hκ11 : 11 ≤ κ) (L : MemoryImage κ)
    {σ : Val} {b o off : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V}
    (ht : WinTabs L.read (σ tabs * gen ^ off)) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C L.read σ (gcInlineOT b o off w tabs) next kret) :
    ((σ w).limb 0).lane.toNat % 2 ^ b = 0 ∧ next := by
  obtain ⟨hh, hi, htl, hn⟩ := (holds_gcInlineOT b o off w tabs next kret).mp h
  have h0 : gcShift (gcW b) off (σ ∘ gcRen o w tabs) (.n 0) = σ w :=
    gcShift_not (by gc_np)
  have h1 : gcShift (gcW b) off (σ ∘ gcRen o w tabs) (.n 1) = σ tabs * gen ^ off :=
    gcShift_of (Or.inl rfl)
  have := gc_sound hκ hκ11 L (gc_shape b hb) (by rw [h1]; exact ht) hh hi htl
  rw [h0] at this
  exact ⟨this, hn⟩

/-! ## Completeness -/

theorem gcIterVal_tabs {rd : Reader} {b : ℕ} {w t t' : E} {i r : ℕ} (h9 : r < 9) (hr : r ≠ 6) :
    gcIterVal rd b w t i r = gcIterVal rd b w t' i r := by
  interval_cases r
  all_goals first | exact absurd rfl hr | simp only [gcIterVal]

/-- The honest values read the tables only at `1` and the table reads' pointers. -/
theorem gcVals_tabs {rd : Reader} {b : ℕ} {w t t' : E} {k : ℕ} (h : ¬ GcPtrIdx (gcW b) k) :
    gcVals rd b w t k = gcVals rd b w t' k := by
  unfold gcVals
  refine ite_congr rfl (fun _ ↦ rfl) fun _ ↦ ?_
  refine ite_congr rfl (fun c ↦ absurd (Or.inl c) h) fun _ ↦ ?_
  refine ite_congr rfl (fun _ ↦ rfl) fun n2 ↦ ?_
  refine ite_congr rfl (fun _ ↦ rfl) fun n3 ↦ ?_
  refine ite_congr rfl (fun _ ↦ rfl) fun n4 ↦ ?_
  refine ite_congr rfl (fun _ ↦ rfl) fun n5 ↦ ?_
  refine ite_congr rfl (fun _ ↦ rfl) fun n6 ↦ ?_
  refine ite_congr rfl (fun _ ↦ rfl) fun n7 ↦ ?_
  refine ite_congr rfl (fun c ↦ absurd (Or.inr (Or.inl c)) h) fun n8 ↦ ?_
  refine ite_congr rfl (fun _ ↦ rfl) fun n9 ↦ ?_
  refine ite_congr rfl (fun c ↦ gcIterVal_tabs (Nat.mod_lt _ (by norm_num)) fun h6 ↦ h (Or.inr (Or.inr
    ⟨(k - gcW b) / 9, by omega, by omega, by omega⟩))) fun _ ↦ rfl

theorem gcVals_shift {rd : Reader} {b off : ℕ} {w t : E} (k : ℕ) (hk : k < gcLen b) :
    gcShift (gcW b) off (fun v ↦ gcVals rd b w t v.idx) (.n k) = gcVals rd b w (t * gen ^ off) k := by
  by_cases h : GcPtrIdx (gcW b) k
  · rw [gcShift_of h]
    show gcVals rd b w t k * gen ^ off = _
    rcases h with rfl | rfl | ⟨i, h1, h2, rfl⟩
    · unfold gcVals; simp
    · rw [gv_top_ptr, gv_top_ptr]
      ring
    · rw [gv_iter h1 h2 (by omega), gv_iter h1 h2 (by omega)]
      show t * gen ^ _ * gen ^ off = t * gen ^ off * gen ^ _
      ring
  · rw [gcShift_not h]; exact gcVals_tabs h

/-- **Inlined, its reads at `off`, complete** wherever the windows' range checks pass: on a
valuation holding the honest values (`gcVals` at the tables `t`) on its own values, the windows at
`t·g^off`. -/
theorem gcInlineO_complete_of {C : CallRel} {rd : Reader}
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    {b o off : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V} {σ : Val}
    (ht : WinTabs rd (σ tabs * gen ^ off))
    (hlow : ((σ w).limb 0).lane.toNat % 2 ^ b = 0)
    (hσ : ∀ k, 2 ≤ k → k < gcLen b → σ (.n (o + k - 2)) = gcVals rd b (σ w) (σ tabs) k)
    {next : Prop} (hn : next) {kret : List E → Prop} :
    Stmt.HoldsList C rd σ (gcInlineOT b o off w tabs) next kret := by
  have hτ : ∀ k < gcLen b, (σ ∘ gcRen o w tabs) (.n k) = gcVals rd b (σ w) (σ tabs) k := gcRen_vals hσ
  -- the shifted valuation is the honest one at `t·g^off` on the expansion's values
  have hv : ∀ v ∈ Stmt.valsList (gcPre b), gcShift (gcW b) off (σ ∘ gcRen o w tabs) v =
      gcVals rd b (σ w) (σ tabs * gen ^ off) v.idx := by
    intro v hv
    obtain ⟨hve, hlt⟩ := of_decide_eq_true (List.all_eq_true.mp (gcPre_vals b hb) v hv)
    rw [hve]
    by_cases h : GcPtrIdx (gcW b) v.idx
    · rw [gcShift_of h, hτ _ hlt, ← gcVals_shift (off := off) _ hlt, gcShift_of h]
    · rw [gcShift_not h, hτ _ hlt, gcVals_tabs h]
  have H : Stmt.HoldsList C rd (fun v ↦ gcVals rd b (σ w) (σ tabs * gen ^ off) v.idx) (gcPre b) next kret := by
    rw [holds_gcPre]
    obtain ⟨hh, hi, htl⟩ := gc_complete_of hrc (gc_shape b hb) (gcW_pos b hb) ht hlow
    exact ⟨hh, hi, htl, hn⟩
  rw [← Sig.holdsList_congr (gcPre b) hv next kret, holds_gcPre] at H
  rw [holds_gcInlineOT]
  exact H

/-! ## Its statements -/

/-- **The expansion is atoms.** -/
theorem gcInlineOT_atoms (b o off : ℕ) (w tabs : V) : AllAtoms (gcInlineOT b o off w tabs) := by
  intro s hs
  obtain ⟨s0, hs0, rfl⟩ := renameList_mem_inv hs
  simp only [gcPreO, gcHeadO, gcIterAtO, gcTailPre, List.mem_append, List.mem_flatten, List.mem_map,
    List.mem_range] at hs0
  rcases hs0 with (hs0 | ⟨l, ⟨i, hi, rfl⟩, hs0⟩) | hs0
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-! ## On a caller's evaluated valuation -/

variable {rd : Reader} {S : List Atom} {wo : ℕ → E} {σ : Val}

/-- **Inlined, its reads at `off`, evaluated, holds**: on the caller's evaluated valuation, the word
passing the proof of work. -/
theorem gcInlineO_holds_of_good {C : CallRel} {b o off : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V}
    (hwo : w.idx < o) (hto : tabs.idx < o)
    (hg : ∀ s ∈ gcInlineOT b o off w tabs, GoodS rd S wo σ s)
    (hS : ∀ a ∈ S, loadInto o (o + (gcLen b - 2)) a = false)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ tabs * gen ^ off))
    (hwin : ∀ j ≤ gcW b, wo (o + j) = gcWin b (σ w) j)
    (hlow : ((σ w).limb 0).lane.toNat % 2 ^ b = 0) {next : Prop} (hn : next)
    {kret : List E → Prop} : Stmt.HoldsList C rd σ (gcInlineOT b o off w tabs) next kret :=
  gcInlineO_complete_of hrc hb ht hlow
    (gcInlineO_vals_of_good hb hwo hto hg hS hrc ht hwin) hn

end
end LeanVM.Guest.B1
