/-
  LeanVM.Guest.B1.VerifySub.GrindOff

  `grind_check` inlined on constant tables: its table reads at an offset.
-/

module

public import LeanVM.Guest.B1.Bits.GrindFwd
public import LeanVM.Guest.B1.Common.Atoms

/-!
# `grind_check` inlined, its tables folded into the reads

Where the tables are a constant `t·g^off` (`verify_sub`'s `g_squares·g^WIN_TAB_AT`), the compiler multiplies each window into `t` and reads at offset `off`: `gcInlineOT b o off w t` is `gcInlineT b o w t` with its table reads at `off`. Its blocks (`holds_gcInlineOT`) are the plain ones on the valuation with `t` and the table reads' pointers times `g^off` (`gcShift`), so soundness (`gcInlineO_sound`) and completeness (`gcInlineO_complete_of`) follow from `Bits/Grind`'s with the tables at `t·g^off`. On a caller's evaluated valuation its own values are `gcVals` at `t` (`gcInlineO_vals_of_good`, `Bits/GrindFwd`'s proof with the reads at `off`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The expansion -/

/-- `gcHead b`, its table read at `off`. -/
def gcHeadO (b off : ℕ) : List Stmt :=
  [.atom (.hint (.windowsExp (.n 0) b 11 (gcW b)
      (.stack ((List.range (gcW b)).map fun j => .n (2 + j))))),
    .atom (.hint (.windowsExp (.n 0) (b + 11 * gcW b) (gcTop b) 1 (.stack [.n (gcW b + 2)]))),
    .atom (.const (.n (gcW b + 3)) (wBound (gcTop b))),
    .atom (.rangeCheck (.n (gcW b + 2)) (.n (gcW b + 4)) (.n (gcW b + 5)) (.n (gcW b + 6))
      (.n (gcW b + 3))),
    .atom (.mul (.n (gcW b + 7)) (.n 1) (.n (gcW b + 2))),
    .atom (.load (.n (gcW b + 8)) (.n (gcW b + 7)) off)]

/-- `gcIterAt W i`, its table read at `off`. -/
def gcIterAtO (W i off : ℕ) : List Stmt :=
  [.atom (.const (.n (W + 9 * i)) (wBound 11)),
    .atom (.rangeCheck (.n (W + 2 - i)) (.n (W + 9 * i + 1)) (.n (W + 9 * i + 2))
      (.n (W + 9 * i + 3)) (.n (W + 9 * i))),
    .atom (.const (.n (W + 9 * i + 4)) (word 2048 0)),
    .atom (.mul (.n (W + 9 * i + 5)) (.n (W + 9 * i - 1)) (.n (W + 9 * i + 4))),
    .atom (.mul (.n (W + 9 * i + 6)) (.n 1) (.n (W + 2 - i))),
    .atom (.load (.n (W + 9 * i + 7)) (.n (W + 9 * i + 6)) off),
    .atom (.add (.n (W + 9 * i + 8)) (.n (W + 9 * i + 5)) (.n (W + 9 * i + 7)))]

/-- `gcPre b`, its table reads at `off`. -/
def gcPreO (b off : ℕ) : List Stmt :=
  gcHeadO b off ++ ((List.range (gcW b)).map fun i => gcIterAtO (gcW b) (i + 1) off).flatten ++
    gcTailPre b

/-- **`grind_check(w, t·g^off, b)` inlined**, its own values from `.n o`, its table reads at `off`. -/
def gcInlineOT (b o off : ℕ) (w tabs : V) : List Stmt := Stmt.renameList (gcRen o w tabs) (gcPreO b off)

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
  rw [gcShift_not (k := W + 3) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 2) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 4) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 5) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 6) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 8) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_of (k := W + 7) (Or.inr (Or.inl rfl)), gcShift_of (k := 1) (Or.inl rfl),
    gcMulShift_iff, gcLoadShift_iff]

theorem gcIterOkO_iff {rd : Reader} {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ W) :
    GcIterOkO rd off τ W i ↔ GcIterOk rd (gcShift W off τ) W i := by
  unfold GcIterOkO GcIterOk
  rw [gcShift_not (k := W + 9 * i) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 2 - i) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 9 * i + 1) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 9 * i + 2) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 9 * i + 3) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 9 * i + 4) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 9 * i + 5) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 9 * i - 1) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 9 * i + 7) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := W + 9 * i + 8) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_of (k := W + 9 * i + 6) (Or.inr (Or.inr ⟨i, h1, h2, rfl⟩)), gcShift_of (k := 1) (Or.inl rfl),
    gcMulShift_iff, gcLoadShift_iff]

theorem gcTailOk_shift {b : ℕ} (hW : W = gcW b) : GcTailOk τ W b ↔ GcTailOk (gcShift W off τ) W b := by
  unfold GcTailOk
  rw [gcShift_not (k := 0) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := 10 * W + 8) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := 10 * W + 9) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := 10 * W + 10) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := 10 * W + 11) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := 10 * W + 12) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := 10 * W + 13) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := 10 * W + 14) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega),
    gcShift_not (k := 10 * W + 15) (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega)]

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
    gcShift_not (by rintro (h | h | ⟨_, _, _, h⟩) <;> omega)
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

theorem gv_head7 {rd : Reader} {b : ℕ} {w t : E} : gcVals rd b w t (gcW b + 7) = t * gen ^ gcV b w 0 := by
  unfold gcVals
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left rfl]

theorem gcVals_shift {rd : Reader} {b off : ℕ} {w t : E} (k : ℕ) (hk : k < gcLen b) :
    gcShift (gcW b) off (fun v ↦ gcVals rd b w t v.idx) (.n k) = gcVals rd b w (t * gen ^ off) k := by
  by_cases h : GcPtrIdx (gcW b) k
  · rw [gcShift_of h]
    show gcVals rd b w t k * gen ^ off = _
    rcases h with rfl | rfl | ⟨i, h1, h2, rfl⟩
    · unfold gcVals; simp
    · rw [gv_head7, gv_head7]
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
  have hτ : ∀ k < gcLen b, (σ ∘ gcRen o w tabs) (.n k) = gcVals rd b (σ w) (σ tabs) k := by
    intro k hk
    show σ (gcRen o w tabs (.n k)) = _
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · rw [gcRen_word]; unfold gcVals; simp
      · rw [gcRen_tabs]; unfold gcVals; simp
    · rw [gcRen_own o w tabs h2]; exact hσ _ h2 hk
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

theorem gcO_mem_renameList_inv {r : V → V} : ∀ {ss : List Stmt} {s : Stmt}, s ∈ Stmt.renameList r ss →
    ∃ s0 ∈ ss, s0.rename r = s
  | [], _, h => absurd h (by simp [Stmt.renameList])
  | t :: ss, s, h => by
    simp only [Stmt.renameList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨t, List.mem_cons_self, rfl⟩
    · obtain ⟨s0, hs0, e⟩ := gcO_mem_renameList_inv h
      exact ⟨s0, List.mem_cons_of_mem _ hs0, e⟩

/-- **The expansion is atoms.** -/
theorem gcInlineOT_atoms (b o off : ℕ) (w tabs : V) : AllAtoms (gcInlineOT b o off w tabs) := by
  intro s hs
  obtain ⟨s0, hs0, rfl⟩ := gcO_mem_renameList_inv hs
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

theorem winTab_loadO {rd : Reader} {t : E} {off : ℕ} (ht : WinTabs rd (t * gen ^ off)) {e : ℕ}
    (he : e < 2 ^ 11) : LoadHolds rd (t * gen ^ e) off (eOfNat e) := by
  have h := winTab_load ht he
  rw [mul_right_comm, loadHolds_mul_gen_pow, Nat.add_zero] at h
  exact h

variable {rd : Reader} {S : List Atom} {wo : ℕ → E} {σ : Val}

/-- **`grind_check` inlined, evaluated, is honest** on its own values. -/
theorem gcInlineO_vals_of_good {b o off : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V}
    (hwo : w.idx < o) (hto : tabs.idx < o)
    (hg : ∀ s ∈ gcInlineOT b o off w tabs, GoodS rd S wo σ s)
    (hS : ∀ a ∈ S, loadInto o (o + (gcLen b - 2)) a = false)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ tabs * gen ^ off))
    (hwin : ∀ j ≤ gcW b, wo (o + j) = gcWin b (σ w) j) :
    ∀ k, 2 ≤ k → k < gcLen b → σ (.n (o + k - 2)) = gcVals rd b (σ w) (σ tabs) k := by
  obtain ⟨hT1, hT, hsum⟩ := gc_shape b hb
  have hW1 := gcW_pos b hb
  generalize hWd : gcW b = W at hT1 hT hsum hW1 hwin
  generalize hRd : gcRen o w tabs = R at hg
  have Rk : ∀ k, 2 ≤ k → R (.n k) = .n (o + k - 2) := fun k hk ↦ by
    rw [← hRd]; exact gcRen_own o w tabs hk
  have R0 : R (.n 0) = w := by rw [← hRd]; rfl
  have R1 : R (.n 1) = tabs := by rw [← hRd]; rfl
  -- the valuation through the renaming
  let τ : ℕ → E := fun k ↦ σ (R (.n k))
  have τk : ∀ k, 2 ≤ k → τ k = σ (.n (o + k - 2)) := fun k hk ↦ by simp only [τ, Rk k hk]
  have τ0 : τ 0 = σ w := by simp only [τ, R0]
  have τ1 : τ 1 = σ tabs := by simp only [τ, R1]
  have rlt : ∀ x d, x < d → 2 ≤ d → (R (.n x)).idx < (R (.n d)).idx := by
    intro x d hx hd
    rw [Rk d hd]
    rcases Nat.lt_or_ge x 2 with h2 | h2
    · rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl
      · rw [R0]; show w.idx < o + d - 2; omega
      · rw [R1]; show tabs.idx < o + d - 2; omega
    · rw [Rk x h2]; show o + x - 2 < o + d - 2; omega
  generalize hG : gcVals rd b (σ w) (σ tabs) = G
  -- the atoms' equations
  have hgA : ∀ a, Stmt.atom a ∈ gcPreO b off → Good rd S wo σ (a.rename R) := fun a ha ↦ by
    have := hg _ (by rw [gcInlineOT, hRd]; exact gc_mem_renameList ha)
    exact this
  have gconst : ∀ d c, Stmt.atom (.const (.n d) c) ∈ gcPreO b off → τ d = c := fun d c h ↦ hgA _ h
  have gadd : ∀ d x y, Stmt.atom (.add (.n d) (.n x) (.n y)) ∈ gcPreO b off → τ d = τ x + τ y :=
    fun d x y h ↦ hgA _ h
  have gmul : ∀ d x y, x < d → y < d → 2 ≤ d → Stmt.atom (.mul (.n d) (.n x) (.n y)) ∈ gcPreO b off →
      τ d = τ x * τ y := by
    intro d x y hx hy hd h
    have := hgA _ h
    simp only [Atom.rename, Good] at this
    rwa [ite_eq_left ⟨rlt x d hx hd, rlt y d hy hd⟩] at this
  have gload : ∀ d p k, 2 ≤ d → d < gcLen b → Stmt.atom (.load (.n d) (.n p) k) ∈ gcPreO b off →
      τ d = rdAt rd (τ p) k := by
    intro d p k hd hdl h
    have := hgA _ h
    simp only [Atom.rename, Good] at this
    rcases this with h' | h'
    · have := hS _ h'
      simp only [loadInto, Rk d hd, decide_eq_false_iff_not] at this
      exact absurd ⟨by show o ≤ o + d - 2; omega, by show o + d - 2 < o + (gcLen b - 2); omega⟩ this
    · exact h'
  have grc : ∀ x y t1 t2 k, k < y → 2 ≤ y →
      Stmt.atom (.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n k)) ∈ gcPreO b off →
      τ t1 = rdAt rd (τ x) 0 ∧ τ t2 = rdAt rd (τ y) 0 ∧ τ y = τ k * (τ x)⁻¹ := by
    intro x y t1 t2 k hk hy h
    have := hgA _ h
    simp only [Atom.rename, Good] at this
    rwa [ite_eq_left (rlt k y hk hy)] at this
  -- membership in the expansion
  have mH : ∀ s ∈ gcHeadO b off, s ∈ gcPreO b off := fun s h ↦
    List.mem_append_left _ (List.mem_append_left _ h)
  have mI : ∀ i, 1 ≤ i → i ≤ W → ∀ s ∈ gcIterAtO W i off, s ∈ gcPreO b off := fun i h1 h2 s h ↦
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr ⟨gcIterAtO W i off,
      List.mem_map.mpr ⟨i - 1, List.mem_range.mpr (by omega), by rw [hWd, Nat.sub_add_cancel h1]⟩,
      h⟩))
  have mT : ∀ s ∈ gcTailPre b, s ∈ gcPreO b off := fun s h ↦ List.mem_append_right _ h
  -- the windows
  have hwins : ∀ j ≤ W, τ (2 + j) = G (2 + j) := by
    intro j hj
    rw [← hG, gcVals_win (by rw [hWd]; exact hj), ← hwin j hj]
    rcases Nat.lt_or_ge j W with hjW | hjW
    · have := hgA (.hint (.windowsExp (.n 0) b 11 (gcW b)
        (.stack ((List.range (gcW b)).map fun j => .n (2 + j))))) (mH _ (by simp [gcHeadO]))
      simp only [Atom.rename, Hint.rename, Dest.rename, Good, hWd] at this
      have hv := this (R (.n (2 + j)))
        (List.mem_map.mpr ⟨.n (2 + j), List.mem_map.mpr ⟨j, List.mem_range.mpr hjW, rfl⟩, rfl⟩)
      rw [Rk _ (by omega)] at hv
      show σ (R (.n (2 + j))) = _
      rw [Rk _ (by omega), hv]
      show wo (o + (2 + j) - 2) = _
      congr 1; omega
    · obtain rfl : j = W := by omega
      have := hgA (.hint (.windowsExp (.n 0) (b + 11 * gcW b) (gcTop b) 1 (.stack [.n (gcW b + 2)])))
        (mH _ (by simp [gcHeadO]))
      simp only [Atom.rename, Hint.rename, Dest.rename, Good, hWd] at this
      have hv := this (R (.n (j + 2))) (by simp)
      rw [Rk _ (by omega)] at hv
      show σ (R (.n (2 + j))) = _
      rw [Nat.add_comm 2 j, Rk _ (by omega), hv]
      show wo (o + (j + 2) - 2) = _
      congr 1
  -- the honest values
  have hV0 : gcV b (σ w) 0 < 2 ^ gcTop b := by
    unfold gcV
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_zero, hWd,
      show gcTop b + (b + 11 * W) = 64 by omega]
    exact kToNat_lt _
  have hV0' : gcV b (σ w) 0 < 2 ^ 11 := lt_of_lt_of_le hV0 (Nat.pow_le_pow_right (by decide) hT)
  have Gw2 : G (W + 2) = gen ^ gcV b (σ w) 0 := by
    rw [← hG]; unfold gcVals
    rw [hWd, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  have gne : ∀ e : ℕ, (gen ^ e : E) ≠ 0 := fun e ↦ pow_ne_zero _ gen_ne_zero
  -- the head
  have hhead : ∀ r < 7, τ (W + 2 + r) = G (W + 2 + r) := by
    have e2 : τ (W + 2) = gen ^ gcV b (σ w) 0 := by
      rw [← Gw2, show W + 2 = 2 + W by ring]; exact hwins W le_rfl
    obtain ⟨y, t1, t2, r1, r2, r3⟩ := hrc _ hT _ hV0
    obtain ⟨c1, c2, c3⟩ := rcWit_spec (rd := rd) ⟨y, t1, t2, r1, r2, r3⟩
    have e3 : τ (W + 3) = wBound (gcTop b) := gconst _ _ (mH _ (by simp [gcHeadO, hWd]))
    obtain ⟨e5, e6, e4⟩ := grc (W + 2) (W + 4) (W + 5) (W + 6) (W + 3) (by omega) (by omega)
      (mH _ (by simp [gcHeadO, hWd]))
    have e7 : τ (W + 7) = τ 1 * τ (W + 2) :=
      gmul _ _ _ (by omega) (by omega) (by omega) (mH _ (by simp [gcHeadO, hWd]))
    have e8 : τ (W + 8) = rdAt rd (τ (W + 7)) off :=
      gload _ _ _ (by omega) (by rw [gcLen, hWd]; omega) (mH _ (by simp [gcHeadO, hWd]))
    rw [e2, e3] at e4
    rw [e2] at e5
    rw [τ1, e2] at e7
    rw [e7, rdAt_of_loadHolds (winTab_loadO ht hV0')] at e8
    have h4 : τ (W + 4) = (rcWit rd (gen ^ gcV b (σ w) 0) (wBound (gcTop b))).1 := by
      rw [e4]
      exact ((eq_mul_inv_iff_mul_eq₀ (gne _)).2 (by rw [mul_comm]; exact c2.symm)).symm
    rw [h4, rdAt_of_loadHolds c3] at e6
    rw [rdAt_of_loadHolds c1] at e5
    intro r hr
    rw [← hG]
    unfold gcVals
    rw [hWd]
    interval_cases r
    · rw [Nat.add_zero, e2, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left rfl]
    · rw [e3, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_left rfl]
    · rw [h4, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    · rw [e5, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    · rw [e6, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_left rfl]
    · rw [e7, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    · rw [e8, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  -- one Horner step
  have step : ∀ i, 1 ≤ i → i ≤ W → τ (W + 9 * i - 1) = G (W + 9 * i - 1) →
      ∀ r < 9, τ (W + 9 * i + r) = G (W + 9 * i + r) := by
    intro i h1 h2 hprev
    have h2' : i ≤ gcW b := by rw [hWd]; exact h2
    have gi : ∀ r < 9, G (W + 9 * i + r) = gcIterVal rd b (σ w) (σ tabs) i r := fun r hr ↦ by
      rw [← hG, ← hWd]; exact gv_iter h1 h2' hr
    have hwin' : gcV b (σ w) i % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by positivity)
    have ew : τ (W + 2 - i) = gen ^ (gcV b (σ w) i % 2 ^ 11) := by
      rw [show W + 2 - i = 2 + (W - i) by omega, hwins _ (by omega), ← hG,
        show 2 + (W - i) = gcW b + 2 - i by omega]
      exact gv_win h1 h2'
    have ep : τ (W + 9 * i - 1) = eOfNat (gcV b (σ w) (i - 1)) := by
      rw [hprev, ← hG, show W + 9 * i - 1 = gcW b + 9 * (i - 1) + 8 by omega]
      exact gv_acc (by omega)
    have mI' := mI i h1 h2
    obtain ⟨y, t1, t2, r1, r2, r3⟩ := hrc 11 le_rfl _ hwin'
    obtain ⟨c1, c2, c3⟩ := rcWit_spec (rd := rd) ⟨y, t1, t2, r1, r2, r3⟩
    have e0 : τ (W + 9 * i) = wBound 11 := gconst _ _ (mI' _ (by simp [gcIterAtO]))
    obtain ⟨e2, e3, e1⟩ := grc (W + 2 - i) (W + 9 * i + 1) (W + 9 * i + 2) (W + 9 * i + 3)
      (W + 9 * i) (by omega) (by omega) (mI' _ (by simp [gcIterAtO]))
    have e4 : τ (W + 9 * i + 4) = word 2048 0 := gconst _ _ (mI' _ (by simp [gcIterAtO]))
    have e5 : τ (W + 9 * i + 5) = τ (W + 9 * i - 1) * τ (W + 9 * i + 4) :=
      gmul _ _ _ (by omega) (by omega) (by omega) (mI' _ (by simp [gcIterAtO]))
    have e6 : τ (W + 9 * i + 6) = τ 1 * τ (W + 2 - i) :=
      gmul _ _ _ (by omega) (by omega) (by omega) (mI' _ (by simp [gcIterAtO]))
    have e7 : τ (W + 9 * i + 7) = rdAt rd (τ (W + 9 * i + 6)) off :=
      gload _ _ _ (by omega) (by rw [gcLen, hWd]; omega) (mI' _ (by simp [gcIterAtO]))
    have e8 : τ (W + 9 * i + 8) = τ (W + 9 * i + 5) + τ (W + 9 * i + 7) :=
      gadd _ _ _ (mI' _ (by simp [gcIterAtO]))
    rw [ew, e0] at e1
    rw [ew] at e2
    rw [τ1, ew] at e6
    rw [e6, rdAt_of_loadHolds (winTab_loadO ht hwin')] at e7
    rw [ep, e4] at e5
    rw [e5, e7] at e8
    have h1' : τ (W + 9 * i + 1) = (rcWit rd (gen ^ (gcV b (σ w) i % 2 ^ 11)) (wBound 11)).1 := by
      rw [e1]
      exact ((eq_mul_inv_iff_mul_eq₀ (gne _)).2 (by rw [mul_comm]; exact c2.symm)).symm
    rw [h1', rdAt_of_loadHolds c3] at e3
    rw [rdAt_of_loadHolds c1] at e2
    intro r hr
    rw [gi r hr]
    interval_cases r
    · rw [Nat.add_zero, e0]; rfl
    · rw [h1']; rfl
    · rw [e2]; rfl
    · rw [e3]; rfl
    · rw [e4]; rfl
    · rw [e5]; rfl
    · rw [e6]; rfl
    · rw [e7]; rfl
    · rw [e8]
      show _ = eOfNat (gcV b (σ w) i)
      have hp := gcV_pred (b := b) (σ w) h1 h2'
      have h64 : 2 ^ 11 * gcV b (σ w) (i - 1) < 2 ^ 64 := by
        rw [hp]
        exact lt_of_le_of_lt (Nat.mul_div_le _ _) (gcV_lt (σ w) _)
      rw [horner_step h64 hwin', hp, Nat.div_add_mod]
  have hiter : ∀ i, 1 ≤ i → i ≤ W → ∀ r < 9, τ (W + 9 * i + r) = G (W + 9 * i + r) := by
    intro i h1
    induction i, h1 using Nat.le_induction with
    | base =>
      intro h2
      refine step 1 le_rfl h2 ?_
      rw [show W + 9 * 1 - 1 = W + 2 + 6 by omega]
      exact hhead 6 (by omega)
    | succ i hi ih =>
      intro h2
      refine step (i + 1) (by omega) h2 ?_
      rw [show W + 9 * (i + 1) - 1 = W + 9 * i + 8 by omega]
      exact ih (by omega) 8 (by omega)
  -- the tail
  have htail : ∀ r < 7, τ (10 * W + 9 + r) = G (10 * W + 9 + r) := by
    have gt : ∀ r, G (10 * W + 9 + r) = gcTailVal b (σ w) r := fun r ↦ by
      rw [← hG, ← hWd]; exact gv_tail
    have ea : τ (10 * W + 8) = eOfNat (gcV b (σ w) W) := by
      rw [show 10 * W + 8 = W + 9 * W + 8 by ring, hiter W hW1 le_rfl 8 (by omega), ← hG, ← hWd]
      exact gv_acc le_rfl
    have e0 : τ (10 * W + 9) = word (2 ^ b) 0 := gconst _ _ (mT _ (by simp [gcTailPre, hWd]))
    have e1 : τ (10 * W + 10) = τ (10 * W + 8) * τ (10 * W + 9) :=
      gmul _ _ _ (by omega) (by omega) (by omega) (mT _ (by simp [gcTailPre, hWd]))
    have e2 : τ (10 * W + 11) = τ 0 + τ (10 * W + 10) := gadd _ _ _ (mT _ (by simp [gcTailPre, hWd]))
    have e3 : τ (10 * W + 12) = word 2 1 := gconst _ _ (mT _ (by simp [gcTailPre, hWd]))
    have e4 : τ (10 * W + 13) = τ (10 * W + 11) * τ (10 * W + 12) :=
      gmul _ _ _ (by omega) (by omega) (by omega) (mT _ (by simp [gcTailPre, hWd]))
    have e5 : τ (10 * W + 14) = word (2 ^ b) 0 := gconst _ _ (mT _ (by simp [gcTailPre, hWd]))
    have e6 : τ (10 * W + 15) = τ (10 * W + 8) * τ (10 * W + 14) :=
      gmul _ _ _ (by omega) (by omega) (by omega) (mT _ (by simp [gcTailPre, hWd]))
    rw [ea, e0] at e1
    rw [τ0, e1] at e2
    rw [e2, e3] at e4
    rw [ea, e5] at e6
    intro r hr
    rw [gt r]
    interval_cases r
    · rw [Nat.add_zero, e0]; rfl
    · rw [e1]; simp only [gcTailVal, hWd]
    · rw [e2]; simp only [gcTailVal, hWd]
    · rw [e3]; rfl
    · rw [e4]; simp only [gcTailVal, hWd]
    · rw [e5]; rfl
    · rw [e6]; simp only [gcTailVal, hWd]
  -- every own value
  intro k hk2 hkL
  rw [gcLen, hWd] at hkL
  rw [← τk k hk2]
  rcases Nat.lt_or_ge k (W + 2) with h | h
  · have := hwins (k - 2) (by omega)
    rwa [show 2 + (k - 2) = k by omega] at this
  rcases Nat.lt_or_ge k (W + 9) with h' | h'
  · have := hhead (k - (W + 2)) (by omega)
    rwa [show W + 2 + (k - (W + 2)) = k by omega] at this
  rcases Nat.lt_or_ge k (10 * W + 9) with h'' | h''
  · have := hiter ((k - W) / 9) (by omega) (by omega) ((k - W) % 9) (Nat.mod_lt _ (by omega))
    rwa [show W + 9 * ((k - W) / 9) + (k - W) % 9 = k by omega] at this
  · have := htail (k - (10 * W + 9)) (by omega)
    rwa [show 10 * W + 9 + (k - (10 * W + 9)) = k by omega] at this

/-- **`grind_check` inlined, evaluated: its table reads' pointers** are the tables' words `tabs·g^e`,
`e < 2^11`: the head's, at `o + gcW b + 5`, and step `i + 1`'s, at `o + gcW b + 9 (i + 1) + 4`. -/
theorem gcInlineO_ptrs_of_good {b o off : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V}
    (hwo : w.idx < o) (hto : tabs.idx < o)
    (hg : ∀ s ∈ gcInlineOT b o off w tabs, GoodS rd S wo σ s)
    (hS : ∀ a ∈ S, loadInto o (o + (gcLen b - 2)) a = false)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ tabs * gen ^ off))
    (hwin : ∀ j ≤ gcW b, wo (o + j) = gcWin b (σ w) j) :
    (∃ e < 2 ^ 11, σ (.n (o + gcW b + 5)) = σ tabs * gen ^ e) ∧
      ∀ i < gcW b, ∃ e < 2 ^ 11, σ (.n (o + gcW b + 9 * (i + 1) + 4)) = σ tabs * gen ^ e := by
  have hv := gcInlineO_vals_of_good hb hwo hto hg hS hrc ht hwin
  obtain ⟨hT1, hT, hsum⟩ := gc_shape b hb
  refine ⟨⟨gcV b (σ w) 0, ?_, ?_⟩, fun i hi ↦ ⟨gcV b (σ w) (i + 1) % 2 ^ 11, Nat.mod_lt _ (by positivity), ?_⟩⟩
  · have hV0 : gcV b (σ w) 0 < 2 ^ gcTop b := by
      unfold gcV
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_zero,
        show gcTop b + (b + 11 * gcW b) = 64 by omega]
      exact kToNat_lt _
    exact lt_of_lt_of_le hV0 (Nat.pow_le_pow_right (by decide) hT)
  · have := hv (gcW b + 7) (by omega) (by unfold gcLen; omega)
    rw [show o + (gcW b + 7) - 2 = o + gcW b + 5 by omega] at this
    rw [this]
    unfold gcVals
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left rfl]
  · have := hv (gcW b + 9 * (i + 1) + 6) (by omega) (by unfold gcLen; omega)
    rw [show o + (gcW b + 9 * (i + 1) + 6) - 2 = o + gcW b + 9 * (i + 1) + 4 by omega,
      gv_iter (by omega) (by omega) (by omega)] at this
    rw [this]
    rfl

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
