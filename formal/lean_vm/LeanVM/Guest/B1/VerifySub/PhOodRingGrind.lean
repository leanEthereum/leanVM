/-
  LeanVM.Guest.B1.VerifySub.PhOodRingGrind

  `grind_check` inlined where its tables `q·g^off` are folded into its reads: sound.
-/

module

public import LeanVM.Guest.B1.Bits.Grind

/-!
# `grind_check` with folded tables

`verify_sub` passes `tabs = g_squares·g^WIN_TAB_AT`, which the compiler folds into the table reads:
each `tabs[w]` is a load at offset `178` from `g_squares·w`. `gcPreAt b off` is `gcPre b` with its
two kinds of table reads at offset `off`, `gcInlineAt` its inlining. `gcInlineAt_sound`: on the
tables at `σ tabs·g^off`, the word passes the proof of work, by `gc_sound` on the valuation that
multiplies the tables and every table address by `g^off` (`gcShift`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `gcHead b`, its table read at offset `off`. -/
def gcHeadAt (b off : ℕ) : List Stmt :=
  [.atom (.hint (.windowsExp (.n 0) b 11 (gcW b)
      (.stack ((List.range (gcW b)).map fun j => .n (2 + j))))),
    .atom (.hint (.windowsExp (.n 0) (b + 11 * gcW b) (gcTop b) 1 (.stack [.n (gcW b + 2)]))),
    .atom (.const (.n (gcW b + 3)) (wBound (gcTop b))),
    .atom (.rangeCheck (.n (gcW b + 2)) (.n (gcW b + 4)) (.n (gcW b + 5)) (.n (gcW b + 6))
      (.n (gcW b + 3))),
    .atom (.mul (.n (gcW b + 7)) (.n 1) (.n (gcW b + 2))),
    .atom (.load (.n (gcW b + 8)) (.n (gcW b + 7)) off)]

/-- `gcIterAt W i`, its table read at offset `off`. -/
def gcIterAtOff (W i off : ℕ) : List Stmt :=
  [.atom (.const (.n (W + 9 * i)) (wBound 11)),
    .atom (.rangeCheck (.n (W + 2 - i)) (.n (W + 9 * i + 1)) (.n (W + 9 * i + 2))
      (.n (W + 9 * i + 3)) (.n (W + 9 * i))),
    .atom (.const (.n (W + 9 * i + 4)) (word 2048 0)),
    .atom (.mul (.n (W + 9 * i + 5)) (.n (W + 9 * i - 1)) (.n (W + 9 * i + 4))),
    .atom (.mul (.n (W + 9 * i + 6)) (.n 1) (.n (W + 2 - i))),
    .atom (.load (.n (W + 9 * i + 7)) (.n (W + 9 * i + 6)) off),
    .atom (.add (.n (W + 9 * i + 8)) (.n (W + 9 * i + 5)) (.n (W + 9 * i + 7)))]

/-- **`grind_check`'s expansion, its table reads at offset `off`.** -/
def gcPreAt (b off : ℕ) : List Stmt :=
  gcHeadAt b off ++ ((List.range (gcW b)).map fun i => gcIterAtOff (gcW b) (i + 1) off).flatten ++
    gcTailPre b

/-- **`grind_check(w, q·g^off, b)` inlined**, the offset folded into its reads, its own values
from `.n o`. -/
def gcInlineAt (b o off : ℕ) (w tabs : V) : List Stmt :=
  Stmt.renameList (gcRen o w tabs) (gcPreAt b off)

/-- `GcHeadOk`, the read at offset `off`. -/
def GcHeadOkAt (rd : Reader) (σ : Val) (W T off : ℕ) : Prop :=
  σ (.n (W + 3)) = wBound T ∧
    (LoadHolds rd (σ (.n (W + 2))) 0 (σ (.n (W + 5))) ∧
      σ (.n (W + 3)) = σ (.n (W + 2)) * σ (.n (W + 4)) ∧
      LoadHolds rd (σ (.n (W + 4))) 0 (σ (.n (W + 6)))) ∧
    σ (.n (W + 7)) = σ (.n 1) * σ (.n (W + 2)) ∧
    LoadHolds rd (σ (.n (W + 7))) off (σ (.n (W + 8)))

/-- `GcIterOk`, the read at offset `off`. -/
def GcIterOkAt (rd : Reader) (σ : Val) (W i off : ℕ) : Prop :=
  σ (.n (W + 9 * i)) = wBound 11 ∧
    (LoadHolds rd (σ (.n (W + 2 - i))) 0 (σ (.n (W + 9 * i + 2))) ∧
      σ (.n (W + 9 * i)) = σ (.n (W + 2 - i)) * σ (.n (W + 9 * i + 1)) ∧
      LoadHolds rd (σ (.n (W + 9 * i + 1))) 0 (σ (.n (W + 9 * i + 3)))) ∧
    σ (.n (W + 9 * i + 4)) = word 2048 0 ∧
    σ (.n (W + 9 * i + 5)) = σ (.n (W + 9 * i - 1)) * σ (.n (W + 9 * i + 4)) ∧
    σ (.n (W + 9 * i + 6)) = σ (.n 1) * σ (.n (W + 2 - i)) ∧
    LoadHolds rd (σ (.n (W + 9 * i + 6))) off (σ (.n (W + 9 * i + 7))) ∧
    σ (.n (W + 9 * i + 8)) = σ (.n (W + 9 * i + 5)) + σ (.n (W + 9 * i + 7))

theorem holds_gcPreAt {C : CallRel} {rd : Reader} {σ : Val} (b off : ℕ) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gcPreAt b off) next kret ↔
      GcHeadOkAt rd σ (gcW b) (gcTop b) off ∧
        (∀ i < gcW b, GcIterOkAt rd σ (gcW b) (i + 1) off) ∧ GcTailOk σ (gcW b) b ∧ next := by
  rw [gcPreAt, holdsList_append, holdsList_append,
    holdsList_range_flatten _ _ (fun i => rfl)]
  simp only [gcHeadAt, gcIterAtOff, gcTailPre, GcHeadOkAt, GcIterOkAt, GcTailOk, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, true_and, and_true, and_assoc]

/-- The valuation with the tables `σ 1` and every table address multiplied by `g^off`. -/
noncomputable def gcShift (σ : Val) (W off : ℕ) : Val := fun v ↦
  if v.idx = 1 ∨ v.idx = W + 7 ∨ (W + 15 ≤ v.idx ∧ v.idx ≤ 10 * W + 6 ∧ (v.idx - (W + 6)) % 9 = 0)
  then σ v * gen ^ off else σ v

theorem gcShift_n (σ : Val) (W off k : ℕ) : gcShift σ W off (.n k) =
    if k = 1 ∨ k = W + 7 ∨ (W + 15 ≤ k ∧ k ≤ 10 * W + 6 ∧ (k - (W + 6)) % 9 = 0)
    then σ (.n k) * gen ^ off else σ (.n k) := rfl

theorem gcShift_keep {σ : Val} {W off k : ℕ}
    (h : ¬ (k = 1 ∨ k = W + 7 ∨ (W + 15 ≤ k ∧ k ≤ 10 * W + 6 ∧ (k - (W + 6)) % 9 = 0))) :
    gcShift σ W off (.n k) = σ (.n k) := by
  rw [gcShift_n, ite_eq_right h]

theorem gcShift_mul {σ : Val} {W off k : ℕ}
    (h : k = 1 ∨ k = W + 7 ∨ (W + 15 ≤ k ∧ k ≤ 10 * W + 6 ∧ (k - (W + 6)) % 9 = 0)) :
    gcShift σ W off (.n k) = σ (.n k) * gen ^ off := by
  rw [gcShift_n, ite_eq_left h]

theorem loadHolds_shift {rd : Reader} {p v : E} {off : ℕ} (h : LoadHolds rd p off v) :
    LoadHolds rd (p * gen ^ off) 0 v :=
  (loadHolds_mul_gen_pow rd p off 0 v).mpr (by simpa using h)

theorem gcShift_head {rd : Reader} {σ : Val} {W T off : ℕ} (h : GcHeadOkAt rd σ W T off) :
    GcHeadOk rd (gcShift σ W off) W T := by
  obtain ⟨h1, ⟨h2, h3, h4⟩, h5, h6⟩ := h
  have k2 : gcShift σ W off (.n (W + 2)) = σ (.n (W + 2)) := gcShift_keep (by omega)
  have k3 : gcShift σ W off (.n (W + 3)) = σ (.n (W + 3)) := gcShift_keep (by omega)
  have k4 : gcShift σ W off (.n (W + 4)) = σ (.n (W + 4)) := gcShift_keep (by omega)
  have k5 : gcShift σ W off (.n (W + 5)) = σ (.n (W + 5)) := gcShift_keep (by omega)
  have k6 : gcShift σ W off (.n (W + 6)) = σ (.n (W + 6)) := gcShift_keep (by omega)
  have k8 : gcShift σ W off (.n (W + 8)) = σ (.n (W + 8)) := gcShift_keep (by omega)
  have m1 : gcShift σ W off (.n 1) = σ (.n 1) * gen ^ off := gcShift_mul (by omega)
  have m7 : gcShift σ W off (.n (W + 7)) = σ (.n (W + 7)) * gen ^ off := gcShift_mul (by omega)
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [k3, h1]
  · rw [k2, k5]; exact h2
  · rw [k3, k2, k4]; exact h3
  · rw [k4, k6]; exact h4
  · rw [m7, m1, k2, h5]; ring
  · rw [m7, k8]; exact loadHolds_shift h6

theorem gcShift_iter {rd : Reader} {σ : Val} {W i off : ℕ} (hi : i < W)
    (h : GcIterOkAt rd σ W (i + 1) off) : GcIterOk rd (gcShift σ W off) W (i + 1) := by
  obtain ⟨h1, ⟨h2, h3, h4⟩, h5, h6, h7, h8, h9⟩ := h
  have kw : gcShift σ W off (.n (W + 2 - (i + 1))) = σ (.n (W + 2 - (i + 1))) :=
    gcShift_keep (by omega)
  have k0 : gcShift σ W off (.n (W + 9 * (i + 1))) = σ (.n (W + 9 * (i + 1))) :=
    gcShift_keep (by omega)
  have k1 : gcShift σ W off (.n (W + 9 * (i + 1) + 1)) = σ (.n (W + 9 * (i + 1) + 1)) :=
    gcShift_keep (by omega)
  have k2 : gcShift σ W off (.n (W + 9 * (i + 1) + 2)) = σ (.n (W + 9 * (i + 1) + 2)) :=
    gcShift_keep (by omega)
  have k3 : gcShift σ W off (.n (W + 9 * (i + 1) + 3)) = σ (.n (W + 9 * (i + 1) + 3)) :=
    gcShift_keep (by omega)
  have k4 : gcShift σ W off (.n (W + 9 * (i + 1) + 4)) = σ (.n (W + 9 * (i + 1) + 4)) :=
    gcShift_keep (by omega)
  have k5 : gcShift σ W off (.n (W + 9 * (i + 1) + 5)) = σ (.n (W + 9 * (i + 1) + 5)) :=
    gcShift_keep (by omega)
  have k7 : gcShift σ W off (.n (W + 9 * (i + 1) + 7)) = σ (.n (W + 9 * (i + 1) + 7)) :=
    gcShift_keep (by omega)
  have k8 : gcShift σ W off (.n (W + 9 * (i + 1) + 8)) = σ (.n (W + 9 * (i + 1) + 8)) :=
    gcShift_keep (by omega)
  have kp : gcShift σ W off (.n (W + 9 * (i + 1) - 1)) = σ (.n (W + 9 * (i + 1) - 1)) :=
    gcShift_keep (by omega)
  have m1 : gcShift σ W off (.n 1) = σ (.n 1) * gen ^ off := gcShift_mul (by omega)
  have m6 : gcShift σ W off (.n (W + 9 * (i + 1) + 6)) = σ (.n (W + 9 * (i + 1) + 6)) * gen ^ off :=
    gcShift_mul (by omega)
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k0, h1]
  · rw [kw, k2]; exact h2
  · rw [k0, kw, k1]; exact h3
  · rw [k1, k3]; exact h4
  · rw [k4, h5]
  · rw [k5, kp, k4]; exact h6
  · rw [m6, m1, kw, h7]; ring
  · rw [m6, k7]; exact loadHolds_shift h8
  · rw [k8, k5, k7]; exact h9

theorem gcShift_tail {σ : Val} {W b off : ℕ} (h : GcTailOk σ W b) : GcTailOk (gcShift σ W off) W b := by
  have k : ∀ j, j ≤ 15 → 8 ≤ j → gcShift σ W off (.n (10 * W + j)) = σ (.n (10 * W + j)) :=
    fun j h1 h2 ↦ gcShift_keep (by omega)
  have k0 : gcShift σ W off (.n 0) = σ (.n 0) := gcShift_keep (by omega)
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := h
  rw [GcTailOk, k 9 (by omega) (by omega), k 10 (by omega) (by omega), k 11 (by omega) (by omega),
    k 12 (by omega) (by omega), k 13 (by omega) (by omega), k 14 (by omega) (by omega),
    k 15 (by omega) (by omega), k 8 (by omega) (by omega), k0]
  exact ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩

/-- **`grind_check` inlined with folded tables is sound**: on a memory image of `2^κ ≥ 2^11` words
whose `σ tabs·g^off` holds the windows, the word passes the proof of work. -/
theorem gcInlineAt_sound {C : CallRel} {κ : ℕ} (hκ : κ ≤ 32) (hκ11 : 11 ≤ κ) (L : MemoryImage κ)
    {σ : Val} {b o off : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V}
    (ht : WinTabs L.read (σ tabs * gen ^ off)) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C L.read σ (gcInlineAt b o off w tabs) next kret) :
    ((σ w).limb 0).lane.toNat % 2 ^ b = 0 ∧ next := by
  rw [gcInlineAt, Stmt.holdsList_rename, holds_gcPreAt] at h
  obtain ⟨hh, hi, htl, hn⟩ := h
  have e0 : (σ ∘ gcRen o w tabs) (.n 0) = σ w := by simp [gcRen]
  have e1 : (σ ∘ gcRen o w tabs) (.n 1) = σ tabs := by simp [gcRen]
  have ht' : WinTabs L.read (gcShift (σ ∘ gcRen o w tabs) (gcW b) off (.n 1)) := by
    rw [gcShift_mul (k := 1) (W := gcW b) (by omega), e1]; exact ht
  have hs := gc_sound hκ hκ11 L (gc_shape b hb) ht' (gcShift_head hh)
    (fun i hi' ↦ gcShift_iter hi' (hi i hi')) (gcShift_tail htl)
  rw [gcShift_keep (k := 0) (W := gcW b) (by omega), e0] at hs
  exact ⟨hs, hn⟩

end
end LeanVM.Guest.B1
