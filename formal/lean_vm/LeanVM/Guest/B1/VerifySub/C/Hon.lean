/-
  LeanVM.Guest.B1.VerifySub.C.Hon

  `verify_sub`'s honest valuation on a memory: its evaluation list evaluated from the arguments,
  loads read from the memory, allocations, hints' and callees' words from an oracle. What it
  gives by position, and the statements that hold by it alone (after B1-c's `Hon`).
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Flat
public import LeanVM.Guest.B1.Fwd.FlatIte
public import LeanVM.Guest.B1.Fwd.NotStored
public import LeanVM.Guest.B1.Tables.Basic

/-!
# The honest valuation

`vsσ rd w args`: `vsEvL` evaluated (`Fwd.ev`) on the memory `rd` and the oracle `w` from the
arguments `args`. Each statement of the list satisfies its equations (`GoodS`) with the stores
`vsSL` (`vs_good`); the parameters are the arguments (`vsC_param`). `verify_sub` has no `ite`.

By position of `vsCPre` (the kernel comparing the statements read): `vs_goodL` (a block's
equations), `vs_read` (a read gives the word the memory holds), `vs_readH`, `vsh_store`.
`vs_block`: a block's statements satisfy `VSH` when the ones evaluation alone does not settle do.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables

@[expose] public section

/-- The stores of the evaluation list. -/
def vsSL : List Atom := storesOf 6 vsEvL

/-- The pointers of `verify_sub`'s stores (`vsSL_ptrs`). -/
def vsStorePtrs : List ℕ := [5, 26, 127, 139, 346, 427, 664, 665]

theorem vsSL_ptrs : vsSL.all (ptrInB vsStorePtrs) = true := by decide +kernel

/-- `a ∉ vsSL` by the read's numbers, its pointer first (`Fwd.notStoredB`): without evaluating
`vsSL` when no store goes through the read's pointer. -/
instance (priority := high) instDecidableNotMemVsSL (a : Atom) : Decidable (a ∉ vsSL) :=
  decidable_of_iff _ (notStoredB_iff vsSL_ptrs a)

theorem vs_chk' : chk 6 vsEvL = some 1728 := by decide +kernel

/-- **The honest valuation** of `verify_sub`. -/
noncomputable def vsσ (rd : Reader) (w : ℕ → E) (args : List E) : Val :=
  B1.Val.ofArgs (ev rd w args vsEvL)

/-- The equations of a block, as one conjunction. -/
def VsGoodL (rd : Reader) (w : ℕ → E) (σ : Val) : List Stmt → Prop
  | [] => True
  | s :: ss => GoodS rd vsSL w σ (fixNe s) ∧ VsGoodL rd w σ ss

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vs_good (hl : args.length = 6) : ∀ s ∈ vsEvL, GoodS rd vsSL w (vsσ rd w args) s := by
  have h := (ev_spec rd w vsEvL args (by rw [hl]; exact vs_chk')).2.2
  rw [hl] at h
  exact h

theorem vsC_param (hl : args.length = 6) {i : ℕ} (hi : i < 6) :
    vsσ rd w args (.n i) = args.getD i 0 :=
  ev_params rd w (by rw [hl]; exact vs_chk') (by rw [hl]; exact hi)

/-- A statement of the body is in the list as `fixNe` reads it (no `ite` in the body). -/
theorem vsEvL_mem {s : Stmt} (hs : s ∈ vsCPre) (hni : ∀ c z n, s ≠ .ite c z n) :
    fixNe s ∈ vsEvL :=
  List.mem_map_of_mem (mem_flatIte_of hni hs)

theorem vs_mem_slice {n : ℕ} {blk : List Stmt}
    (heq : tbStmtsEqb blk ((vsCPre.drop n).take blk.length) = true) {s : Stmt} (hs : s ∈ blk) :
    s ∈ vsCPre := by
  rw [tbStmtsEqb_sound heq] at hs
  exact List.mem_of_mem_drop (List.mem_of_mem_take hs)

theorem vs_goodS (hl : args.length = 6) {s : Stmt} (hs : s ∈ vsCPre) :
    GoodS rd vsSL w (vsσ rd w args) (fixNe s) := by
  by_cases hi : ∃ c z n, s = .ite c z n
  · obtain ⟨c, z, n, rfl⟩ := hi
    trivial
  · exact vs_good hl _ (vsEvL_mem hs fun c z n h ↦ hi ⟨c, z, n, h⟩)

/-- An atom evaluation alone settles (a constant, a sum, a copy, a product of older values, a
hint) holds. -/
theorem vs_auto (hl : args.length = 6) {s : Stmt} (hs : s ∈ vsCPre) (ha : autoB s = true) :
    VSH (coreProgram.Rel rd) rd (vsσ rd w args) s := by
  cases s with
  | atom a =>
    have hg := vs_goodS (rd := rd) (w := w) hl hs
    rw [fixNe_atom] at hg
    simp only [autoB, Bool.or_eq_true] at ha
    rcases ha with ha | ha
    · have e : fixA a = a := by
        cases a with
        | assertNe => simp [pureB] at ha
        | _ => rfl
      rw [e] at hg
      exact holds_of_pure (S := vsSL) (w := w) ha hg
    · cases a with
      | hint _ => exact True.intro
      | _ => simp only [hintB, Bool.false_eq_true] at ha
  | _ => simp only [autoB, Bool.false_eq_true] at ha

/-- **A block's statements hold** when the ones evaluation alone does not settle (`rest`) do. -/
theorem vs_block (hl : args.length = 6) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((vsCPre.drop n).take blk.length) = true) (rest : List Stmt)
    (hrest : tbStmtsEqb (blk.filter (fun s ↦ !autoB s)) rest = true)
    (h : ∀ s ∈ rest, VSH (coreProgram.Rel rd) rd (vsσ rd w args) s) :
    ∀ s ∈ blk, VSH (coreProgram.Rel rd) rd (vsσ rd w args) s := by
  intro s hs
  cases ha : autoB s
  · exact h s (tbStmtsEqb_sound hrest ▸ List.mem_filter.mpr ⟨hs, by simp [ha]⟩)
  · exact vs_auto hl (vs_mem_slice heq hs) ha

end

end
end LeanVM.Guest.B1.VerifySub
