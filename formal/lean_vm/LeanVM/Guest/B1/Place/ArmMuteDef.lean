/-
  LeanVM.Guest.B1.Place.ArmMuteDef

  The check that an arm of `open_stacked` pops nothing itself and calls only `level_queries` or functions with no witness hint in their subtrees, and what it gives.
-/

module

public import LeanVM.Guest.B1.Common.NoWitMute
public import LeanVM.Guest.B1.Whir.HelperTables
public import LeanVM.Guest.B1.Place.FreeMaskData

/-!
# The arms' mute check

* `lqNameB g`: `g` names an entry of `lqTable`;
* `armS g`: `g` is such a name or passes `noWitness`;
* `armMuteOk name j`: function `j` is named `name`, has no witness hint in its body, and each of its callees is one of the arms' (its bit in `armCalleeMask`), decided by the kernel per arm (`ArmMuteA`, `ArmMute6` to `ArmMute10`); the arms' callees are entries of `lqTable` or have no witness hint in their subtrees, decided once for every arm (`ArmMuteNeedOk`);
* `armMute_find`: such a function's body is mute in `armS`.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

/-- `g` names an entry of `lqTable`. -/
def lqNameB (g : String) : Bool := lqTable.any (·.1 == g)

/-- A name of `lqTable`, or a function passing `noWitness`. -/
noncomputable def armS (g : String) : Bool := lqNameB g || noWitS g

/-- **Function `j`, named `name`, pops nothing itself, and each of its callees is one of the arms'
(`armCalleeMask`), whose `level_queries` callees are entries of `lqTable` and the others have no
witness hint in their subtrees (`ArmMuteNeedOk`).** -/
noncomputable def armMuteOk (name : String) (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | some fn => fn.name == name && Stmt.noWitList fn.body &&
      (Stmt.blockCallees fn.body).all (maskCallee armCalleeMask j)
  | none => false

/-- The arms' callees' facts the mute check reads, decided once (`Place/FreeNoWitOk`, `Place/FreeLq`). -/
def ArmMuteNeedOk : Prop :=
  (∀ k ∈ armNoWitNeed, noWitJ 8 k = true) ∧ ∀ k ∈ armLqNeed, (Data.nameT.find k).all lqNameB = true

theorem armMute_find (hN : ArmMuteNeedOk) {name : String} {j : ℕ} (h : armMuteOk name j = true) :
    ∃ fn, coreProgram.find? name = some fn ∧ Stmt.muteList armS fn.body = true := by
  unfold armMuteOk at h
  split at h
  · next fn hj =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨hn, hw⟩, hc⟩ := h
    refine ⟨fn, coreProgram_find?_at hj hn, Stmt.muteList_of_noWit fn.body hw fun g hg ↦ ?_⟩
    obtain ⟨k, hk, hk', hg'⟩ := maskCallee_mem armCalleeMask_mute (hc g hg)
    rcases List.mem_append.mp hk with hk | hk
    · simp [armS, noWitS_iff.mpr ⟨8, k, hk', hN.1 k hk⟩]
    · have hq : lqNameB g = true := by simpa [hg'] using hN.2 k hk
      simp [armS, hq]
  · exact absurd h Bool.false_ne_true

end
end LeanVM.Guest.B1.Arm
