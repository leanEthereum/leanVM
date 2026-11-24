/-
  LeanVM.Guest.B1.Place.ArmMuteDef

  The check that an arm of `open_stacked` pops nothing itself and calls only `level_queries` or functions with no witness hint in their subtrees, and what it gives.
-/

module

public import LeanVM.Guest.B1.Common.NoWitMute
public import LeanVM.Guest.B1.Whir.HelperTables
public import LeanVM.Guest.B1.Place.ArmRoots

/-!
# The arms' mute check

* `lqNameB g`: `g` names an entry of `lqTable`;
* `armS g`: `g` is such a name or passes `noWitJ`;
* `armMuteOk name j`: function `j` is an arm named `name`, has no witness hint in its body, and its callees have
  indices, decided by the kernel per arm (`ArmOkA`, `ArmOkB`);
* `nwLoc`: `noWitJ`'s own step (`noWitJ_succ`); `NwRootsOk`: every root (`armRoots`) names an entry of `lqTable` or
  has no witness hint in its subtree, from the groups' checks (`nwRootsOk_of`);
* `armMute_find`: so an arm's body is mute in `armS`.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

/-- `g` names an entry of `lqTable`. -/
def lqNameB (g : String) : Bool := lqTable.any (·.1 == g)

/-- A name of `lqTable`, or a function passing `noWitJ`. -/
noncomputable def armS (g : String) : Bool := lqNameB g || noWitS g

/-- **Function `j`, named `name`, is an arm, pops nothing itself, and its callees have indices** (each
`level_queries` or with no witness hint in its subtree, `armMute_find`, by the roots' check). -/
noncomputable def armMuteOk (name : String) (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | some fn => fn.name == name && armIdxs.contains j && Stmt.noWitList fn.body &&
      (Stmt.blockCallees fn.body).all fun g => (calleeIdx j g).isSome
  | none => false

/-- `noWitJ`'s own step on function `j`: no witness hint in its body, its callees indexed. -/
noncomputable def nwLoc (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | some fn => Stmt.noWitList fn.body && (Stmt.blockCallees fn.body).all (fun g => (calleeIdx j g).isSome)
  | none => false

theorem noWitJ_succ (d j : ℕ) :
    noWitJ (d + 1) j = (nwLoc j && (Data.calleesJ j).all fun k ↦ k == j || noWitJ d k) := by
  rw [noWitJ, nwLoc]
  cases coreProgram[j]? <;> rfl

/-- Root `k` names an entry of `lqTable`. -/
noncomputable def lqRootS (k : ℕ) : Bool := lqNameB ((Data.nameT.find k).getD "")

/-- **Each root names an entry of `lqTable` or has no witness hint in its subtree**, from the groups' checks
(`ArmFree0` to `ArmFree5`). -/
def NwRootsOk : Prop := ∀ k ∈ armRoots, lqRootS k = true ∨ ∃ d, noWitJ d k = true

theorem nwRootsOk_of (e0 : armGrpOk nwLoc lqRootS 0 = true) (e1 : armGrpOk nwLoc lqRootS 1 = true)
    (e2 : armGrpOk nwLoc lqRootS 2 = true) (e3 : armGrpOk nwLoc lqRootS 3 = true)
    (e4 : armGrpOk nwLoc lqRootS 4 = true) (e5 : armGrpOk nwLoc lqRootS 5 true = true) : NwRootsOk :=
  have s := fun {i last} (e : armGrpOk nwLoc lqRootS i last = true) ↦
    armGrpOk_sound (J := noWitJ) (fun _ ↦ rfl) noWitJ_succ e
  armRoots_all (s e0) (s e1) (s e2) (s e3) (s e4) (s e5)

theorem armMute_find (hR : NwRootsOk) {name : String} {j : ℕ} (h : armMuteOk name j = true) :
    ∃ fn, coreProgram.find? name = some fn ∧ Stmt.muteList armS fn.body = true := by
  unfold armMuteOk at h
  split at h
  · next fn hj =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.all_eq_true] at h
    obtain ⟨⟨⟨hn, hA⟩, hw⟩, hc⟩ := h
    refine ⟨fn, coreProgram_find?_at hj hn, Stmt.muteList_of_noWit fn.body hw fun g hg ↦ ?_⟩
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hc g hg)
    obtain ⟨hr, hnk⟩ := calleeIdx_root hA hk
    rcases hR k hr with hs | ⟨d, hd⟩
    · rw [lqRootS, hnk, Option.getD_some] at hs
      simp [armS, hs]
    · simp [armS, noWitS_iff.mpr ⟨d, k, calleeIdx_spec hk, hd⟩]
  · exact absurd h Bool.false_ne_true

end
end LeanVM.Guest.B1.Arm
