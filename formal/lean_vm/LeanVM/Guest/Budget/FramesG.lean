/-
  LeanVM.Guest.Budget.FramesG

  b2c's frame sizes against the certificates': equal on every function, `fsW` zero elsewhere.
-/

module

public import LeanVM.Guest.Budget.FramesV
public import LeanVM.Guest.B2C.Cells

/-!
# b2c's frames within the certificates'

`fs_within_fsW`: on every function of the guest `B2C.fs` is `fsW`, the frame sizes the certificates
were made at (`main`'s with the jump table, the others at least `2`), by one kernel check over the
indices (`wfsJ_eq_fsN`). `not_fs_le_fsW`: off the functions it is not, `fsW` being `0` at a tail key
(`fsW_tailKey`) and `B2C.fs` at least `2`. `B2C.fs_tailKey_le` is the tails' part.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- **The certificates' frame sizes are b2c's**, by index, by the kernel. -/
theorem wfsJ_eq_fsN : (List.range coreProgram.length).all (fun i ↦ Data.wfsJ i == B2C.fsN (i + 1)) = true := by
  rw [coreProgram_length]
  set_option maxRecDepth 100000 in decide +kernel

private theorem idxOf_of_find' {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) :
    ∃ j, B2C.idxOf f = some j := by
  have h' : List.find? (fun g ↦ g.name == f) coreProgram = some fn := h
  have hany : coreProgram.any (fun g ↦ g.name == f) = true :=
    List.any_eq_true.mpr ⟨fn, List.mem_of_find?_eq_some h', List.find?_some (p := fun g : Fn ↦ g.name == f) h'⟩
  rw [← List.findIdx?_isSome] at hany
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hany
  exact ⟨i + 1, by unfold B2C.idxOf Core.Program.indexOf?; rw [hi]; rfl⟩

/-- **b2c's frame sizes are the certificates' on the guest's functions.** -/
theorem fs_eq_fsW {g : String} {fn : Fn} (hg : coreProgram.find? g = some fn) : B2C.fs g = fsW g := by
  obtain ⟨j, hj⟩ := idxOf_of_find' hg
  obtain ⟨i, rfl, hi, hn, -, -, hfs, -⟩ := B2C.fn_of_idx hj
  have h := List.all_eq_true.mp wfsJ_eq_fsN i (List.mem_range.mpr hi)
  rw [beq_iff_eq] at h
  rw [hfs, fsW, ← hn, coreIdx_getElem hi, h]

/-- **b2c's frame sizes within the certificates' on functions** (`FramesWithin.fs`). -/
theorem fs_within_fsW : FnWithin coreProgram B2C.fs fsW := fun _ _ hg ↦ (fs_eq_fsW hg).le

/-- The certificates' frame size at a tail key is `0`: no function has its name. -/
theorem fsW_tailKey (f : String) : fsW (tailKey f) = 0 := by
  have hn : tailKey f ∉ coreProgram.map (·.name) := by
    intro hm
    obtain ⟨g, hg, he⟩ := List.mem_map.mp hm
    have h0 := B2C.indexOf_tailKey f
    unfold Core.Program.indexOf? at h0
    have := List.findIdx?_eq_none_iff.mp h0 g hg
    simp [he] at this
  unfold fsW coreIdx
  rw [List.idxOf_eq_length hn, List.length_map, coreProgram_length]
  decide +kernel

/-- **b2c's frame sizes are not within the certificates' everywhere**: at `main`'s tail key `B2C.fs` is
at least `2`, `fsW` is `0`. So `FramesWithin.fs` is stated on functions. -/
theorem not_fs_le_fsW : ¬ ∀ g, B2C.fs g ≤ fsW g := fun h ↦ by
  have h1 := h (tailKey "main")
  rw [fsW_tailKey] at h1
  have := B2C.two_le_fs (tailKey "main")
  omega

end

end LeanVM.Guest.Budget
