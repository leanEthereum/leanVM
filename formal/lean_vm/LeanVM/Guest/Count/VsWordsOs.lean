/-
  LeanVM.Guest.Count.VsWordsOs

  `verify_sub`'s callees' words with `open_stacked`'s at the deployed frame sizes
  (`VsWordsOs Deployed.fs`): `vsWords` and `open_stacked`'s arms' callees from the words certificates
  (`Count/VsOsAll`).
-/

module

public import LeanVM.Guest.Count.VsWords
public import LeanVM.Guest.Count.VsBoundBase
public import LeanVM.Guest.Count.Instances
public import LeanVM.Guest.Count.VsOsAll
public import LeanVM.Guest.B1.VerifySub.BoundsB

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section


/-- Every deployed frame is below `2^32`: the compiler's sizes, by the kernel, and `main`'s. -/
theorem fs_lt (f : String) : Deployed.fs f < 2 ^ 32 := by
  have hall : Deployed.Data.frameSizes.all (fun x ↦ decide (x < 2 ^ 32)) = true := by decide +kernel
  have hat : ∀ j, Deployed.fsAt j < 2 ^ 32 := fun j ↦ by
    unfold Deployed.fsAt
    rw [List.getD_eq_getElem?_getD]
    cases hj : Deployed.Data.frameSizes[j]? with
    | none => simp
    | some x =>
      simpa using of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_of_getElem? hj))
  unfold Deployed.fs
  split
  · unfold Deployed.mainFrame; norm_num
  · exact max_lt (by norm_num) (hat _)
  · norm_num

/-- **`verify_sub`'s callees' words with `open_stacked`'s, at `Deployed.fs`.** -/
noncomputable def vsWordsOs : B1.VerifySub.VsWordsOs Deployed.fs where
  toVsWords := vsWords
  Bnd := wSB
  hleaf := osLeafBounds
  hfs := fs_lt

end
end LeanVM.Guest.Count
