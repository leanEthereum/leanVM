/-
  LeanVM.Guest.Count.VsWordsOs

  `verify_sub`'s callees' words with `open_stacked`'s at the deployed frame sizes
  (`VsWordsOs B2C.fs`): `vsWords` and `open_stacked`'s arms' callees from the words certificates
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
theorem fs_lt (f : String) : B2C.fs f < 2 ^ 32 := by
  have hall : Data.frameSizes.all (fun x ↦ decide (x < 2 ^ 32)) = true := by decide +kernel
  have hat : ∀ j, fsAt j < 2 ^ 32 := fun j ↦ by
    unfold fsAt
    rw [List.getD_eq_getElem?_getD]
    cases hj : Data.frameSizes[j]? with
    | none => simp
    | some x =>
      simpa using of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_of_getElem? hj))
  unfold B2C.fs
  split
  · unfold B2C.mainFrame; norm_num
  · exact max_lt (by norm_num) (hat _)
  · norm_num

/-- **`verify_sub`'s callees' words with `open_stacked`'s, at `B2C.fs`.** -/
noncomputable def vsWordsOs : B1.VerifySub.VsWordsOs B2C.fs where
  toVsWords := vsWords
  Bnd := wSB
  hleaf := osLeafBounds
  hfs := fs_lt

end
end LeanVM.Guest.Count
