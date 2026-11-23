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


/-- Every deployed frame is below `2^32`. -/
theorem fs_lt (f : String) : B2C.fs f < 2 ^ 32 :=
  lt_of_lt_of_le (B2C.fs_lt f) (by norm_num)

/-- **`verify_sub`'s callees' words with `open_stacked`'s, at `B2C.fs`.** -/
noncomputable def vsWordsOs : B1.VerifySub.VsWordsOs B2C.fs where
  toVsWords := vsWords
  Bnd := wSBos
  hleaf := osLeafBounds
  hfs := fs_lt
  htl := B2C.fs_tailKey_le

end
end LeanVM.Guest.Count
