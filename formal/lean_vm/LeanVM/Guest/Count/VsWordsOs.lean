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


/-- **`verify_sub`'s callees' words with `open_stacked`'s, at `B2C.fs`.** -/
noncomputable def vsWordsOs : B1.VerifySub.VsWordsOs B2C.fs where
  toVsWords := vsWords
  Bnd := wSB
  hleaf := osLeafBounds

end
end LeanVM.Guest.Count
