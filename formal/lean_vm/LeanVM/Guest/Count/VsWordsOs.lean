/-
  LeanVM.Guest.Count.VsWordsOs

  `verify_sub`'s callees' words with `open_stacked`'s at the deployed frame sizes
  (`VsWordsOs B2C.fs`): `vsWords` and `open_stacked`'s leaves and residual loops from the words
  certificates (`Count/Instances`).
-/

module

public import LeanVM.Guest.Count.VsWords
public import LeanVM.Guest.Count.Instances
public import LeanVM.Guest.B1.VerifySub.BoundsB

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- **`open_stacked`'s named callees' words**: `wSB` on the names `osKindOf` knows, `0` on the
others (the queries' callees and the loops, which `osBk` bounds by `osSpB`). -/
noncomputable def osBnd (f : String) : ℕ := if (B1.osKindOf f).isSome then wSB f else 0

theorem osLeafBoundsB : B1.OsLeafBounds B2C.fs osBnd := fun f K hK => by
  have h := osLeafBounds f K hK
  simpa [osBnd, hK] using h

/-- **`verify_sub`'s callees' words with `open_stacked`'s, at `B2C.fs`.** -/
noncomputable def vsWordsOs : B1.VerifySub.VsWordsOs B2C.fs where
  toVsWords := vsWords
  Bnd := osBnd
  Kr := fun f => wSK f - B2C.fs f
  hleaf := osLeafBoundsB
  hloop := fun μ r h1 h2 h3 h4 => osLoopBounds _ (by unfold B1.Whir.candidate; omega)

end
end LeanVM.Guest.Count
