/-
  LeanVM.Guest.Backend.Guest.B2.Locs

  The test of one function's places against its certificate's cells, as a function of the
  places, for a kernel walk that has them.
-/

module

public import LeanVM.Guest.Glob
public import LeanVM.Guest.Backend.Guest.B2.Residual

/-!
# One function's places against its cells

`agreeWith locs j` is function `j`'s places `locs`, its certificate's cells and its residual
entries (`resOf`); `locsOkAt i locs` is `Agree.fnOk` of entry `i` of the back end's input
(function `i + 1`) on the places `locs`. `Bridge.lean`'s `LocsAgree` is `locsOkAt i` of each
function's placed locations.
-/

namespace LeanVM.Guest.Backend.B2

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- The residual entries of function `f` (`residual`). -/
def resOf (f : String) : List (V × Res) := ((residual.find? (·.1 == f)).map (·.2.2)).getD []

/-- Function `j`'s places `locs` against its certificate's cells and its residual entries. -/
noncomputable def agreeWith (locs : VMap Loc) (j : ℕ) : Agree :=
  ⟨fun v => locs[v]?, (certOf j).locs, resOf (coreOf j).name⟩

/-- **The test of entry `i` of the back end's input** (function `i + 1`) on the places `locs`. -/
noncomputable def locsOkAt (i : ℕ) (locs : VMap Loc) : Bool :=
  (agreeWith locs (i + 1)).fnOk (coreOf (i + 1))

end
end LeanVM.Guest.Backend.B2
