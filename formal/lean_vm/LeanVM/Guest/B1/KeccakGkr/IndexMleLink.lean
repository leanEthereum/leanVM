/-
  LeanVM.Guest.B1.KeccakGkr.IndexMleLink

  `index_mle`'s soundness in the form the link's `index_side` takes as its hypothesis.
-/

module

public import LeanVM.Guest.B1.Link.IndexSide
public import LeanVM.Guest.B1.Link.IndexMle

namespace LeanVM.Guest.B1.KeccakGkr

open LeanVM.Guest.Core

@[expose] public section

/-- **`IndexMleSound` holds** (`Link/IndexSide.lean`'s hypothesis): `Link.index_mle_holds`. -/
theorem indexMleSound_core : Link.IndexMleSound coreProgram := Link.index_mle_holds

/-- `index_side`'s soundness, its hypothesis discharged. -/
theorem index_side_sound_core : Link.index_side_SoundP coreProgram :=
  Link.index_side_sound indexMleSound_core

end
end LeanVM.Guest.B1.KeccakGkr
