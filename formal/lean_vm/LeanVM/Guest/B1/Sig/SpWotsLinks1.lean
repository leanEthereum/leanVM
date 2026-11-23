/-
  LeanVM.Guest.B1.Sig.SpWotsLinks1

  `sp_wots`'s link, pieces `8` to `14`, and its owners: distinct, the parameters, the values the
  decoder reads.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsLinks
public import LeanVM.Guest.Pack.sp_wots.Core

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest.Ref

public section

theorem sp_piece_8 : spPiece 8 = true := by decide +kernel
theorem sp_piece_9 : spPiece 9 = true := by decide +kernel
theorem sp_piece_10 : spPiece 10 = true := by decide +kernel
theorem sp_piece_11 : spPiece 11 = true := by decide +kernel
theorem sp_piece_12 : spPiece 12 = true := by decide +kernel
theorem sp_piece_13 : spPiece 13 = true := by decide +kernel
theorem sp_piece_14 : spPiece 14 = true := by decide +kernel

/-- No two values own one name. -/
theorem sp_distinct : distinct spMap.ent 0 = true := by decide +kernel

/-- The parameters are the reference function's, owning their names. -/
theorem sp_params : spMap.uses 0 Fn.«sp_wots».core.params = some spK0 ∧
    Tm.eqbs (Fn.«sp_wots».core.params.map spMap.h) (spWotsRef.params.map .v) = true := by
  decide +kernel

/-- The decoder's values own their names. -/
theorem sp_owners : ownersAt spMap spPositions = true := by decide +kernel

end
end LeanVM.Guest.B1.Sig
