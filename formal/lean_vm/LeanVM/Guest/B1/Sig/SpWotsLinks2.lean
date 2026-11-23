/-
  LeanVM.Guest.B1.Sig.SpWotsLinks2

  `sp_wots`'s link, pieces `15` to `21` and the last.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsLinks
-- Read by the pieces; it also keeps `lake-build.py --dev`'s kernel on this module (`CORE_READ`).
public import LeanVM.Guest.Pack.sp_wots.Core

namespace LeanVM.Guest.B1.Sig

public section

theorem sp_piece_15 : spPiece 15 = true := by decide +kernel
theorem sp_piece_16 : spPiece 16 = true := by decide +kernel
theorem sp_piece_17 : spPiece 17 = true := by decide +kernel
theorem sp_piece_18 : spPiece 18 = true := by decide +kernel
theorem sp_piece_19 : spPiece 19 = true := by decide +kernel
theorem sp_piece_20 : spPiece 20 = true := by decide +kernel
theorem sp_piece_21 : spPiece 21 = true := by decide +kernel

theorem sp_piece_last : spPieceLast = true := by decide +kernel

end
end LeanVM.Guest.B1.Sig
