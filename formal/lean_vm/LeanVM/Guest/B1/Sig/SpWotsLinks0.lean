/-
  LeanVM.Guest.B1.Sig.SpWotsLinks0

  `sp_wots`'s link, pieces `0` to `7`.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsLinks
-- Read by the pieces; it also keeps `lake-build.py --dev`'s kernel on this module (`CORE_READ`).
public import LeanVM.Guest.Pack.sp_wots.Core

namespace LeanVM.Guest.B1.Sig

public section

theorem sp_piece_0 : spPiece 0 = true := by decide +kernel
theorem sp_piece_1 : spPiece 1 = true := by decide +kernel
theorem sp_piece_2 : spPiece 2 = true := by decide +kernel
theorem sp_piece_3 : spPiece 3 = true := by decide +kernel
theorem sp_piece_4 : spPiece 4 = true := by decide +kernel
theorem sp_piece_5 : spPiece 5 = true := by decide +kernel
theorem sp_piece_6 : spPiece 6 = true := by decide +kernel
theorem sp_piece_7 : spPiece 7 = true := by decide +kernel

end
end LeanVM.Guest.B1.Sig
