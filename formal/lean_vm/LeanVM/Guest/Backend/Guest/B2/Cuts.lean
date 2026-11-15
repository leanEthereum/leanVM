/-
  LeanVM.Guest.Backend.Guest.B2.Cuts

  The placed locations of the functions whose piece is checked in parts: the locations of the
  last state of their cut walk.
-/

module

public import LeanVM.Guest.Backend.Sound.Cut
public import LeanVM.Guest.Backend.Guest.Piece.C11P0
public import LeanVM.Guest.Backend.Guest.Piece.C11P1
public import LeanVM.Guest.Backend.Guest.Piece.C20P0
public import LeanVM.Guest.Backend.Guest.Piece.C20P1

/-!
# Placed locations from the cuts

`verify_tables` (entry `11`) and `verify_sig_lean_sphincs` (entry `20`) are placed by the kernel in
parts (`Guest/Piece/C11*`, `C20*`): the walk's segments end in the states `cut11_end`,
`cut20_end`. With the segment equations and `placeFn_of_cut`, their placed locations are those
states' (`placedLocs_of_cut`), which the kernel evaluates without placing the function again.
-/

namespace LeanVM.Guest.Backend.GuestPiece

open LeanVM.Guest.Backend

@[expose] public section

/-- **The placed locations of a function walked in parts** are its last state's. -/
theorem placedLocs_of_cut {j k : ℕ} {st₁ st : St}
    (h₁ : placeHead (guestTraced.getD j default) k (ctxOf loopsG sigsG (guestTraced.getD j default))
      (initSt loopsG (tablesAt outsG j) (guestTraced.getD j default)) = .ok ((), st₁))
    (h₂ : placeTail (guestTraced.getD j default) k (ctxOf loopsG sigsG (guestTraced.getD j default)) st₁ =
      .ok ((), st))
    (hhead : cutHeadAt loopsG guestTraced outsG Data.functions.tail j st = true) :
    placedLocs j = st.locs := by
  simp only [cutHeadAt, Bool.and_eq_true] at hhead
  unfold placedLocs placedLocsAt
  rw [placeFn_of_cut hhead.1 (placeBody_of_cut h₁ h₂)]
  rfl

theorem placedLocs_11 : placedLocs 11 = cut11_end.locs :=
  placedLocs_of_cut (placeHead_add (placeHead_add cut11_seg0 cut11_seg1) cut11_seg2) cut11_tail cut11_head

theorem placedLocs_20 : placedLocs 20 = cut20_end.locs :=
  placedLocs_of_cut (placeHead_add cut20_seg0 cut20_seg1) cut20_tail cut20_head

end
end LeanVM.Guest.Backend.GuestPiece
