/-
  LeanVM.Guest.B1.VerifySub.TermGlue

  What `verify_sub` hands `check_opening_terminal`, in the terminal's forms: the exponent table's
  nibble shares (`GTabsAt`), `verify_tables`' context (`TCtx`) as the terminal's `TermCtx`, and the
  layout's placements at the guest's bytecode log size.
-/

module

public import LeanVM.Guest.B1.Terminal.InterfaceP
public import LeanVM.Guest.B1.Bits.Tables
public import LeanVM.Guest.B1.VerifySub.Sizes

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The exponent table's nibble shares, as `check_opening_terminal` reads them at `g_squares·g^34`. -/
theorem gTabs_of_exp {rd : Reader} {sq : E} (h : ExpTables rd sq) :
    Tables.GTabsAt rd (sq * gen ^ 34) := by
  intro j hj u hu
  rw [loadHolds_mul_gen_pow]
  have := h.2.1 j (by simp only [Tables.selNibbles] at hj; simp only [selTabNibbles]; omega) u hu
  simpa only [sizeBits, Nat.add_assoc] using this

/-- `verify_tables`' context is the terminal's (`TermCtx` is `Tables.TCtx`). -/
theorem termCtx_of_tctx {rd : Reader} {layout : Layout} {bus : BusResult}
    {claims : List ColumnClaim} {zeta chi rm gmu gzcn : E}
    (h : Tables.TCtx rd layout bus claims [zeta, chi, rm, gmu, gzcn]) :
    TermCtx rd layout bus claims [zeta, chi, rm, gmu, gzcn] := h

/-- The layout's placements, at the guest's bytecode log size `19`. -/
theorem layoutOf_placements {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) (logMem : ℕ)
    (rowsN : List ℕ) : (Tables.layoutOf bytecode logMem rowsN).placements =
      (placementsOf (columnKappas logMem 19 (Tables.tableHeightsOf rowsN))).1 := by
  unfold Tables.layoutOf
  simp only []
  rw [log2_bytecode hbl]

/-- The layout's stack log, at the guest's bytecode log size `19`. -/
theorem layoutOf_stackLog {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) (logMem : ℕ)
    (rowsN : List ℕ) : (Tables.layoutOf bytecode logMem rowsN).stackLog =
      (placementsOf (columnKappas logMem 19 (Tables.tableHeightsOf rowsN))).2 := by
  unfold Tables.layoutOf
  simp only []
  rw [log2_bytecode hbl]

end
end LeanVM.Guest.B1.VerifySub
