/-
  LeanVM.Guest.B1.Da.WitnessAtTB

  `da_verify` placed on a LeanDA witness, by a tree of its honest shape, within its words bound
  (`dvB`) at the witness's row count and padded log, for the budget.

  The witness and `Da.MatrixWitness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Da.DvAt
public import LeanVM.Guest.B1.Da.Witness
public import LeanVM.Guest.Data.NameStrings

/-!
# `da_verify` on a witness, within its bound

`da_verify_completeAtTB`: for a witness opening `(root, z)`, `da_verify` is complete,
placed on the count table at `g^tb` (`L = wLog w`), by a tree of `dvNH r L` within
`dvB fs SB SK r L` (`r` its rows), returning the root's cells and `z`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDTB Returns)

@[expose] public section

variable (fs : String → ℕ) {SB SK : String → ℕ} (cert : String → V → ℕ)

/-- **`da_verify` is complete, placed, on a witness, by a tree of its honest shape, within
`dvB`.** -/
theorem da_verify_completeAtTB (hrf : Lift.RunsFit fs cert) {w : LeanVM.Da.MatrixWitness}
    {root : Digest} {z : E} (hw : w.Opens root z) (hS : DvStaticB fs SB SK) {Lin : B1.Main.Layout} {tb : ℕ}
    (hbt : ∀ rd, B1.Main.MemL rd Lin → CountWords rd (gen ^ tb))
    (hbr : ∀ v ≤ LeanDa.maxRows, B1.Main.RegionL Lin (tb + v)) :
    CompleteAtDTB fs cert 16 "da_verify" Lin [gen ^ tb]
      (Returns (digestCells root ++ [z]))
      (dvNH w.rows.length (wLog w)) (dvB fs SB SK w.rows.length (wLog w)) := by
  have hr1 := hw.1
  have hr := hw.2.1
  have hL : 2 ^ wLog w = LeanDa.maxRows := rfl
  rw [opens_eq hw]
  exact dv_completeAtB fs cert hrf hS hr1 hr hL (wSyms_len hw) (wDot hw) hbt hbr

end
end LeanVM.Guest.B1.Da
