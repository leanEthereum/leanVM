/-
  LeanVM.Guest.B1.Tables.CoordPadding

  A table's padding row (`Table.padding`) with `keccakF` of the zero state evaluated
  (`keccakF_zero`), so that the padding tie (`Vt.FormsPad`) is a kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Tables.InterfaceP
public import LeanVM.Guest.Value.KeccakConst

/-!
# The padding row

A table's padding row is zero but for the `KECCAK` table's output lanes, `keccakF` of the zero
state. `paddingRow` is the row with that value written out; `padding_eq` (`keccakF_zero`). The
baked `COORD_PADDING` is tied to it in `Vt.FormsPad`, and `Vt.SpecPad` uses it for the padding sums.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `Table.padding` with `keccakF` of zeros evaluated. -/
def paddingRow (t : Table) : List E :=
  (List.range t.width).map fun i ↦
    if t.opcode = opKeccak ∧ keccakOut ≤ i ∧ i < keccakOut + 25 then
      eOfNat (Keccak.lane Keccak.keccakFZero (i - keccakOut)).toNat
    else 0

theorem padding_eq (t : Table) : t.padding = paddingRow t := by
  unfold Table.padding paddingRow
  rw [show (Vector.replicate 25 0 : KeccakState) = Keccak.zeroState from rfl, Keccak.keccakF_zero]

end
end LeanVM.Guest.B1.Tables
