/-
  LeanVM.Guest.B1.Tables.Base

  The vocabulary of the B1 lemmas of the bus, the tables, the selectors and the placement: runs of
  the specification's programs on the duplex sponge that the guest carries between functions as
  its five capacity cells.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.CoreLemmas
public import LeanVM.Guest.Value.Keccak
public import LeanVM.Guest.Value.Bits
public import LeanVM.Protocol.WithHash

/-!
# B1 of the bus and the tables: vocabulary

These are local to `B1/{Gkr, Tables, Selectors, Placement}`; memory runs are `B1/Common`'s
`ReadsAt`.

* Runs of the Spec's programs on the carried sponge are `RunsTo` (`B1/Common/Sponge`),
  copied as `RunsTo` in `B1/Gkr/Fs`: from any sponge the guest carries as five capacity cells
  and waiting scalars, a program reads exactly the stream words given and returns its value,
  leaving a sponge the guest carries as the cells after.
* `BytecodeAt ev words point value`: the check `ev` of the fixed polynomial accepts `value` at
  `point`, consuming nothing.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `Compile.run` with the deployed hash and permutation. -/
abbrev tbRun {α : Type} (p : VerifierProgram α) (s : VerifierProgramState) : Option (α ×
    VerifierProgramState) :=
  Compile.runWithHash (m := Id) keccak256 keccakF1600 p s

/-- The check `ev` of the fixed polynomial of `words` accepts `value` at `point`, consuming
nothing (`computedBytecodeValue` where the value is the polynomial's, `claimedBytecodeValue` where
the point and the value are the claim's). -/
def BytecodeAt (ev : List K → List E → E → VerifierProgram Unit) (words : List K) (point : List E)
    (value : E) : Prop :=
  ∀ s, tbRun (ev words point value) s = some ((), s)

/-- `g_squares` (`exponent_tables`): `g^(2^j)` at `g^j`, `j < SIZE_BITS = 34`. -/
def gSquaresList : List E := (List.range 34).map fun j ↦ gen ^ 2 ^ j

end
end LeanVM.Guest.B1.Tables
