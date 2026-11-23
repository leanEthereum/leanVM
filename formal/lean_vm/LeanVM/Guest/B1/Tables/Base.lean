/-
  LeanVM.Guest.B1.Tables.Base

  The vocabulary of the B1 lemmas of the bus, the tables, the selectors and the placement, on top
  of the shared `B1/Common` machinery.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.B1.Common.Atoms
public import LeanVM.Guest.B1.Common.Sponge
public import LeanVM.Guest.CoreLemmas
public import LeanVM.Guest.Value.Keccak
public import LeanVM.Guest.Value.Bits
public import LeanVM.Protocol.WithHash

/-!
# B1 of the bus and the tables: vocabulary

* `BytecodeAt ev words point value`: the check `ev` of the fixed polynomial accepts `value` at
  `point`, consuming nothing.
* `gSquaresList`: the words `g^(2^j)` that `exponent_tables` writes.

Memory runs (`ReadsAt`), runs of the Spec's programs (`runId`, `RunsTo`) and the templates'
machinery (`stmtsEqb`, `holds_slice`, `loop_sound`, …) are `B1/Common`'s.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The check `ev` of the fixed polynomial of `words` accepts `value` at `point`, consuming
nothing (`computedBytecodeValue` where the value is the polynomial's, `claimedBytecodeValue` where
the point and the value are the claim's). -/
def BytecodeAt (ev : List K → List E → E → VerifierProgram Unit) (words : List K) (point : List E)
    (value : E) : Prop :=
  ∀ s, runId (ev words point value) s = some ((), s)

/-- `g_squares` (`exponent_tables`): `g^(2^j)` at `g^j`, `j < SIZE_BITS = 34`. -/
def gSquaresList : List E := (List.range 34).map fun j ↦ gen ^ 2 ^ j

end
end LeanVM.Guest.B1.Tables
