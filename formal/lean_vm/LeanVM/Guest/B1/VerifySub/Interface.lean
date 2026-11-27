/-
  LeanVM.Guest.B1.VerifySub.Interface

  B1 of `verify_sub`, the child verifier: what it runs, and what its callers establish.
-/

module

import LeanVM.Guest.B1.Tables.Interface
import LeanVM.Guest.B1.Placement.Interface
import LeanVM.Guest.B1.KeccakGkr.Interface
import LeanVM.Guest.B1.Ring.Interface
import LeanVM.Guest.B1.Bits.Meaning
import Statement.LeanVmGuest
public import Statement.LeanSphincs
public import Statement.LeanXmss
import LeanDa.Scheme
public import Statement.Fast.Keccak
public import FastFields.QuadExt
public import FastFields.FieldWords
public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.CoreData
public import Statement.LeanVmGuestBatching
import LeanVM.Facts.Verifier

/-!
# `verify_sub` (TRIAGE G #71): the interface

`verify_sub(pi_0, pi_1, seed_0, seed_1, g_squares, defer_out)` runs
`verifyDeferredWith` on one child's proof: the seed `keccakF (seedInput iv pi)` by
`keccak_cells(…, final=0)`, the announced sizes (`readAnnouncedSizes`), the stack's root
(`commitStack`), the bus challenges and GKR (`verify_bus_gkr`), the bus leaves, the table
sumcheck and the public input (`verify_tables`), the Keccak reduction (`verify_keccak`), the
ring switch (`ring_switch_target`, `c_table`), the batching challenge, the placement
(`certify_placement`), the stacked opening (`open_stacked__L{j}`) and its terminal
(`check_opening_terminal`); it stores the claim on the bytecode the run leaves at `defer_out`
(`Node.DeferredBytecodeClaim.cells`: the bus point's `BYTECODE_LOG = 19` row coordinates, the four bus challenges,
the value).

* `bytecodeVars`: the deferred claim's point has `23` coordinates;
* `VerifySubPre`: `g_squares` holds the exponent table and its window section (`ExpTables`,
  `ExpWinTab`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `BYTECODE_VARS`: the deferred claim's point has `23` coordinates. -/
abbrev bytecodeVars : ℕ := 23

/-- What `verify_sub`'s callers establish: the exponent table at `g_squares` with its window
section (`exponent_tables`, B1-a's `ExpTables` and `ExpWinTab`). -/
def VerifySubPre (rd : Reader) : List E → Prop
  | [_, _, _, _, sq, _] => ExpTables rd sq ∧ ExpWinTab rd sq
  | _ => False

end
end LeanVM.Guest.B1.VerifySub
