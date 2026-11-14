/-
  LeanVM.Guest.B1.VerifySub.Interface

  B1 of `verify_sub`, the child verifier: its meaning, the deferring verifier accepting a proof
  of the child's statement, and the statement of its soundness.
-/

module

public import LeanVM.Guest.B1.Tables.Interface
public import LeanVM.Guest.B1.Placement.Interface
public import LeanVM.Guest.B1.KeccakGkr.Interface
public import LeanVM.Guest.B1.Ring.Interface
public import LeanVM.Guest.B1.Bits.Meaning
public import Statement.LeanVmGuest
public import LeanXmss.Scheme
public import Statement.LeanSphincs
public import Statement.Fast.Schemes
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords
public import LeanVM.Facts.Verifier

/-!
# `verify_sub` (TRIAGE G #71): the interface

`verify_sub(pi_0, pi_1, seed_0, seed_1, g_squares, defer_out)` (G:3505-3704) runs
`verifyDeferredWith` (V:2328) on one child's proof: the seed `keccakF (seedInput iv pi)` by
`keccak_cells(…, final=0)`, the announced sizes (`readAnnouncedSizes`), the stack's root
(`commitStack`), the bus challenges and GKR (`verify_bus_gkr`), the bus leaves, the table
sumcheck and the public input (`verify_tables`), the Keccak reduction (`verify_keccak`), the
ring switch (`ring_switch_target`, `c_table`), the batching challenge, the placement
(`certify_placement`), the stacked opening (`open_stacked__L{j}`) and its terminal
(`check_opening_terminal`); it stores the claim on the bytecode the run leaves at `defer_out`
(`Node.DeferredClaim.cells`: the bus point's `BYTECODE_LOG = 19` row coordinates, the four bus challenges,
the value).

* `MeaningVerifySub bytecode`: the cells are a seed and a public input, and for some claim `c` on
  the bytecode of the guest's shape (`23` coordinates) and some proof `π`, the deferring verifier
  accepts `π` for the public input under the seed (`verifyDeferred`, V:2344), with
  `DeferredClaim.cells c` at `defer_out`;
* `VerifySubPre`: `g_squares` holds the exponent table and its window section (`ExpTables`,
  `ExpWinTab`);
* `verify_sub_Spec bytecode`: on a memory image of at most `2^32` words, under `VerifySubPre`, the
  relation gives the meaning, for the bytecode of `2^23` words (`bytecodeWords guest`).

Its proof (`verify_sub_holds`) takes the callees' statements as hypotheses: `verify_bus_gkr_Spec`,
`verify_tables_Spec`, `certify_placement_Spec`, `HypKappa` (B1-c), the WHIR opening's (B1-b), the
Bits/Fs/Eq meanings (B1-a), and this family's.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `BYTECODE_VARS`: the deferred claim's point has `23` coordinates. -/
abbrev bytecodeVars : ℕ := 23

/-- **`verify_sub`'s meaning** on `[pi_0, pi_1, seed_0, seed_1, g_squares, defer_out]`: the cells of a seed `seed` and a public input `pi`, and for some claim `c` on the
bytecode with `23` coordinates and some proof `π`, the deferring verifier accepts `π` for `pi`
under `seed` (`verifyDeferred`, V:2344), with `DeferredClaim.cells c` at `defer_out`; it returns
nothing. -/
def MeaningVerifySub (bytecode : List K) (rd : Reader) : List E → List E → Prop
  | [pi0, pi1, s0, s1, _, out], rets =>
      rets = [] ∧ ∃ (seed pi : Digest) (c : BytecodeClaim) (π : Proof),
        (s0, s1) = digestHalves seed ∧ (pi0, pi1) = digestHalves pi ∧
        verifyDeferred bytecode seed pi c π = true ∧ c.bytecodePoint.length = bytecodeVars ∧
        ReadsAt rd out (Node.DeferredClaim.cells c)
  | _, _ => False

/-- What `verify_sub`'s callers establish: the exponent table at `g_squares` with its window
section (`exponent_tables`, B1-a's `ExpTables` and `ExpWinTab`). -/
def VerifySubPre (rd : Reader) : List E → Prop
  | [_, _, _, _, sq, _] => ExpTables rd sq ∧ ExpWinTab rd sq
  | _ => False

/-- **`verify_sub` is sound** (G:3505-3704; TRIAGE #71): on a memory image of at most `2^32`
words holding the exponent tables, for a bytecode of `2^23` words. -/
def verify_sub_Spec (bytecode : List K) : Prop :=
  bytecode.length = 2 ^ bytecodeVars →
    ∀ {κ : ℕ}, κ ≤ 32 → ∀ (L : MemoryImage κ) (args rets : List E), VerifySubPre L.read args →
      coreProgram.Rel L.read "verify_sub" args rets → MeaningVerifySub bytecode L.read args rets

end
end LeanVM.Guest.B1.VerifySub
