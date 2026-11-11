module

public import Statement.Prover.Run
public import Statement.Prover.Columns
public import Statement.Prover.Ntt
public import Statement.Prover.Bus
public import Statement.Prover.Table
public import Statement.Prover.Keccak
public import Statement.Prover.Whir

/-!
# The honest prover

`LeanVM.Prover.prove F prog input t ρ fuel`: leanVM's honest prover over the permutation `F` in any
monad, Keccak-256 the sponge over `F`. With Keccak-f[1600] in `Id` it is the executable
(`lake exe leanvm-prove`); with the model's permutation (`Common.queryPermutation`) it is the
prover the completeness statements name (`LeanVm.lean`, `LeanVmGuestCompleteness.lean`).

It computes the witness from the trace (`witness?`: one run of the program) and runs the honest
script, one executable prover per phase of `verify_execution`, against the verifier's own program
(`runScript`). Its only search is the proof-of-work nonce search, bounded by `fuel`; nothing
branches on a permutation answer except through the challenges the verifier's program samples.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

/-- **The honest script** of an execution's witness `W` at the rate `ρ` and the public input
`publicInput`: the eight moves of `verify_execution` (its `walk`,
`crates/verifier/src/lib.rs:217-331`), each phase's executable prover beside the verifier's phase
(`Script.alongside`), which hands the next phase its result. The public-input phase sends nothing;
the output lanes' claims, on no committed column, do not reach the stack (`ColumnClaim.onStack`). -/
def honestScript (W : Witness) (ρ : ℕ) (publicInput : Digest) : Script Unit :=
  let layout := W.layout
  (Script.sendList (W.announce ρ)).bind fun _ ↦
  (Script.commitS (stackWordFast layout.stackLog ρ W.stack)).bind fun _ ↦
  (Script.alongside (verifyBusBalance computedBytecodeValue layout) (busFast layout W.cols)).bind
    fun bus ↦
  (Script.alongside (tablePhase layout bus) (tableFast W.cols layout.tableLogHeights bus)).bind
    fun evaluations ↦
  (Script.alongside (publicInputPhase layout publicInput) Script.sampleE).bind fun publicClaims ↦
  (Script.alongside (keccakPhase layout evaluations) (KeccakGkr.keccakPhaseProve
    (layout.tableLogHeights.getD opKeccak 0) W.cols evaluations)).bind fun keccak ↦
  (ringFast keccak.2.1 keccak.2.2).bind fun r ↦
  let claims := (bus.claims ++ tableColumnClaims evaluations ++ publicClaims).filter
    (fun c ↦ c.column ∉ keccakOutputColumns) ++ keccak.1
  openingFast layout.stackLog ρ W.stack (r.claim layout :: claims.map (ClaimDesc.column layout))

/-- **leanVM's honest prover.** The proof of the execution `t` of `prog` on `input` at the rate
`2^-ρ`, trying `fuel` nonces per proof of work; `none` for a trace that is no valid execution
within the cap, an invalid rate, or a proof-of-work search that finds no nonce. -/
def prove {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (prog : LeanIsaProgram)
    (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ) : m (Option Proof) :=
  match witness? prog input t with
  | none => pure none
  | some W =>
    if 1 ≤ ρ ∧ ρ ≤ 4 then do
      let seed ← spongeSeedWith F (bytecodeWords prog) (publicInputDigest input)
      runScript F (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
        (honestScript W ρ (publicInputDigest input)) seed fuel
    else pure none

end LeanVM.Prover

end
