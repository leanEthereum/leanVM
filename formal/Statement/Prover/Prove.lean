module

public import Statement.Prover.Run
public import Statement.Prover.Link
public import Statement.Prover.Ntt
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

/-- **The honest prover of the commitment's out-of-domain sample** (`readOod`; `ood_sample`,
`crates/pcs/src/ood.rs`): a grind, the point `z` of the stack's `μ` variables, then the
stack's multilinear at `z`; the point and the value. -/
def oodFast (μ : ℕ) (stack : Array K) : Script (List E × E) :=
  (Script.grindBits Whir.oodGrindingBits).bind fun _ ↦
  (Script.sampleN μ).bind fun z ↦
  let value := mleK stack z
  (Script.sendE value).bind fun _ ↦ .ret (z, value)

/-- **The honest script** of an execution's witness `W` at the rate `ρ` and the public input
`publicInput`: the moves of `verify_execution` (its `walk`, `crates/verifier/src/lib.rs`),
each phase's executable prover beside the verifier's phase (`Script.alongside`), which hands the
next phase its result. The public-input phase sends nothing; the ring switch sends nothing either,
and draws the opening's batching challenge; the opening's claims are the verifier's, in its
order: the ring-switched claim (the Keccak reduction's slices on `q_keccak`, then the link's on the
pointer columns), the memory term, the column claims with a placement (the link's, the public
input's, the Keccak reduction's on `q_keccak`) and the out-of-domain claim. -/
def honestScript (W : Witness) (ρ : ℕ) (publicInput : Digest) : Script Unit := do
  let layout := W.layout
  Script.sendList (W.announce ρ)
  Script.commitS (stackWordFast layout.stackLog ρ W.stack)
  let ood ← oodFast layout.stackLog W.stack
  let link ← Script.alongside (verifyLink computedSplit layout) (linkProve W)
  let publicClaims ← Script.alongside (bindPublicInput layout publicInput) Script.sampleE
  let (outputs, keccakPoint, keccakSlices) ← Script.alongside (keccakValidity layout link)
    (KeccakGkr.keccakPhaseProve (layout.tableLogHeights.getD opKeccak 0) W.cols link)
  let qkeccakPlacement := (layout.placements.getD qkeccak none).getD default
  let ring ← ringFast true
  let placed := fun (column : ℕ) ↦ (layout.placements.getD column none).getD default
  let columnClaims := (linkColumnClaims link ++ publicClaims ++ outputs).filterMap fun c ↦
    (layout.placements.getD c.column none).map fun p ↦ ClaimDesc.cells [(p, c.point, 1)]
  openingFast layout.stackLog ρ W.stack
    (.ring [keccakRingClaim qkeccakPlacement keccakPoint keccakSlices, link.ring] ring.f ring.g
        ring.rho ::
      .cells [(placed memory0, link.memoryPoint, link.memoryScales.1),
        (placed memory1, link.memoryPoint, link.memoryScales.2)] ::
      columnClaims ++ [.ood ood.1])
    ring.batching

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
