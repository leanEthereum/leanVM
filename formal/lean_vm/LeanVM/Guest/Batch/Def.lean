/-
  LeanVM.Guest.Batch.Def

  The batching of a node's children as the guest program computes it, a `StateM Sponge`
  transcript (`Node.batch`): moved here from `Statement/LeanVmGuest.lean`, names kept, which states
  the batching once, as the verifier program `Batch.nodeBatchingProgram` (`Batch.batchRun_batchOf_iff` relates
  the two).
-/

module

public import Statement.LeanVmGuest

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A Fiat-Shamir chain: the verifier's duplex sponge over Keccak-f[1600] (`FiatShamirState`). -/
abbrev Chain : Type → Type := StateM Sponge

/-- Absorb a scalar (`observe`). -/
def observe (x : E) : Chain Unit :=
  modify fun sp ↦ Id.run (Compile.absorb (m := Id) keccakF1600 sp x dsObserve)

/-- Squeeze a challenge (`sample`). -/
def sample : Chain E := do
  let (c, sp) := Id.run (Compile.squeeze (m := Id) keccakF1600 (← get))
  set sp
  return c

/-- The rounds of a batching sumcheck from the running claim: each round absorbs `g(1)` and
`g(∞)`, squeezes the challenge, and folds the round polynomial (`batch_sumcheck`,
`lean_ethereum.py:1147-1164`; `absorb_round`, `aggregation/deferred.rs:222-238`). The challenges and the
final claim. -/
def batchRounds : E → List (E × E) → Chain (List E × E)
  | claim, [] => return ([], claim)
  | claim, (g1, gInf) :: rest => do
    observe g1
    observe gInf
    let r ← sample
    let (rs, final) ← batchRounds (Guest.Batch.sumcheckRoundPolynomial claim (g1, gInf) r) rest
    return (r :: rs, final)

/-- The batching transcript's initial state (`FiatShamirState::from_label`): Keccak-f of the
label's hash in lanes `0..4`, the other lanes zero. The guest program bakes its capacity
(`AGG_SEED_*`, `aggregation/placeholders.rs:823-826`). -/
def batchSeed : KeccakState := keccakF1600 (seedInput (keccak256 batchingLabel) (Vector.replicate 4 0))

/-- **The batching**: one transcript absorbs the children's count, then every child's public
input and claims, each group padded to a whole rate; it squeezes one challenge `λ`, whose powers
`λ^(2i)`, `λ^(2i+1)` are child `i`'s coefficients (`lambdaPowers`), and one sumcheck reduces every
child's two claims on the bytecode to one point. The claim deferred there, if the sumcheck
closes. -/
def batch (children : List ChildClaims) (h : BatchingHints) : Option DeferredClaim :=
  go.run' ⟨batchSeed, [], none⟩
where
  /-- The transcript. -/
  go : Chain (Option DeferredClaim) := do
    for x in padToRate [gpow children.length] do observe x
    for c in children do
      for x in padToRate c.words do observe x
    let lam ← sample
    let lambdas := Guest.Batch.lambdaPowers lam children.length
    let (r, final) ← batchRounds (Guest.Batch.batchedClaim children lambdas) h.sumcheckMessages
    if final = h.finalBytecodeValue * Guest.Batch.batchedBytecodeWeight children lambdas r then
      return some ⟨r, h.finalBytecodeValue⟩
    else return none

end
end LeanVM.Node
