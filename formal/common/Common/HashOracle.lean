module

public import Statement.SufCma
public import Common.WithHash

@[expose] public section

/-!
# The model with a Keccak-256 oracle, a proof device

The statement's model has coins, `π` and `π⁻¹` and nothing else (`RandomPermutationOracles`): every party hashes
with Keccak-256 over `π` (`keccak256OverPermutation`). The proofs of `common`, `lean_xmss`, `lean_sphincs` and
`lean_da` reason with Keccak-256 as one more oracle, answered by the sponge over the same lazily
sampled permutation (`KSpecH`, `kImplH`, `runKH`), a hash of `n` bytes costing its `⌊n / 136⌋ + 1`
permutation calls (`permCallsH`), and with the SUF-CMA game over it (`SufCma.rpmGameH`,
`RpmSecureH`). `Common.PiOnly` proves that the statement's games are these games with each hash
call expanded into its permutation calls, with one distribution and one cost.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace Common

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- The oracles of the model with a hash oracle: coins, Keccak-256 (its digest's 32 bytes), `π`
and `π⁻¹`. -/
abbrev KSpecH := unifSpec + ((List UInt8 →ₒ DigestBytes) + permutationOracleSpec KeccakState)

/-- Calls of the permutation: a hash of `n` bytes costs `⌊n / 136⌋ + 1` (one per block of the
padded message), a call of `π` or `π⁻¹` one. -/
def permCallsH : KSpecH.Domain → ℕ
  | .inl _ => 0
  | .inr (.inl m) => m.length / 136 + 1
  | .inr (.inr _) => 1

/-- The answers: coins forwarded, Keccak-256 over the lazily sampled permutation, `π` and `π⁻¹`
the lazily sampled permutation. -/
noncomputable def kImplH : QueryImpl KSpecH (StateT (PermutationEdges KeccakState) ProbComp)
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.inl m) => Digest.toBytes <$> keccak256With (fun x ↦ lazyRandomPermutation (.forward x)) m
  | .inr (.inr q) => lazyRandomPermutation q

/-- A game with the hash oracle, run against the lazily sampled random permutation from no
edge. -/
noncomputable def runKH {α : Type} (G : OracleComp KSpecH α) : ProbComp α :=
  (simulateQ kImplH G).run' []

namespace SufCma

variable {Seed PK SK Req Resp F : Type}

/-- The hash as the Keccak-256 oracle (`digestBytesEquivBitVec`). -/
def hashKH : QueryImpl SchemeHashSpec (OracleComp KSpecH) :=
  fun m ↦ digestBytesEquivBitVec <$> (liftM (KSpecH.query (.inr (.inl m))) : OracleComp KSpecH
      DigestBytes)

/-- The signing oracle with the hash oracle. -/
def signingOracleKH (S : SchemeWithHash Seed PK SK Req Resp F) (sk : SK) :
    QueryImpl (Req →ₒ Resp) (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecH)) :=
  QueryImpl.withLogging fun r ↦ simulateQ hashKH (S.sign sk r)

/-- The RPM game with the hash oracle: an adversary that also queries Keccak-256. -/
noncomputable def rpmGameH (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpecH + (Req →ₒ Resp)) F) : OracleComp KSpecH Bool := do
  let seed ← liftM S.sample
  let (pk, sk) ← simulateQ hashKH (S.keygen seed)
  let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
    (simulateQ (QueryImpl.ofLift KSpecH (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecH)) +
      signingOracleKH S sk) (main pk)).run
  let verified ← simulateQ hashKH (S.verify pk forgery)
  return S.win log forgery && verified

/-- The RPM experiment with the hash oracle. -/
noncomputable def rpmExperimentH (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpecH + (Req →ₒ Resp)) F) : ProbComp Bool :=
  runKH (rpmGameH S main)

/-- `bits` bits of SUF-CMA security against adversaries that also query Keccak-256. -/
def RpmSecureH (S : SchemeWithHash Seed PK SK Req Resp F) (bits : ℕ) : Prop :=
  ∀ Q, 1 ≤ Q → ∀ main : PK → OracleComp (KSpecH + (Req →ₒ Resp)) F,
    QueryCostAtMost (rpmGameH S main) permCallsH Q →
      Pr{let b ← rpmExperimentH S main}[b = true] ≤ ((Q : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ bits

end SufCma

end Common
