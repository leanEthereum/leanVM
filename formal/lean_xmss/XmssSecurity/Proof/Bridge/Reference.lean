import XmssSecurity.Proof.Deterministic.RequestSampling
import XmssSecurity.Proof.Deterministic.ReferenceSource
import XmssSecurity.Proof.Deterministic.MemoGame
import XmssSecurity.Proof.Deterministic.CostState

/-!
# From the table signer to the model's signer

For a fixed key and cache: memoizing the adversary's repeated requests can only help it, and then
every request is fresh, so a uniform table of randomizer bases is a fresh uniform base per request,
the model's signer. The budget transfers the same way.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false

theorem worldHandler_randomOracle : worldHandler randomOracle = romImpl := rfl

theorem prob_table_le_memo (adversary : Adversary) (randomizers : RandomizerOutputs)
    (publicKey : PublicKey) (secretKey : XmssSecurity.SecretKey) (cache : QueryCache HashSpec) :
    Pr{let x ← (simulateQ romImpl (gameRest (tableScheme randomizers) adversary publicKey secretKey)).run' cache}[x = true] ≤
      Pr{let x ← ((simulateQ romImpl
        (gameRest (tableScheme randomizers) (memoAdversary adversary) publicKey secretKey)).run' cache)}[x = true] := by
  rw [← runSigning_sourceGame, ← runSigning_sourceGame]
  exact prob_sourceGame_le_memo _ _ _ _

theorem hashQueryBound_table_memo (adversary : Adversary) (randomizers : RandomizerOutputs)
    (publicKey : PublicKey) (secretKey : XmssSecurity.SecretKey) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (gameRest (tableScheme randomizers) adversary publicKey secretKey) cache q) :
    HashQueryBound (gameRest (tableScheme randomizers) (memoAdversary adversary) publicKey secretKey) cache q := by
  rw [← runSigning_sourceGame] at hbound ⊢
  exact hashQueryBound_sourceGame_memo _ _ _ cache q hbound

variable {State : Type}

/-- A uniform table of randomizer bases is the model's signer, once requests are memoized. -/
theorem evalDist_table_memo_run (hash : QueryImpl HashSpec (StateT State ProbComp)) (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : XmssSecurity.SecretKey) (state : State) :
    (do
      let randomizers ← sampleRandomizerOutputs
      (simulateQ (worldHandler hash)
        (gameRest (tableScheme randomizers) (memoAdversary adversary) publicKey secretKey)).run state) =ᵈ
      ((simulateQ (worldHandler hash)
        (gameRest Concrete.scheme (memoAdversary adversary) publicKey secretKey)).run state) := by
  have hleft (randomizers : RandomizerOutputs) := runSigning_sourceGame randomizers secretKey publicKey
    (memoAdversary adversary)
  simp_rw [← hleft]
  rw [← runWorldSigning_sourceGame, simulateQ_runWorldSigning]
  exact evalDist_tableRequests hash secretKey (sourceGame publicKey (memoAdversary adversary))
    (freshRequests_sourceGame_memo _ _) state

theorem evalDist_table_memo (adversary : Adversary) (publicKey : PublicKey)
    (secretKey : XmssSecurity.SecretKey) (cache : QueryCache HashSpec) :
    (do
      let randomizers ← sampleRandomizerOutputs
      (simulateQ romImpl
        (gameRest (tableScheme randomizers) (memoAdversary adversary) publicKey secretKey)).run' cache) =ᵈ
      ((simulateQ romImpl (gameRest Concrete.scheme (memoAdversary adversary) publicKey secretKey)).run' cache) := by
  have h := evalDist_table_memo_run randomOracle adversary publicKey secretKey cache
  rw [worldHandler_randomOracle] at h
  have heq := h.map Prod.fst
  simpa only [StateT.run'_eq, map_bind] using heq

theorem hashQueryBound_reference (adversary : Adversary) (publicKey : PublicKey)
    (secretKey : XmssSecurity.SecretKey) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : ∀ randomizers, HashQueryBound
      (gameRest (tableScheme randomizers) (memoAdversary adversary) publicKey secretKey) cache q) :
    HashQueryBound (gameRest Concrete.scheme (memoAdversary adversary) publicKey secretKey) cache q := by
  rw [hashQueryBound_iff_costState]
  intro result hresult
  rw [← OracleComp.support_eq_of_evalDistEq (evalDist_table_memo_run costHash adversary publicKey secretKey
    (cache, 0)), mem_support_bind_iff] at hresult
  obtain ⟨randomizers, _, hresult⟩ := hresult
  exact (hashQueryBound_iff_costState _ cache q).1 (hbound randomizers) result hresult

end XmssSecurity.Seeded
