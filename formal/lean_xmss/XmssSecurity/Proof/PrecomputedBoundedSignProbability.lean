module

public import XmssSecurity.Proof.PrecomputedBoundedSignCache
public import XmssSecurity.Proof.EncodingTargetMap
public import XmssSecurity.Proof.SigningRandomnessUniformity
public import Mathlib.Data.Set.Card.Arithmetic
public import XmssSecurity.Proof.StatementLemmas

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

noncomputable local instance precomputedRandomnessSampleable : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

noncomputable def Concrete.precomputedSignBoundedAttemptsContinuation
    (attempts trial : Nat) (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (base : Randomness) (result : Option Signature × QueryCache HashSpec) :
    ProbComp (Option Signature × QueryCache HashSpec) :=
  match result.1 with
  | some signature => pure (some signature, result.2)
  | none => (simulateQ romImpl
      (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base attempts trial)).run
        result.2

attribute [irreducible] Concrete.precomputedSignBoundedAttemptsContinuation

theorem Concrete.precomputedSignBoundedAttempts_run_succ_eq
    (attempts trial : Nat) (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (base : Randomness) (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base (attempts + 1)
        trial)).run cache =
      ((simulateQ randomOracle
          (Concrete.precomputedSignAttempt secretKey leafIndex message
            (base + BitVec.ofNat randomnessBits trial) :
            OracleComp HashSpec (Option Signature))).run cache >>=
          Concrete.precomputedSignBoundedAttemptsContinuation attempts (trial + 1) secretKey
            leafIndex message base) := by
  rw [Concrete.precomputedSignBoundedAttempts, simulateQ_bind, StateT.run_bind]
  have hroute :
      simulateQ romImpl
          (liftM (Concrete.precomputedSignAttempt secretKey leafIndex message
            (base + BitVec.ofNat randomnessBits trial) :
            OracleComp HashSpec (Option Signature))) =
        simulateQ randomOracle
          (Concrete.precomputedSignAttempt secretKey leafIndex message
            (base + BitVec.ofNat randomnessBits trial) :
            OracleComp HashSpec (Option Signature)) := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
        (liftM (Concrete.precomputedSignAttempt secretKey leafIndex message
          (base + BitVec.ofNat randomnessBits trial) :
          OracleComp HashSpec (Option Signature))) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.precomputedSignAttempt secretKey leafIndex message
        (base + BitVec.ofNat randomnessBits trial) :
        OracleComp HashSpec (Option Signature))
  rw [hroute]
  apply bind_congr
  intro result
  rcases result with ⟨result, resultCache⟩
  cases result <;> simp [Concrete.precomputedSignBoundedAttemptsContinuation]

end XmssSecurity
