import XmssSecurity.Proof.Deterministic.TableSigner
import XmssSecurity.Proof.Deterministic.World
import XmssSecurity.Proof.StatementLemmas
import XmssSecurity.Proof.RandomOracle
import XmssSecurity.Proof.UniformFiniteTable

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

attribute [local irreducible] Concrete.precomputedSignAttempt

variable {State : Type}

/-- Lifted to the oracle world, the table signer's trials are the reference signer's. -/
theorem liftM_tableSignFrom (base : Randomness) (secretKey : XmssSecurity.SecretKey)
    (leafIndex : LeafIndex) (message : Message) (attempts trial : Nat) :
    (liftM (tableSignFrom base secretKey leafIndex message attempts trial :
        OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature)) =
      Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base attempts trial := by
  induction attempts generalizing trial with
  | zero => simp [tableSignFrom, Concrete.precomputedSignBoundedAttempts]
  | succ attempts ih =>
      simp only [tableSignFrom, Concrete.precomputedSignBoundedAttempts, liftM_bind]
      apply bind_congr
      intro result
      cases result with
      | none => exact ih (trial + 1)
      | some signature => simp

def randomizerHalves : HashOutput ≃ (BitVec 128 × Randomness) where
  toFun output := (output.extractLsb' randomnessBits 128, output.extractLsb' 0 randomnessBits)
  invFun pair := pair.1 ++ pair.2
  left_inv output := BitVec.extractLsb'_append_extractLsb' (w := 128) (len := 128) (x := output)
  right_inv pair := by
    apply Prod.ext
    · exact BitVec.extractLsb'_append_eq_left
    · exact BitVec.extractLsb'_append_eq_right

noncomputable local instance : SampleableType Randomness := SampleableType.ofFintype Randomness

theorem evalDist_uniform_discard {A B : Type} [SampleableType A] (next : ProbComp B) :
    𝒟[do let _ ← $ᵗ A; next] = 𝒟[next] :=
  OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (probFailure_uniformSample _) _

/-- The first 16 bytes of a uniform hash output are a uniform randomizer base. -/
theorem evalDist_randomizer :
    𝒟[(fun output : HashOutput => output.extractLsb' 0 randomnessBits) <$> ($ᵗ HashOutput)] =
      𝒟[Concrete.signingRandomness] := by
  have h := evalDist_map_bijective_uniform_cross
    (α := HashOutput) (β := BitVec 128 × Randomness) randomizerHalves randomizerHalves.bijective
  have hpair := evalDist_independent_uniform_pair (α := BitVec 128) (β := Randomness)
  calc
    _ = 𝒟[Prod.snd <$> (randomizerHalves <$> ($ᵗ HashOutput))] := by
      simp only [Functor.map_map]; rfl
    _ = 𝒟[Prod.snd <$> ($ᵗ (BitVec 128 × Randomness))] := by rw [evalDist_map, h, ← evalDist_map]
    _ = 𝒟[Prod.snd <$> (do
        let high ← $ᵗ (BitVec 128)
        let low ← $ᵗ Randomness
        pure (high, low))] := by rw [evalDist_map, ← hpair, ← evalDist_map]
    _ = _ := by
      simp only [map_bind, bind_pure_comp, Functor.map_map, id_map', Concrete.signingRandomness_eq]
      exact evalDist_uniform_discard (A := BitVec 128) ($ᵗ Randomness)

/-- A uniform table entry as the randomizer base gives the reference signer. -/
theorem evalDist_tableSign (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : XmssSecurity.SecretKey) (leafIndex : LeafIndex) (message : Message) (state : State) :
    𝒟[do
      let output ← ($ᵗ HashOutput : ProbComp HashOutput)
      (simulateQ (worldHandler hash) (liftM (tableSign (fun _ => output) secretKey leafIndex message :
        OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld _)).run state] =
      𝒟[(simulateQ (worldHandler hash) (Concrete.precomputedCappedSign secretKey leafIndex message)).run state] := by
  unfold tableSign Concrete.precomputedCappedSign
  simp only [liftM_bind, liftM_pure, liftM_tableSignFrom]
  rw [worldHandler_sampling_bind]
  conv_rhs => rw [evalDist_bind, ← evalDist_randomizer, ← evalDist_bind, bind_map_left]
  rw [evalDist_bind]

end XmssSecurity.Seeded
