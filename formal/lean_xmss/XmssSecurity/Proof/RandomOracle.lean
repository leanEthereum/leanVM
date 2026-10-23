import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.EvalDistEq
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.QueryTracking.Unpredictability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem hashOutputBits_eq : hashOutputBits = digestBits + digestBits := by
  decide

/-- A 256-bit oracle output viewed as two digest halves; `truncateHash` keeps the low half. -/
def splitHashOutput (output : HashOutput) : BitVec (digestBits + digestBits) :=
  output.cast hashOutputBits_eq

end XmssSecurity

namespace XmssSecurity.Rom

noncomputable local instance : UniformAnswerMeasure HashSpec :=
  UniformAnswerMeasure.ofFiniteNonempty _

theorem card_hashOutput : Fintype.card HashOutput = 2 ^ hashOutputBits := by
  simp

private def joinDigest (high low : Digest) : HashOutput :=
  (high ++ low).cast hashOutputBits_eq.symm

private def highDigest (output : HashOutput) : Digest :=
  (splitHashOutput output).extractLsb' digestBits digestBits

private def digestFiberEquiv (target : Digest) :
    Digest ≃ {output : HashOutput // truncateHash output = target} where
  toFun high := ⟨joinDigest high target, by
    change BitVec.extractLsb' 0 digestBits (high ++ target) = target
    exact BitVec.extractLsb'_append_eq_right⟩
  invFun output := highDigest output.val
  left_inv high := by
    change BitVec.extractLsb' digestBits digestBits (high ++ target) = high
    exact BitVec.extractLsb'_append_eq_left
  right_inv output := by
    apply Subtype.ext
    calc
      joinDigest (highDigest output.val) target =
          joinDigest (highDigest output.val) (truncateHash output.val) := by
        rw [output.property]
      _ = (splitHashOutput output.val).cast hashOutputBits_eq.symm := by
        exact congrArg (BitVec.cast hashOutputBits_eq.symm)
          (BitVec.extractLsb'_append_extractLsb' (x := splitHashOutput output.val))
      _ = output.val := by simp [splitHashOutput]

/-- A 256-bit random-oracle answer is equivalently an independent high half and the 128-bit digest used by XMSS. -/
def hashOutputEquivDigestPair : HashOutput ≃ Digest × Digest where
  toFun output := (highDigest output, truncateHash output)
  invFun halves := joinDigest halves.1 halves.2
  left_inv output := by
    calc
      joinDigest (highDigest output) (truncateHash output) =
          (splitHashOutput output).cast hashOutputBits_eq.symm := by
        exact congrArg (BitVec.cast hashOutputBits_eq.symm)
          (BitVec.extractLsb'_append_extractLsb' (x := splitHashOutput output))
      _ = output := by simp [splitHashOutput]
  right_inv halves := by
    apply Prod.ext
    · change BitVec.extractLsb' digestBits digestBits (halves.1 ++ halves.2) = halves.1
      exact BitVec.extractLsb'_append_eq_left
    · change BitVec.extractLsb' 0 digestBits (halves.1 ++ halves.2) = halves.2
      exact BitVec.extractLsb'_append_eq_right

noncomputable def independentDigestHalves : ProbComp (Digest × Digest) := do
  let high ← $ᵗ Digest
  let low ← $ᵗ Digest
  return (high, low)

/-- Splitting a uniform 256-bit answer gives two independent uniform 128-bit halves. -/
theorem evalDist_split_uniformHashOutput_eq_independent :
    (hashOutputEquivDigestPair <$> ($ᵗ HashOutput)) =ᵈ independentDigestHalves := by
  calc
    (hashOutputEquivDigestPair <$> ($ᵗ HashOutput)) =ᵈ ($ᵗ (Digest × Digest)) :=
      SampleableType.map_uniformSample_evalDistEq_of_bijective
        hashOutputEquivDigestPair.bijective
    _ =ᵈ independentDigestHalves := by
      unfold independentDigestHalves
      rw [SampleableType.uniformSample_prod_eq_bind]

/-- Truncating a uniform 256-bit answer gives a uniform XMSS digest. -/
theorem evalDist_truncate_uniformHashOutput :
    (truncateHash <$> ($ᵗ HashOutput)) =ᵈ ($ᵗ Digest) := by
  calc
    (truncateHash <$> ($ᵗ HashOutput)) =ᵈ
        (Prod.snd <$> (hashOutputEquivDigestPair <$> ($ᵗ HashOutput))) := by
      simp [Functor.map_map, hashOutputEquivDigestPair]
    _ =ᵈ (Prod.snd <$> independentDigestHalves) :=
      evalDist_split_uniformHashOutput_eq_independent.map _
    _ =ᵈ ($ᵗ Digest) := by
      unfold independentDigestHalves
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply, bind_pure]
      exact OracleComp.EvalDistEq.bind_const _ _

/-- Sample a 256-bit oracle answer whose low XMSS digest is fixed while its high half remains uniform. -/
noncomputable def sampleHashOutputWithDigest (target : Digest) :
    ProbComp HashOutput :=
  (fun high => hashOutputEquivDigestPair.symm (high, target)) <$>
    ($ᵗ Digest)

@[simp]
noncomputable def sampledHashOutputWithDigest :
    ProbComp (Digest × HashOutput) := do
  let low ← $ᵗ Digest
  let output ← sampleHashOutputWithDigest low
  return (low, output)

/-- A programmed answer together with its chosen low digest has the same joint distribution as a uniform answer together with its truncation. -/
theorem evalDist_sampledHashOutputWithDigest_eq_uniform :
    sampledHashOutputWithDigest =ᵈ ((fun output : HashOutput => (truncateHash output, output)) <$>
        ($ᵗ HashOutput)) := by
  calc
    (sampledHashOutputWithDigest) =ᵈ
        ($ᵗ Digest >>= fun high =>
          $ᵗ Digest >>= fun low =>
            pure (low, hashOutputEquivDigestPair.symm (high, low))) := by
      unfold sampledHashOutputWithDigest sampleHashOutputWithDigest
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
    _ =ᵈ ((fun halves : Digest × Digest =>
          (halves.2, hashOutputEquivDigestPair.symm halves)) <$>
        independentDigestHalves) := by
      simp [independentDigestHalves, map_eq_bind_pure_comp, bind_assoc]
    _ =ᵈ ((fun halves : Digest × Digest =>
          (halves.2, hashOutputEquivDigestPair.symm halves)) <$>
        (hashOutputEquivDigestPair <$> ($ᵗ HashOutput))) :=
      evalDist_split_uniformHashOutput_eq_independent.symm.map _
    _ =ᵈ ((fun output : HashOutput => (truncateHash output, output)) <$>
        ($ᵗ HashOutput)) := by
      have hfunction :
          (fun halves : Digest × Digest =>
            (halves.2, hashOutputEquivDigestPair.symm halves)) ∘
              hashOutputEquivDigestPair =
            (fun output : HashOutput => (truncateHash output, output)) := by
        funext output
        apply Prod.ext
        · rfl
        · exact hashOutputEquivDigestPair.symm_apply_apply output
      rw [Functor.map_map]
      exact .of_eq (congrArg (· <$> ($ᵗ HashOutput)) hfunction)


/-- A programmed low digest and its independent high half may be replaced by one ordinary random-oracle output inside any continuation. -/
theorem evalDist_sampledHashOutputWithDigest_bind_eq_uniform_bind
    (continuation : Digest × HashOutput → ProbComp α) :
    (sampledHashOutputWithDigest >>= continuation) =ᵈ
      ($ᵗ HashOutput >>= fun output =>
        continuation (truncateHash output, output)) := by
  calc
    (sampledHashOutputWithDigest >>= continuation) =ᵈ
        (((fun output : HashOutput => (truncateHash output, output)) <$>
          ($ᵗ HashOutput)) >>= continuation) :=
      evalDist_sampledHashOutputWithDigest_eq_uniform.bind_left _

    _ =ᵈ ($ᵗ HashOutput >>= fun output =>
          continuation (truncateHash output, output)) := by
      simp [map_eq_bind_pure_comp, bind_assoc]

def matchingOutputs (target : Digest) : Finset HashOutput :=
  Finset.univ.filter (truncateHash · = target)

theorem card_matchingOutputs (target : Digest) :
    (matchingOutputs target).card = 2 ^ digestBits := by
  rw [show matchingOutputs target = Finset.univ.filter (truncateHash · = target) from rfl]
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (digestFiberEquiv target)).symm.trans (by simp)

end XmssSecurity.Rom
