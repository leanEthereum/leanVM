import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeUniform
/-!
# Encoding acceptance probability

The target-sum decoder accepts a finite nonempty set of 128-bit digests. A fresh random-oracle
answer has a uniform 128-bit truncation, so acceptance has exactly the corresponding finite ratio.
-/

namespace SphincsSecurity

open OracleComp ENNReal
open scoped BigOperators

set_option maxRecDepth 100000

theorem evalDist_truncateHash_uniform :
    𝒟[truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒟[($ᵗ Digest : ProbComp Digest)] := by
  change 𝒟[(fun output : HashOutput => output.extractLsb' 0 digestBits) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)] = _
  exact evalDist_hashOutput_extract_uniform (width := digestBits) (by decide)

theorem probEvent_uniform_truncateHash_eq (target : Digest) :
    Pr[fun output : HashOutput => truncateHash output = target |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [show (fun output : HashOutput => truncateHash output = target) =
      (fun output => output = target) ∘ truncateHash from rfl]
  rw [← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) evalDist_truncateHash_uniform]
  rw [probEvent_eq_eq_probOutput, probOutput_uniformSample]

theorem probEvent_uniform_truncateHash_mem (targets : Finset Digest) :
    Pr[fun output : HashOutput => truncateHash output ∈ targets |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      (targets.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
  rw [show (fun output : HashOutput => truncateHash output ∈ targets) =
      (fun digest => digest ∈ targets) ∘ truncateHash from rfl]
  rw [← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) evalDist_truncateHash_uniform]
  rw [probEvent_uniformSample]
  rw [Finset.filter_univ_mem]

end SphincsSecurity
