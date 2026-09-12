import SphincsSecurity.Proof.Ots.OtsPrefixFrontier
import SphincsSecurity.Proof.Base.UniformTableSplit
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem replaceChain_self (segment : OtsPrefix) (secrets : OtsFrontierValues) (value : Digest) :
    segment.replaceChain secrets value segment.lay segment.tree segment.leaf segment.chainIdx = value := by
  simp only [replaceChain, SameChain, and_self, ↓reduceIte]

theorem replaceChain_replaceChain (segment : OtsPrefix) (secrets : OtsFrontierValues) (first second : Digest) :
    segment.replaceChain (segment.replaceChain secrets first) second = segment.replaceChain secrets second := by
  funext lay tree leaf chainIdx
  by_cases h : segment.SameChain lay tree leaf chainIdx <;> simp only [replaceChain, h, ↓reduceIte]

theorem replaceChain_current (segment : OtsPrefix) (secrets : OtsFrontierValues) :
    segment.replaceChain secrets (secrets segment.lay segment.tree segment.leaf segment.chainIdx) = secrets := by
  funext lay tree leaf chainIdx
  by_cases h : segment.SameChain lay tree leaf chainIdx
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact segment.replaceChain_self secrets _
  · simp only [replaceChain, h, ↓reduceIte]

abbrev ErasedSecrets (segment : OtsPrefix) :=
  {secrets : OtsFrontierValues // secrets segment.lay segment.tree segment.leaf segment.chainIdx = 0}

instance (segment : OtsPrefix) : Nonempty segment.ErasedSecrets := ⟨⟨fun _ _ _ _ => 0, rfl⟩⟩

def secretSplit (segment : OtsPrefix) : OtsFrontierValues ≃ segment.ErasedSecrets × Digest where
  toFun secrets := (⟨segment.replaceChain secrets 0, segment.replaceChain_self secrets 0⟩,
    secrets segment.lay segment.tree segment.leaf segment.chainIdx)
  invFun pair := segment.replaceChain pair.1.val pair.2
  left_inv secrets := (segment.replaceChain_replaceChain secrets 0 _).trans (segment.replaceChain_current secrets)
  right_inv pair := by
    apply Prod.ext
    · apply Subtype.ext
      exact (segment.replaceChain_replaceChain pair.1.val pair.2 0).trans
        (by simpa only [pair.1.property] using segment.replaceChain_current pair.1.val)
    · exact segment.replaceChain_self pair.1.val pair.2

theorem uniform_secrets (segment : OtsPrefix) :
    PMF.uniformOfFintype OtsFrontierValues =
      (PMF.uniformOfFintype segment.ErasedSecrets).bind (fun other =>
        (PMF.uniformOfFintype Digest).map (segment.replaceChain other.val)) := by
  have h := PMF.uniformOfFintype_map_of_bijective segment.secretSplit.symm segment.secretSplit.symm.bijective
  rw [UniformTableSplit.uniform_product, PMF.map_bind] at h
  simpa only [PMF.map_comp, Function.comp_def, secretSplit, Equiv.coe_fn_symm_mk] using h.symm

theorem sampleOtsSecrets_eq_split (segment : OtsPrefix) :
    𝒟[sampleOtsSecrets] = (do
      let other ← 𝒟[PMF.uniformOfFintype segment.ErasedSecrets]
      let secret ← 𝒟[PMF.uniformOfFintype Digest]
      pure (segment.replaceChain other.val secret) : SPMF OtsFrontierValues) := by
  rw [sampleOtsSecrets, evalDist_uniformSample, segment.uniform_secrets]
  simp only [← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map, evalDist_bind, map_eq_bind_pure_comp,
    Function.comp_apply, evalDist_pure]

end SphincsSecurity.Concrete.OtsPrefix
