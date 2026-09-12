import SphincsSecurity.Proof.Ots.EncodingNeighborProbability
import SphincsSecurity.Proof.Ots.ReferenceEncodingTable
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def FreshEncodingSupport (reference : Encoding) (allowed : Finset HashOutput) : Prop :=
  allowed = Finset.univ ∨ ∀ output ∈ allowed, decodeEncodingOutput output = none ∨ decodeEncodingOutput output = some reference

theorem firstSuccess_allowed_fresh {n : Nat} (index : Fin n) (reference : Encoding) (coordinate : Fin n) :
    FreshEncodingSupport reference (FirstSuccessTable.allowed decodeEncodingOutput index reference coordinate) := by
  unfold FirstSuccessTable.allowed
  split_ifs with hlt heq
  · exact Or.inr fun output ho => Or.inl ((FirstSuccessTable.mem_invalid _ _).mp ho)
  · exact Or.inr fun output ho => Or.inr ((FirstSuccessTable.mem_fiber _ _ _).mp ho)
  · exact Or.inl rfl

theorem freshEncodingSupport_probability_le (reference : Encoding) (targets : Finset Encoding) (href : reference ∉ targets)
    (allowed : Finset HashOutput) (ha : allowed.Nonempty) (hallowed : FreshEncodingSupport reference allowed) :
    Pr[fun output : HashOutput => truncateHash output ∈ TargetSum.decodingDigests targets | PMF.uniformOfFinset allowed ha] ≤
      (targets.card : ENNReal) / Fintype.card Digest := by
  rcases hallowed with rfl | hrestricted
  · have h := TargetSum.decodingDigests_uniform_le targets
    simpa only [probEvent_eq_tsum_ite, probOutput_uniformSample, PMF.probOutput_eq_apply, PMF.uniformOfFinset_apply,
      Finset.mem_univ, if_true, Finset.card_univ] using h
  · have hzero : Pr[fun output : HashOutput => truncateHash output ∈ TargetSum.decodingDigests targets |
        PMF.uniformOfFinset allowed ha] = 0 := by
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro output
      by_cases hm : output ∈ allowed
      · have hn : truncateHash output ∉ TargetSum.decodingDigests targets := by
          intro hd
          obtain ⟨word, hw, hdecode⟩ := TargetSum.mem_decodingDigests.mp hd
          change decodeEncodingOutput output = some word at hdecode
          rcases hrestricted output hm with hi | hr
          · rw [hi] at hdecode
            contradiction
          · have he : reference = word := Option.some.inj (hr.symm.trans hdecode)
            exact href (he ▸ hw)
        exact if_neg hn
      · simp only [PMF.uniformOfFinset_apply, if_neg hm, ite_self]
    rw [hzero]
    exact zero_le

theorem freshEncodingSupport_neighbor_le (reference : Encoding) (lowered : ChainIndex)
    (allowed : Finset HashOutput) (ha : allowed.Nonempty) (hallowed : FreshEncodingSupport reference allowed) :
    Pr[fun output : HashOutput => truncateHash output ∈ TargetSum.decodingDigests (TargetSum.unitNeighbors reference lowered) |
      PMF.uniformOfFinset allowed ha] ≤ 41 / (Fintype.card Digest : ENNReal) := by
  have href : reference ∉ TargetSum.unitNeighbors reference lowered := by
    intro h
    obtain ⟨raised, ht⟩ := TargetSum.mem_unitNeighbors.mp h
    exact ht.ne rfl
  exact (freshEncodingSupport_probability_le reference _ href allowed ha hallowed).trans
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (TargetSum.unitNeighbors_card_le reference lowered)) _)

theorem freshEncodingSupport_all_neighbors_le (reference : Encoding)
    (allowed : Finset HashOutput) (ha : allowed.Nonempty) (hallowed : FreshEncodingSupport reference allowed) :
    Pr[fun output : HashOutput => truncateHash output ∈ TargetSum.decodingDigests (TargetSum.allUnitNeighbors reference) |
      PMF.uniformOfFinset allowed ha] ≤ 1722 / (Fintype.card Digest : ENNReal) := by
  have href : reference ∉ TargetSum.allUnitNeighbors reference := by
    intro h
    obtain ⟨lowered, raised, ht⟩ := TargetSum.mem_allUnitNeighbors.mp h
    exact ht.ne rfl
  exact (freshEncodingSupport_probability_le reference _ href allowed ha hallowed).trans
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (TargetSum.allUnitNeighbors_card_le reference)) _)

end SphincsSecurity.Concrete
