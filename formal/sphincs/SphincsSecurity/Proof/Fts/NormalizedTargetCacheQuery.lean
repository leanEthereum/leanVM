import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CachedTargetSubsetMatch
import SphincsSecurity.Proof.Fts.NormalizedTargetMatches
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def normalizedCachedTargetSubsetMatch (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree) : ENNReal :=
  (Fintype.card FtsLeaf ^ required.card : Nat) * cachedTargetSubsetMatch parameter cache targetInput target required

noncomputable def normalizedTargetCacheProduct (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree) : ENNReal :=
  ∏ slot : Fin m, normalizedCachedTargetSubsetMatch parameter cache targetInput target (groups slot)

theorem normalizedCachedTargetSubsetMatch_eq_weight (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree) :
    normalizedCachedTargetSubsetMatch parameter cache targetInput target required =
      cacheMessageWeight parameter (fun input source => if input = targetInput then 0 else normalizedSourceSubsetMatch target source required) cache := by
  unfold normalizedCachedTargetSubsetMatch cachedTargetSubsetMatch
  rw [mul_comm, ← cacheMessageWeight_mul_right]
  congr 1
  funext input source
  split_ifs <;> simp only [normalizedSourceSubsetMatch, zero_mul, mul_comm]

theorem normalizedCachedTargetSubsetMatch_cacheQuery (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (hne : input ≠ targetInput) :
    normalizedCachedTargetSubsetMatch parameter (before.cacheQuery input output) targetInput target required =
      normalizedCachedTargetSubsetMatch parameter before targetInput target required +
        if Admissible (truncateMessageDigest output) then normalizedSourceSubsetMatch target (hashOutputFewTimeView output) required else 0 := by
  simp only [normalizedCachedTargetSubsetMatch, cachedTargetSubsetMatch_cacheQuery parameter before targetInput target required input output hfresh,
    hmessage, true_and, if_neg hne, mul_add, mul_ite, mul_zero, normalizedSourceSubsetMatch]

theorem normalizedTargetCacheProduct_cacheQuery (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree)
    (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (hne : input ≠ targetInput) :
    normalizedTargetCacheProduct parameter (before.cacheQuery input output) targetInput target groups =
      normalizedTargetCacheProduct parameter before targetInput target groups +
        ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
          (if Admissible (truncateMessageDigest output) then
            ∏ slot ∈ selected, normalizedSourceSubsetMatch target (hashOutputFewTimeView output) (groups slot) else 0) *
              ∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, normalizedCachedTargetSubsetMatch parameter before targetInput target (groups slot) := by
  unfold normalizedTargetCacheProduct
  simp only [normalizedCachedTargetSubsetMatch_cacheQuery parameter before targetInput target _ input output hfresh hmessage hne]
  rw [show (∏ slot : Fin m, (normalizedCachedTargetSubsetMatch parameter before targetInput target (groups slot) +
      if Admissible (truncateMessageDigest output) then normalizedSourceSubsetMatch target (hashOutputFewTimeView output) (groups slot) else 0)) =
      ∏ slot : Fin m, ((if Admissible (truncateMessageDigest output) then normalizedSourceSubsetMatch target (hashOutputFewTimeView output) (groups slot) else 0) +
        normalizedCachedTargetSubsetMatch parameter before targetInput target (groups slot)) by simp only [add_comm]]
  rw [Finset.prod_add, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _)]
  simp only [Finset.prod_empty, Finset.sdiff_empty, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro selected hselected
  congr 1
  by_cases hadmissible : Admissible (truncateMessageDigest output)
  · simp only [hadmissible, if_true]
  · simp only [hadmissible, if_false]
    obtain ⟨slot, hslot⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1
    exact Finset.prod_eq_zero hslot rfl

theorem expected_normalizedTargetCacheProduct_cacheQuery (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree)
    (hgroups : ∀ slot, (groups slot).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (input : HashInput) (hfresh : before input = none)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (hne : input ≠ targetInput) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      normalizedTargetCacheProduct parameter (before.cacheQuery input output) targetInput target groups) =
      normalizedTargetCacheProduct parameter before targetInput target groups +
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
          ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
            ∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, normalizedCachedTargetSubsetMatch parameter before targetInput target (groups slot) := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
  simp only [normalizedTargetCacheProduct_cacheQuery parameter before targetInput target groups input _ hfresh hmessage hne,
    mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  congr 1
  apply Finset.sum_congr rfl
  intro selected hselected
  simp only [← mul_assoc, ENNReal.tsum_mul_right]
  congr 1
  exact expected_hash_normalizedSourceSubsetMatch_prod target groups selected
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
    (fun slot _ => hgroups slot) (fun i _ j _ hij => hdisjoint hij)

end SphincsSecurity.Concrete
