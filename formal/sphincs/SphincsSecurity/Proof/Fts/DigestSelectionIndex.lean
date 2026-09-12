import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.DigestLoopRecord
import SphincsSecurity.Proof.Fts.RawProposalMomentBound

/-! ## WeightedBinomialOccupancy -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem uniform_view_index_weight_expectation (weight : Index → ENNReal) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight source.1) =
      (∑ index : Index, weight index) / (Fintype.card Index : ENNReal) := by
  have hmarginal : ∀ index, Pr[= index | (Prod.fst <$> ($ᵗ FewTimeView : ProbComp FewTimeView))] =
      Pr[= index | ($ᵗ Index : ProbComp Index)] := by
    intro index
    exact congrArg (fun distribution => distribution index)
      (evalDist_map_fst_uniformSample_prod (α := Index) (β := FtsTree → FtsLeaf))
  rw [← tsum_probOutput_map_mul (mx := ($ᵗ FewTimeView : ProbComp FewTimeView))
    (f := fun source : FewTimeView => source.1) (g := weight)]
  simp only [hmarginal, probOutput_uniformSample, tsum_fintype, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop

noncomputable def completeSelectedIndex (view : Option FewTimeView) : ProbComp Index :=
  view.elim ($ᵗ Index) (fun selected => pure selected.1)

theorem probEvent_uniform_view_index (index : Index) :
    Pr[fun view : FewTimeView => view.1 = index | ($ᵗ FewTimeView : ProbComp FewTimeView)] =
      (Fintype.card Index : ENNReal)⁻¹ := by
  rw [probEvent_eq_tsum_ite]
  have h := uniform_view_index_weight_expectation
    (fun source => if source = index then (1 : ENNReal) else 0)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, one_div] using h

theorem cachedMessageEntryCountWhere_index_le (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (index : Index) :
    cachedMessageEntryCountWhere cache key.parameter key.root message (fun view => view.1 = index) ≤
      cachedIndexMultiplicity key.parameter cache index := by
  let entries := cachedMessageInputSetWhere cache key.parameter key.root message (fun view => view.1 = index)
  let inputOf : entries → HashInput := fun entry => entry.1.1
  have hinjective : Function.Injective inputOf := by
    rintro ⟨⟨left, leftOutput⟩, hleft⟩ ⟨⟨right, rightOutput⟩, hright⟩ heq
    change left = right at heq
    subst right
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq (Option.some.inj (hleft.1.1.symm.trans hright.1.1)))
  have hweight (entry : entries) :
      cacheMessageEntryWeight key.parameter (fun _ view => if view.1 = index then 1 else 0)
        cache (inputOf entry) = 1 := by
    rcases entry with ⟨⟨input, output⟩, ⟨hcached, randomness, hinput⟩, hadmissible, hindex⟩
    change cache input = some output at hcached
    have hmessage : FtsProbeSimulation.MessageHashInput key.parameter input :=
      ⟨messageDigestPayload key.root message randomness, hinput.symm⟩
    have hvalid := (signAttemptResultOfOutput_ne_none_iff output).mp hadmissible
    simp only [inputOf, cacheMessageEntryWeight, hcached, hmessage, hvalid, and_self,
      if_true, hindex]
  calc
    _ = ∑' _ : entries, (1 : ENNReal) := (ENNReal.tsum_set_one entries).symm
    _ = ∑' entry : entries, cacheMessageEntryWeight key.parameter
        (fun _ view => if view.1 = index then 1 else 0) cache (inputOf entry) :=
      tsum_congr (fun entry => (hweight entry).symm)
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective hinjective _

private theorem selectedLoopView_partition (attempts : Nat) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (P : FewTimeView → Prop) (result : DigestLoopRecord)
    (hr : result ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run cache)) :
    (if ∃ view, selectedLoopView? result = some view ∧ P view then (1 : ENNReal) else 0) =
      (if FreshSelectedView cache key message P result then 1 else 0) +
        (if PrehitSelectedView cache key message P result then 1 else 0) := by
  obtain ⟨selected, after⟩ := result
  cases selected with
  | none => simp [selectedLoopView?, FreshSelectedView, PrehitSelectedView]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      cases hc : cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) with
      | none => simp [selectedLoopView?, FreshSelectedView, PrehitSelectedView, hc]
      | some output =>
          have hattempt := signDigestLoop_initial_cached_result attempts key message randomness index leaves cache after output hc hr
          have hview : selectedFewTimeView index leaves = hashOutputFewTimeView output :=
            signAttemptResultOfOutput_view output index leaves hattempt
          simp [selectedLoopView?, FreshSelectedView, PrehitSelectedView, hc, hattempt, hview]

theorem probEvent_selectedLoopView_eq_fresh_add_cached (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    Pr[fun result => ∃ view, selectedLoopView? result = some view ∧ P view |
      (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] =
      freshDigestSelectionProbability key message cache * Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] +
        cachedMessageEntryCountWhere cache key.parameter key.root message P * exactDigestReuseWeight key message cache := by
  unfold freshDigestSelectionProbability
  rw [← probEvent_signDigestLoop_freshSelected_eq_mass_mul_uniform digestAttemptLimit key message cache cache P
    (onlyRejectedNewMessageEntries_self cache key message),
    ← probEvent_signDigestLoop_prehit_eq_count_mul_exactWeight]
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  by_cases hr : result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache)
  · have h := congrArg (fun value =>
      Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] * value)
      (selectedLoopView_partition digestAttemptLimit key message cache P result hr)
    simpa only [mul_add, mul_ite, mul_one, mul_zero] using h
  · simp only [probOutput_eq_zero_of_not_mem_support hr, ite_self, zero_add]

theorem probOutput_completeSelectedLoopIndex (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (index : Index) :
    Pr[= index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache >>=
      fun result => completeSelectedIndex (selectedLoopView? result)] =
      (freshDigestSelectionProbability key message cache + digestExhaustionProbability key message cache) *
        (Fintype.card Index : ENNReal)⁻¹ +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun view => view.1 = index) *
        exactDigestReuseWeight key message cache := by
  have h := probEvent_completeOption_eq
    ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache)
    (fun result => (selectedLoopView? result).map Prod.fst) ($ᵗ Index) (fun selected => selected = index)
  have hcomplete (view : Option FewTimeView) :
      (view.map Prod.fst).elim ($ᵗ Index : ProbComp Index) pure = completeSelectedIndex view := by
    cases view <;> rfl
  have hselected (result : DigestLoopRecord) :
      (∃ selected, (selectedLoopView? result).map Prod.fst = some selected ∧ selected = index) ↔
        ∃ view, selectedLoopView? result = some view ∧ view.1 = index := by
    cases selectedLoopView? result <;> simp
  have hnone (result : DigestLoopRecord) : (selectedLoopView? result).map Prod.fst = none ↔ result.1 = none := by
    cases hresult : result.1 <;> simp [selectedLoopView?, hresult]
  simp only [hcomplete, hselected, hnone] at h
  rw [probEvent_selectedLoopView_eq_fresh_add_cached, probEvent_uniform_view_index] at h
  simpa only [probEvent_eq_eq_probOutput, probOutput_uniformSample, digestExhaustionProbability,
    add_mul, add_assoc, add_comm, add_left_comm] using h

theorem probOutput_completeSelectedLoopIndex_le (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (index : Index) :
    Pr[= index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache >>=
      fun result => completeSelectedIndex (selectedLoopView? result)] ≤
      (Fintype.card Index : ENNReal)⁻¹ +
        exactDigestReuseWeight key message cache * cachedIndexMultiplicity key.parameter cache index := by
  rw [probOutput_completeSelectedLoopIndex]
  have hmass : freshDigestSelectionProbability key message cache + digestExhaustionProbability key message cache ≤ 1 := by
    calc
      _ ≤ (freshDigestSelectionProbability key message cache +
          cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) *
            exactDigestReuseWeight key message cache) + digestExhaustionProbability key message cache :=
        add_le_add le_self_add le_rfl
      _ = 1 := freshSelection_add_count_exactWeight_add_exhaustion key message cache
  exact add_le_add (mul_le_of_le_one_left' hmass)
    ((mul_le_mul' (cachedMessageEntryCountWhere_index_le key message cache index) le_rfl).trans_eq (mul_comm _ _))

theorem probOutput_completeSelectedLoopIndex_le_proposalRate (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (spent : Nat) (hspent : spent ≤ 2 ^ 127)
    (hcache : QueryCache.enncard cache ≤ spent) (hclean : ¬ MessageDeficitExceptional key cache)
    (hindex : ∀ index, cachedIndexMultiplicity key.parameter cache index ≤
      (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal)) (index : Index) :
    Pr[= index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache >>=
      fun result => completeSelectedIndex (selectedLoopView? result)] ≤ targetProposalIndexRate := by
  apply (probOutput_completeSelectedLoopIndex_le key message cache index).trans
  apply (add_le_add le_rfl (mul_le_mul'
    (exactDigestReuseWeight_le_near_uniform_of_clean_cache key cache spent hspent hcache hclean message) le_rfl)).trans
  simpa only [Nat.add_zero, Nat.cast_zero, zero_mul, add_zero] using
    targetProposalRate_of_cache_bound (cachedIndexMultiplicity key.parameter cache index)
      spent 0 0 0 hspent (Nat.zero_le _) (Nat.zero_le _) (hindex index)

end SphincsSecurity.Concrete
