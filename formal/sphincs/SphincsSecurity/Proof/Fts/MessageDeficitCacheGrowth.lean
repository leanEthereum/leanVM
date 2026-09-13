import SphincsSecurity.Proof.Fts.MessageDeficitMomentGrowth
namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def MessageInputAt (parameter : PublicParameter) (root : Digest) (message : Message) (input : HashInput) : Prop :=
  ∃ randomness, input = tweakableHashInput parameter .message (Concrete.messageDigestPayload root message randomness)

theorem MessageInputAt.unique {parameter : PublicParameter} {root : Digest} {left right : Message} {input : HashInput}
    (hl : MessageInputAt parameter root left input) (hr : MessageInputAt parameter root right input) : left = right := by
  obtain ⟨lr, hl⟩ := hl
  obtain ⟨rr, hr⟩ := hr
  exact (Concrete.messageDigestPayload_injective root
    (tweakableHashInput_injective parameter (by trivial) (by trivial) (hl.symm.trans hr)).2).1

private theorem filteredCache_encard_cacheQuery (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput)
    (hfresh : cache input = none) (P : Sigma HashSpec.Range → Prop) :
    (({entry ∈ (cache.cacheQuery input output).toSet | P entry}.encard : ENat) : ENNReal) =
      (({entry ∈ cache.toSet | P entry}.encard : ENat) : ENNReal) + if P ⟨input, output⟩ then 1 else 0 := by
  have hset : (cache.cacheQuery input output).toSet = insert ⟨input, output⟩ cache.toSet := by
    apply Set.Subset.antisymm (QueryCache.toSet_cacheQuery_subset_insert cache input output)
    rintro entry (heq | hold)
    · subst entry
      exact QueryCache.cacheQuery_self _ _ _
    · exact QueryCache.toSet_mono (QueryCache.le_cacheQuery cache hfresh) hold
  by_cases hp : P ⟨input, output⟩
  · have heq : {entry ∈ (cache.cacheQuery input output).toSet | P entry} =
        insert ⟨input, output⟩ {entry ∈ cache.toSet | P entry} := by
      rw [hset]
      ext entry
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
      constructor
      · rintro ⟨heq | hold, hentry⟩
        · exact Or.inl heq
        · exact Or.inr ⟨hold, hentry⟩
      · rintro (rfl | ⟨hold, hentry⟩)
        · exact ⟨Or.inl rfl, hp⟩
        · exact ⟨Or.inr hold, hentry⟩
    have hnot : (⟨input, output⟩ : Sigma HashSpec.Range) ∉ {entry ∈ cache.toSet | P entry} := by
      rintro ⟨hmem, _⟩
      change cache input = some output at hmem
      rw [hfresh] at hmem
      cases hmem
    rw [heq, Set.encard_insert_of_notMem hnot, if_pos hp, ENat.toENNReal_add, ENat.toENNReal_one]
  · have heq : {entry ∈ (cache.cacheQuery input output).toSet | P entry} = {entry ∈ cache.toSet | P entry} := by
      rw [hset]
      ext entry
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
      constructor
      · rintro ⟨rfl | hold, hentry⟩
        · exact False.elim (hp hentry)
        · exact ⟨hold, hentry⟩
      · rintro ⟨hold, hentry⟩
        exact ⟨Or.inr hold, hentry⟩
    rw [heq, if_neg hp, add_zero]

theorem cachedMessageEntryCount_cacheQuery (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput) (hfresh : cache input = none) :
    cachedMessageEntryCount (cache.cacheQuery input output) parameter root message =
      cachedMessageEntryCount cache parameter root message + if MessageInputAt parameter root message input then 1 else 0 :=
  filteredCache_encard_cacheQuery cache input output hfresh (fun entry => MessageInputAt parameter root message entry.1)

theorem cachedMessageEntryCountWhere_cacheQuery (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput) (hfresh : cache input = none) (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere (cache.cacheQuery input output) parameter root message P =
      cachedMessageEntryCountWhere cache parameter root message P +
        if MessageInputAt parameter root message input ∧ Concrete.signAttemptResultOfOutput output ≠ none ∧
          P (Concrete.hashOutputFewTimeView output) then 1 else 0 := by
  have h := filteredCache_encard_cacheQuery cache input output hfresh
      (fun entry => MessageInputAt parameter root message entry.1 ∧ Concrete.signAttemptResultOfOutput entry.2 ≠ none ∧
        P (Concrete.hashOutputFewTimeView entry.2))
  simp only [cachedMessageEntryCountWhere, cachedMessageInputSetWhere, cachedMessageInputSet, MessageInputAt, Set.mem_setOf_eq, and_assoc] at h ⊢
  split_ifs at h ⊢ <;> exact h

theorem messageDeficitScore_cacheQuery (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (output : HashOutput) (hfresh : cache input = none) :
    messageDeficitScore parameter root message (cache.cacheQuery input output) =
      if MessageInputAt parameter root message input then
        messageDeficitScore parameter root message cache + (if Concrete.Admissible (truncateMessageDigest output) then -1023 else 1)
      else messageDeficitScore parameter root message cache := by
  rw [messageDeficitScore, cachedMessageEntryCount_cacheQuery _ _ _ _ _ _ hfresh,
    cachedMessageEntryCountWhere_cacheQuery _ _ _ _ _ _ hfresh]
  simp only [and_true, Concrete.signAttemptResultOfOutput_ne_none_iff]
  split_ifs <;> try tauto
  all_goals
    rw [ENNReal.toReal_add (cachedMessageEntryCount_ne_top_of_finite parameter root message cache hfinite) (by finiteness),
      ENNReal.toReal_add (cachedMessageEntryCountWhere_ne_top_of_finite parameter root message cache hfinite _) (by finiteness)]
    simp only [ENNReal.toReal_one, ENNReal.toReal_zero, messageDeficitScore]
    ring

end SphincsSecurity
