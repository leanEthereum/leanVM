import Sphincs.BridgePotentialA7

/-! The refined events of a final state against the payoff of the linear potential. The
prepared cache holds structural inputs and the encoding search queries only, and no search
answer decodes to a unit neighbour of the prepared word. So, for any table extending the
exposed coordinates, a first-order hit or a correct guess is a hit of the first-order targeting,
the WOTS events are WOTS events of the state, two forest contacts are a pair of the payoff, and a
forest contact is a contact without guess record or a recorded contact (both against the table). -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.PotentialA

open Concrete Completeness Graph HiddenGraph HiddenDebt HiddenBridge HiddenCost HiddenReveal EncodingCode
  TargetAssignment

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] ReferenceChoice.selection encodingAttemptLimit

variable [Params]

section Prepared

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
  (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))

include hprepared in
/-- **Origin of a prepared entry.** A structural input, or an encoding search query whose answer
decodes to nothing or to the prepared word. -/
theorem prepared_origin (input : HashInput) (answer : HashOutput) (hcache : prepared.2 input = some answer) :
    (∃ position : Position, ¬IsRowPosition position ∧
      ∃ payload, input = tweakableHashInput (truncateHash parameterOutput) position.domain payload) ∨
    ∃ (leaf : Index) (counter : Counter), input = Wots.encodingInput (truncateHash parameterOutput) topLayer rootTree
        leaf ((sampleData parameterOutput fixed highs remaining).forestKey leaf) counter ∧
      (TargetSum.decodeDigest (truncateHash answer) = none ∨
        TargetSum.decodeDigest (truncateHash answer) = some (preparedWord prepared.1 leaf)) := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn prepared.2
  have hsearch := (preparation_support _ _ _ prepared hprepared f hf).2
  rcases Graph.hash_cache_origin _ _ prepared.1 prepared.2 hprepared f hf input answer hcache with
    hstruct | hquery
  · left
    obtain ⟨position, hmem, rfl⟩ : ∃ position ∈ graphOrder (structActive (truncateHash parameterOutput)),
        input = canonicalGraphInput (truncateHash parameterOutput)
          (GraphCorrectness.materialOts (splitMaterial parameterOutput highs remaining fixed))
          (GraphCorrectness.materialFts (splitMaterial parameterOutput highs remaining fixed)) position
          (Assembly.labelsOf (splitMaterial parameterOutput highs remaining fixed)
            (splitAnswers highs remaining fixed)) := by
      by_contra hno
      push Not at hno
      have hnone := programGraphCache_empty_none (truncateHash parameterOutput)
        (GraphCorrectness.materialOts (splitMaterial parameterOutput highs remaining fixed))
        (GraphCorrectness.materialFts (splitMaterial parameterOutput highs remaining fixed))
        (Assembly.labelsOf (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed))
        _ input hno
      unfold structCache at hstruct
      rw [splitMaterial_parameter, hnone] at hstruct
      cases hstruct
    exact ⟨position, ((mem_graphOrder _ _).mp hmem).2, _, rfl⟩
  · right
    obtain ⟨leaf, hleaf⟩ := queriedInputs_sequenceFin_mem f _ hquery
    obtain ⟨counter, rfl, hcase⟩ := ReferenceChoice.search_query_classification f _ topLayer rootTree leaf _
      encodingAttemptLimit 0 _ hleaf
    refine ⟨leaf, counter, rfl, ?_⟩
    have hanswer : f (Wots.encodingInput (truncateHash parameterOutput) topLayer rootTree leaf
        ((sampleData parameterOutput fixed highs remaining).forestKey leaf) counter) = answer := hf hcache
    rcases hcase with hnone | hsome
    · left
      rw [← hanswer]
      simpa only [encode, evalWithAnswerFn_bind, eval_tweakableHash, evalWithAnswerFn_pure, Wots.encodingInput]
        using hnone
    · right
      cases hfe : Prefix.firstEncoding f (truncateHash parameterOutput) topLayer rootTree leaf
          ((sampleData parameterOutput fixed highs remaining).forestKey leaf) encodingAttemptLimit 0 with
      | none =>
          rw [hfe] at hsome
          cases hsome
      | some pair =>
          rw [hfe, Option.map_some, Option.some.injEq] at hsome
          have hctr := (Wots.encodingInput_injective _ _ _ _ hsome).2
          have hsound := ReferenceChoice.firstEncoding_sound f _ topLayer rootTree leaf _ encodingAttemptLimit 0
            pair.1 pair.2 hfe
          have hdec := Wots.decode_of_encode f _ topLayer rootTree leaf _ pair.1 pair.2 hsound
          rw [hctr, hanswer] at hdec
          have hw : preparedWord prepared.1 leaf = pair.2 := by
            unfold preparedWord
            rw [← hsearch leaf, hfe]
            rfl
          rw [hw]
          exact hdec

theorem position_domain_chain {position : Position} {lay : Layer} {tree : TreeIndex} {leaf : LeafIndex}
    {chain : ChainIndex} {step : ChainStep} (h : position.domain = .chain lay tree leaf chain step) :
    IsRowPosition position := by
  cases position <;> simp [Position.domain] at h
  trivial

theorem position_domain_fchain {position : Position} {index : Index} {c : Coord} {sp : SuperIdx} {j : SubIdx}
    {a : ChildIdx} {i : FChain} {t : FStep}
    (h : position.domain = .fchain index c sp j a i t) : IsRowPosition position := by
  cases position <;> simp [Position.domain] at h
  trivial

theorem position_domain_enc {position : Position} {lay : Layer} {tree : TreeIndex} {leaf : LeafIndex}
    (h : position.domain = .encoding lay tree leaf) : False := by
  cases position <;> simp [Position.domain] at h

include hprepared in
/-- The prepared cache holds no root-tree chain input. -/
theorem prepared_not_chain {l : Index} {i : ChainIndex} {st : ChainStep} {v : Digest} {a : HashOutput}
    (h : prepared.2 (chainInput (truncateHash parameterOutput) l i st v) = some a) : False := by
  rcases prepared_origin parameterOutput fixed highs remaining prepared hprepared _ a h with
    ⟨position, hrow, payload, heq⟩ | ⟨leaf, counter, heq, -⟩
  · exact hrow (position_domain_chain (domain_eq_of_input heq trivial (Position.domain_inRange _)).1.symm)
  · exact chainInput_ne_enc heq

include hprepared in
/-- The prepared cache holds no forest step. -/
theorem prepared_not_fchain {f : FIn} {a : HashOutput}
    (h : prepared.2 (f.input (truncateHash parameterOutput)) = some a) : False := by
  rcases prepared_origin parameterOutput fixed highs remaining prepared hprepared _ a h with
    ⟨position, hrow, payload, heq⟩ | ⟨leaf', counter, heq, -⟩
  · exact hrow (position_domain_fchain (domain_eq_of_input heq trivial (Position.domain_inRange _)).1.symm)
  · exact enc_ne_fchain heq.symm

include hprepared in
/-- No prepared encoding answer decodes to a unit neighbour of the prepared word. -/
theorem prepared_no_marker {l : Index} {msg : Digest} {ctr : Counter} {a : HashOutput} {i : ChainIndex}
    (h : prepared.2 (Wots.encodingInput (truncateHash parameterOutput) topLayer rootTree l msg ctr) = some a)
    (hm : truncateHash a ∈ decodingDigests (unitNeighbors (preparedWord prepared.1 l) i)) : False := by
  obtain ⟨word, hword, hdec⟩ := mem_decodingDigests.1 hm
  have hne := (mem_unitNeighbors.1 hword).ne
  rcases prepared_origin parameterOutput fixed highs remaining prepared hprepared _ a h with
    ⟨position, -, payload, heq⟩ | ⟨leaf, counter, heq, hcase⟩
  · exact position_domain_enc (domain_eq_of_input heq trivial (Position.domain_inRange _)).1.symm
  · obtain ⟨rfl, -, -⟩ := enc_inj heq
    rcases hcase with hnone | hsome
    · rw [hdec] at hnone
      cases hnone
    · rw [hdec, Option.some.injEq] at hsome
      exact hne hsome

end Prepared

/-! ### The refined events of a final state -/

section Events

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
  (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
  (known : Knowledge Coordinate) (ρ : ℝ) (s : St)
  (hinv : (ctxA parameterOutput fixed highs remaining prepared known ρ).Inv s)
  (T : Coordinate → Digest) (hT : tableExtending s.known T = T)

/-- A forest contact carrying its guess record, at a given step. -/
def RecordedContactAt (K : Ctx) (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (t : FStep) : Prop :=
  ∃ v, K.FCT T s ⟨index, c, sp, j, a, i, t, v⟩ ∧ Ctx.Recd s ⟨index, c, sp, j, a, i, t, v⟩

include hinv hT in
theorem anchor_value {c : Coordinate}
    (hc : (ctxA parameterOutput fixed highs remaining prepared known ρ).Anchor c) :
    T c = (ctxA parameterOutput fixed highs remaining prepared known ρ).F c := by
  have hag := (ForsPotential.agrees_iff_extending _ T).2 hT
  exact hag c _ (hinv.anchored c hc)

theorem initial_none_of_not {x : HashInput} (h : ∀ a, prepared.2 x = some a → False) : prepared.2 x = none := by
  cases hx : prepared.2 x with
  | none => rfl
  | some a => exact (h a hx).elim

include hprepared hinv hT in
/-- **First-order hits.** A cached hit of the first-order targets of any table extending the
exposed coordinates is a hit of the targeting. -/
theorem hit_of_bad
    (hfix : tableExtending (knownOf (truncateHash parameterOutput) fixed) T = T)
    (hbad : CacheMatch.Bad (targetsA (truncateHash parameterOutput) prepared.1
      (compTable parameterOutput fixed highs remaining T prepared.1)) s.cache) :
    Hit (ctxA parameterOutput fixed highs remaining prepared known ρ).tg prepared.2 T s := by
  obtain ⟨input, answer, hcache, hmem⟩ := hbad
  unfold targetsA at hmem
  split_ifs at hmem with hsec
  · exact absurd hmem (Finset.notMem_empty _)
  have hag := (ForsPotential.agrees_iff_extending _ T).2 hT
  cases hinit : prepared.2 input with
  | some old =>
      exfalso
      have hsame := hinv.prepared input old hinit
      rw [hcache, Option.some.injEq] at hsame
      subst hsame
      exact prepared_clean parameterOutput fixed highs remaining prepared hprepared T input answer hinit hmem
  | none =>
      have hkind : (ctxA parameterOutput fixed highs remaining prepared known ρ).tg.kind input =
          (sampleTargeting parameterOutput fixed highs remaining prepared.1).kind input := ite_eq_right hsec
      rcases target_kind parameterOutput fixed highs remaining T hfix prepared.1 input _ hmem with
        hfixed | ⟨coordinate, hhidden, hvalue⟩
      · exact Or.inl (Or.inl ⟨input, answer, _, hcache, hinit, hkind.trans hfixed, rfl⟩)
      · exact hit_of_debt hag coordinate (Or.inr ⟨input, answer, hcache, hinit, hkind.trans hhidden, hvalue⟩)

include hT in
/-- **Correct guesses** are hits of the targeting. -/
theorem hit_of_correctGuess (h : CorrectGuess T s) :
    Hit (ctxA parameterOutput fixed highs remaining prepared known ρ).tg prepared.2 T s := by
  have hag := (ForsPotential.agrees_iff_extending _ T).2 hT
  obtain ⟨guess, hguess, hcorrect⟩ := h
  refine hit_of_debt hag guess.1 (Or.inl ?_)
  change (guess.1, T guess.1) ∈ s.guesses
  rw [hcorrect]
  exact hguess

include hprepared hinv hT in
/-- **WOTS events.** -/
theorem wotsBad_of_event (h : WotsEvent (truncateHash parameterOutput) prepared.1 T s.cache) :
    (ctxA parameterOutput fixed highs remaining prepared known ρ).WotsBad s := by
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  obtain ⟨leaf, hl, hev⟩ := h
  have hfront : ∀ chain, frontierValue prepared.1 T leaf chain = K.front leaf chain := fun chain =>
    anchor_value parameterOutput fixed highs remaining prepared known ρ s hinv T hT
      (Or.inl ⟨rfl, rfl, hl, le_rfl⟩)
  have hchain : ∀ (chain : ChainIndex) (st : ChainStep) (v : Digest) (a : HashOutput),
      s.cache (chainInput (truncateHash parameterOutput) leaf chain st v) = some a →
      K.Fr s (chainInput K.p leaf chain st v) a := fun chain st v a hc =>
    ⟨hc, initial_none_of_not prepared (fun a' h => prepared_not_chain parameterOutput fixed highs remaining
      prepared hprepared h)⟩
  have hcontact : ∀ chain, ContactAt (truncateHash parameterOutput) prepared.1 T s.cache leaf chain →
      (K.ContactB s leaf chain).Nonempty := by
    rintro chain ⟨step, payload, answer, hstep, -, hc, hv⟩
    exact ⟨payload, _, answer, ⟨step, hstep, rfl⟩, hchain chain step payload answer hc, hv.trans (hfront chain)⟩
  have hmarker : ∀ chain, MarkerAt (truncateHash parameterOutput) prepared.1 s.cache leaf chain →
      K.Marker s leaf chain := by
    rintro chain ⟨message, counter, answer, candidate, hc, hdec, hnb⟩
    have hm : truncateHash answer ∈ K.markSet leaf chain :=
      mem_decodingDigests.2 ⟨candidate, mem_unitNeighbors.2 hnb, hdec⟩
    refine ⟨message, counter, answer, ⟨hc, initial_none_of_not prepared fun a' h' => ?_⟩, hm⟩
    have hsame := hinv.prepared _ a' h'
    have hc' : s.cache (Wots.encodingInput K.p topLayer rootTree leaf message counter) = some answer := hc
    rw [hc', Option.some.injEq] at hsame
    subst hsame
    exact prepared_no_marker parameterOutput fixed highs remaining prepared hprepared h' hm
  refine ⟨leaf, hl, ?_⟩
  rcases hev with ⟨chain, first, second, payload, answer, answer', hfs, hsw, hc1, hc2, hv⟩ |
    ⟨chain, hc, hm⟩ | ⟨chain, chain', hne, hc, hc'⟩
  · refine Or.inl ⟨chain, truncateHash answer, ?_, ?_⟩
    · exact ⟨_, answer', ⟨second, hsw, rfl⟩, hchain chain second _ answer' hc2, hv.trans (hfront chain)⟩
    · have hw : (K.w leaf chain).val = (preparedWord prepared.1 leaf chain).val := rfl
      exact ⟨_, answer, ⟨first, payload, by omega, rfl⟩, hchain chain first payload answer hc1, rfl⟩
  · exact Or.inr (Or.inl ⟨chain, hcontact chain hc, hmarker chain hm⟩)
  · exact Or.inr (Or.inr ⟨chain, chain', hne, hcontact chain hc, hcontact chain' hc'⟩)

include hprepared in
theorem fContact_of_at {index : Index} {c : Coord} {sp : SuperIdx} {j : SubIdx} {a : ChildIdx} {i : FChain}
    {t : FStep} (h : FContactAt (truncateHash parameterOutput) T s.cache index c sp j a i t) :
    ∃ v, (ctxA parameterOutput fixed highs remaining prepared known ρ).FCT T s ⟨index, c, sp, j, a, i, t, v⟩ := by
  obtain ⟨payload, answer, -, hc, hv⟩ := h
  exact ⟨payload, answer, ⟨hc, initial_none_of_not prepared fun a' h' =>
    prepared_not_fchain parameterOutput fixed highs remaining prepared hprepared (f := ⟨_, _, _, _, _, _, _, _⟩) h'⟩, hv⟩

include hprepared in
/-- **Two forest contacts** at different chains of one index are a pair of the payoff. -/
theorem twoFors_of_contacts (h : TwoForestContacts (truncateHash parameterOutput) T s.cache) :
    ∃ f g, f.Rel g ∧ (ctxA parameterOutput fixed highs remaining prepared known ρ).FCT T s f ∧
      (ctxA parameterOutput fixed highs remaining prepared known ρ).FCT T s g := by
  obtain ⟨index, c, sp, j, a, i, t, c', sp', j', a', i', t', hne, hc, hc'⟩ := h
  obtain ⟨v, hf⟩ := fContact_of_at parameterOutput fixed highs remaining prepared hprepared known ρ s T hc
  obtain ⟨v', hf'⟩ := fContact_of_at parameterOutput fixed highs remaining prepared hprepared known ρ s T hc'
  exact ⟨⟨index, c, sp, j, a, i, t, v⟩, ⟨index, c', sp', j', a', i', t', v'⟩, ⟨rfl, hne⟩, hf, hf'⟩

include hprepared in
/-- **A forest contact** is a contact without guess record or a recorded contact. -/
theorem fContactAt_split {index : Index} {c : Coord} {sp : SuperIdx} {j : SubIdx} {a : ChildIdx} {i : FChain}
    {t : FStep} (h : FContactAt (truncateHash parameterOutput) T s.cache index c sp j a i t) :
    (∃ f, (ctxA parameterOutput fixed highs remaining prepared known ρ).FCT T s f ∧ ¬Ctx.Recd s f) ∨
      RecordedContactAt s T (ctxA parameterOutput fixed highs remaining prepared known ρ) index c sp j a i t := by
  obtain ⟨v, hf⟩ := fContact_of_at parameterOutput fixed highs remaining prepared hprepared known ρ s T h
  by_cases hg : Ctx.Recd s ⟨index, c, sp, j, a, i, t, v⟩
  · exact Or.inr ⟨v, hf, hg⟩
  · exact Or.inl ⟨_, hf, hg⟩

include hprepared in
/-- **Forest contacts at revealed chains.** Without a guess record they are a payoff event; what
remains is a recorded contact whose chain is revealed at or below its step. -/
theorem revealedContact_split (reveals : List Coordinate)
    (h : RevealedContact (truncateHash parameterOutput) T s.cache reveals) :
    (∃ f, (ctxA parameterOutput fixed highs remaining prepared known ρ).FCT T s f ∧ ¬Ctx.Recd s f) ∨
      ∃ index c sp j a i t, (∃ q : FPos, q.val ≤ t.val ∧ Coordinate.fchain index c sp j a i q ∈ reveals) ∧
        RecordedContactAt s T (ctxA parameterOutput fixed highs remaining prepared known ρ) index c sp j a i t := by
  obtain ⟨index, c, sp, j, a, i, t, hrev, hc⟩ := h
  rcases fContactAt_split parameterOutput fixed highs remaining prepared hprepared known ρ s T hc with hng | hrec
  · exact Or.inl hng
  · exact Or.inr ⟨index, c, sp, j, a, i, t, hrev, hrec⟩

/-- A near cover whose contact carries its guess record. -/
def ForestNearRecorded (K : Ctx) (root : Digest) (outcome : Outcome) (reveals : List Coordinate) : Prop :=
  SigningTranscript.Valid outcome.2.1 ∧
  ∃ digest, cachedDigest s.cache K.p root outcome.1.message outcome.1.signature.randomness = some digest ∧
    Landed K.p (digestIndex digest) ∧
    (∀ entry ∈ outcome.2.1, ∀ signature, entry.2 = some signature →
      ¬(entry.1 = outcome.1.message ∧ signature.randomness = outcome.1.signature.randomness)) ∧
    ∃ c j i t, RecordedContactAt s T K (digestIndex digest) c (digestMarks digest c).super j
        ((digestMarks digest c).child j) i t ∧
      ∀ c' j' i', (c', j', i') ≠ (c, j, i) → ChainCov (revealedSet reveals) (fullDigestView digest) c' j' i'

include hprepared in
/-- **Near covers.** Without a guess record the contact is a payoff event; what remains is a near
cover with a recorded contact. -/
theorem forestNear_split (root : Digest) (outcome : Outcome) (reveals : List Coordinate)
    (h : ForestNear (truncateHash parameterOutput) T s.cache root outcome reveals) :
    (∃ f, (ctxA parameterOutput fixed highs remaining prepared known ρ).FCT T s f ∧ ¬Ctx.Recd s f) ∨
      ForestNearRecorded s T (ctxA parameterOutput fixed highs remaining prepared known ρ) root outcome reveals := by
  obtain ⟨hvalid, digest, hdigest, hland, hunsigned, c, j, i, t, hc, hcov⟩ := h
  rcases fContactAt_split parameterOutput fixed highs remaining prepared hprepared known ρ s T hc with hng | hrec
  · exact Or.inl hng
  · exact Or.inr ⟨hvalid, digest, hdigest, hland, hunsigned, c, j, i, t, hrec, hcov⟩

include hprepared hinv hT in
/-- **The refined bad event.** Every component of `badA` of a final state is a payoff event, a
recorded forest contact at a revealed chain, a near cover with a recorded contact, or a cover. -/
theorem badA_split (hfix : tableExtending (knownOf (truncateHash parameterOutput) fixed) T = T)
    (res : Option Outcome) (reveals : List Coordinate) (entries : List (Entry HashInput))
    (h : badA parameterOutput fixed highs remaining prepared.1 T (((res, reveals), entries), s.cache)) :
    payoffA parameterOutput fixed highs remaining prepared known ρ T s = 1 ∨
      (∃ index c sp j a i t, (∃ q : FPos, q.val ≤ t.val ∧ Coordinate.fchain index c sp j a i q ∈ reveals) ∧
        RecordedContactAt s T (ctxA parameterOutput fixed highs remaining prepared known ρ) index c sp j a i t) ∨
      ∃ outcome, res = some outcome ∧
        (ForestNearRecorded s T (ctxA parameterOutput fixed highs remaining prepared known ρ)
            (sampleData parameterOutput fixed highs remaining).root outcome reveals ∨
          ForestCover (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining).root
            outcome reveals s.cache) := by
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  have hpay : ∀ P : Prop, (P → Hit K.tg prepared.2 T s ∨ K.WotsBad s ∨ (∃ f, K.FCT T s f ∧ ¬Ctx.Recd s f) ∨
      (∃ f g, f.Rel g ∧ K.FCT T s f ∧ K.FCT T s g)) → P →
      payoffA parameterOutput fixed highs remaining prepared known ρ T s = 1 := by
    intro P hP hp
    unfold payoffA Ctx.payoff
    exact ite_eq_left (hP hp)
  rcases h with hhit | hw | hrev | htwo | ⟨outcome, hres, hnear | hcov⟩
  · exact Or.inl (hpay _ (fun h => Or.inl (hit_of_bad parameterOutput fixed highs remaining prepared hprepared
      known ρ s hinv T hT hfix h)) hhit)
  · exact Or.inl (hpay _ (fun h => Or.inr (Or.inl (wotsBad_of_event parameterOutput fixed highs remaining
      prepared hprepared known ρ s hinv T hT h))) hw)
  · rcases revealedContact_split parameterOutput fixed highs remaining prepared hprepared known ρ s T
      reveals hrev with hng | hrec
    · exact Or.inl (hpay _ (fun h => Or.inr (Or.inr (Or.inl h))) hng)
    · exact Or.inr (Or.inl hrec)
  · exact Or.inl (hpay _ (fun h => Or.inr (Or.inr (Or.inr (twoFors_of_contacts parameterOutput fixed highs
      remaining prepared hprepared known ρ s T h)))) htwo)
  · rcases forestNear_split parameterOutput fixed highs remaining prepared hprepared known ρ s T _ outcome
      reveals hnear with hng | hrec
    · exact Or.inl (hpay _ (fun h => Or.inr (Or.inr (Or.inl h))) hng)
    · exact Or.inr (Or.inr ⟨outcome, hres, Or.inl hrec⟩)
  · exact Or.inr (Or.inr ⟨outcome, hres, Or.inr hcov⟩)

end Events

/-! ### Final states of interpreted runs -/

/-- The invariant holds at every final state of an interpreted run. -/
theorem inv_interp (K : Ctx) (M : HiddenRows.Model HashInput HashOutput Address Coordinate)
    (hMp : M.parse = HiddenGraph.parse K.p (candidateActive K.p)) (hMi : M.incoming = Address.inputCoordinate)
    (tg' : Targeting HashInput HashOutput Coordinate) (initial' : QueryCache HashSpec) {α : Type}
    (comp : OracleComp (SourceCostSpec HashInput HashOutput Coordinate) α) :
    ∀ budget (s : St), K.Inv s → ∀ out ∈ support (interp tg' initial' M comp budget s), K.Inv out.2 := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
      intro budget s hs out hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout]
      exact hs
  | query_bind input next ih =>
      intro budget s hs out hout
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        exact ih result.1 _ result.2 (K.inv_step M hMp hMi input s hs result hresult) inner hinner
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout]
        exact hs

section Final

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
  (known : Knowledge Coordinate) (ρ : ℝ)
  (hknown : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
    (knownOf (truncateHash parameterOutput) fixed)))
  (tg : Targeting HashInput HashOutput Coordinate) {α : Type}
  (comp : OracleComp (SourceCostSpec HashInput HashOutput Coordinate) α) (total : ℕ)

include hknown in
/-- **The invariant at the end of the run**, for the inclusion lemmas. -/
theorem inv_final (out : Run HashInput Coordinate α × St)
    (hout : out ∈ support (interp tg prepared.2 (sampleModel parameterOutput highs) comp total
      (DebtState.start prepared.2 known))) :
    (ctxA parameterOutput fixed highs remaining prepared known ρ).Inv out.2 :=
  inv_interp (ctxA parameterOutput fixed highs remaining prepared known ρ) (sampleModel parameterOutput highs)
    (sampleModel_parse parameterOutput highs)
    (sampleModel_incoming parameterOutput highs) tg prepared.2 comp total _
    (inv_start parameterOutput fixed highs remaining prepared known ρ hknown) out hout

include hknown in
/-- A table extending the final exposed coordinates extends the fixed knowledge. -/
theorem knownOf_extending_final (out : Run HashInput Coordinate α × St)
    (hout : out ∈ support (interp tg prepared.2 (sampleModel parameterOutput highs) comp total
      (DebtState.start prepared.2 known)))
    (T : Coordinate → Digest) (hT : tableExtending out.2.known T = T) :
    tableExtending (knownOf (truncateHash parameterOutput) fixed) T = T := by
  have hext := interp_extends tg prepared.2 (sampleModel parameterOutput highs) comp total _ out hout
  have hbase := (exposeR_known _ _ _ hknown).1
  rw [← hT]
  exact tableExtending_of_extends _ _ (fun c v h => hext.2.1 c v (hbase c v h)) T

end Final

end Sphincs.Security.PotentialA
