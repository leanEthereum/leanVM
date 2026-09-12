import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.MessageByteTrace
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs publicDigestLoop
set_option backward.isDefEq.respectTransparency false

theorem messageOnly_map {A B : Type} (parameter : PublicParameter) (f : A → B)
    (computation : OracleComp OracleWorld A) (hmessage : MessageOnly parameter computation) :
    MessageOnly parameter (f <$> computation) := by
  rw [map_eq_bind_pure_comp]
  exact messageOnly_bind parameter computation (pure ∘ f) hmessage (fun value => messageOnly_pure parameter (f value))

theorem hashInputs_map {A B : Type} (f : A → B) (computation : OracleComp OracleWorld A) :
    hashInputs (f <$> computation) = hashInputs computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [map_pure, hashInputs_pure]
  | query_bind input next ih =>
      simp only [map_bind, hashInputs_query_bind, ih]
      cases input <;> rfl

theorem hashInputs_boundary {Result : Type} (parameter : PublicParameter) (computation : OracleComp OracleWorld Result) :
    hashInputs (boundaryComputation parameter computation) = hashInputs computation := by
  rw [← hashInputs_map Prod.fst, boundaryComputation_fst]

theorem hashInputs_bind_pure_next {A B : Type} (first : OracleComp OracleWorld A) (next : A → OracleComp OracleWorld B)
    (hpure : ∀ value, ∃ output, next value = pure output) : hashInputs (first >>= next) = hashInputs first := by
  induction first using OracleComp.inductionOn with
  | pure value =>
      obtain ⟨output, heq⟩ := hpure value
      simp only [pure_bind, heq, hashInputs_pure]
  | query_bind input tail ih =>
      simp only [bind_assoc, hashInputs_query_bind, ih]
      cases input <;> rfl

theorem hashInputs_left_subset {A B : Type} (first : OracleComp OracleWorld A) (next : A → OracleComp OracleWorld B) :
    hashInputs first ⊆ hashInputs (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simp only [hashInputs_pure, Finset.empty_subset]
  | query_bind input tail ih =>
      intro row hrow
      rw [hashInputs_query_bind, Finset.mem_union] at hrow
      rw [bind_assoc, hashInputs_query_bind, Finset.mem_union]
      rcases hrow with hhead | htail
      · cases input <;> exact Or.inl hhead
      · obtain ⟨answer, _, hrow⟩ := Finset.mem_biUnion.mp htail
        exact Or.inr (Finset.mem_biUnion.mpr ⟨answer, Finset.mem_univ _, ih answer hrow⟩)

theorem boundaryComputation_query_bind {Result : Type} (parameter : PublicParameter)
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp OracleWorld Result) :
    boundaryComputation parameter (liftM (OracleWorld.query input) >>= next) =
      liftM (OracleWorld.query input) >>= fun answer =>
        (fun result => (result.1, signingBoundaryTrace parameter input answer * result.2)) <$>
          boundaryComputation parameter (next answer) := by
  simp [boundaryComputation, QueryImpl.withTrace_apply]

theorem fixedBoundaryRun_boundaryComputation {Result : Type} (parameter : PublicParameter)
    (oracle : QueryImpl HashSpec Id) (computation : OracleComp OracleWorld Result) :
    fixedBoundaryRun parameter oracle (boundaryComputation parameter computation) =
      (fun result => (result, result.2)) <$> fixedBoundaryRun parameter oracle computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [boundaryComputation_query_bind, fixedBoundaryRun_query_bind,
        fixedBoundaryRun_query_bind, map_bind]
      apply bind_congr
      intro answer
      simp only [fixedBoundaryRun_map, ih, Functor.map_map, Prod.map_apply, id_eq]

theorem messageOnly_boundary {Result : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld Result) (hmessage : MessageOnly parameter computation) :
    MessageOnly parameter (boundaryComputation parameter computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact messageOnly_pure parameter (value, 1)
  | query_bind input next ih =>
      rw [boundaryComputation_query_bind]
      apply messageOnly_query_bind parameter input _
      · cases input with
        | inl _ => trivial
        | inr input => exact hmessage input (mem_hashInputs_hash_bind input next)
      · intro answer
        exact messageOnly_map parameter _ _ (ih answer
          (fun row hrow => hmessage row ((hashInputs_next_subset input next answer) hrow)))

theorem messageOnly_publicSignAttempt (parameter : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness) :
    MessageOnly parameter (liftM (publicSignAttempt parameter root message randomness)) := by
  simp only [publicSignAttempt, messageDigest, bind_assoc, pure_bind, liftM_bind]
  apply messageOnly_query_bind parameter (.inr (tweakableHashInput parameter .message (messageDigestPayload root message randomness))) _
  · exact ⟨_, rfl⟩
  · intro answer
    split <;> exact messageOnly_pure parameter _

theorem messageOnly_publicDigestLoop (parameter : PublicParameter) (root : Digest) (message : Message) (attempts : Nat) :
    MessageOnly parameter (publicDigestLoop parameter root message attempts) := by
  induction attempts with
  | zero => rw [publicDigestLoop]; exact messageOnly_pure parameter none
  | succ attempts ih =>
      rw [publicDigestLoop]
      apply messageOnly_bind parameter _ _ (messageOnly_lift_prob parameter sampleRandomness)
      intro randomness
      apply messageOnly_bind parameter _ _ (messageOnly_publicSignAttempt parameter root message randomness)
      intro attempt
      cases attempt with
      | none => exact ih
      | some selected => exact messageOnly_pure parameter _

noncomputable def publicSigningWork (parameter : PublicParameter) (root : Digest) (known : Labels)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    OracleComp OracleWorld (PublicSigningRecord × Nat) := do
  let selected ← boundaryComputation parameter (publicDigestLoop parameter root message digestAttemptLimit)
  match selected.1 with
  | none => pure (((none, none), selected.2), 0)
  | some (randomness, index, leaves) =>
      let plan := publicSignPlan known words selections randomness index leaves
      pure (((plan.1, some (selectedFewTimeView index leaves)), selected.2 * (FreeMonoid.of none) ^ plan.2), plan.2)

theorem publicSigningWork_messageOnly (parameter : PublicParameter) (root : Digest) (known : Labels)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    MessageOnly parameter (publicSigningWork parameter root known words selections message) := by
  rw [publicSigningWork]
  apply messageOnly_bind parameter _ _ (messageOnly_boundary parameter _
    (messageOnly_publicDigestLoop parameter root message digestAttemptLimit))
  rintro ⟨selected, trace⟩
  cases selected <;> exact messageOnly_pure parameter _

theorem hashInputs_publicSigningWork (parameter : PublicParameter) (root : Digest) (known : Labels)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    hashInputs (publicSigningWork parameter root known words selections message) =
      hashInputs (publicDigestLoop parameter root message digestAttemptLimit) := by
  rw [publicSigningWork, hashInputs_bind_pure_next, hashInputs_boundary]
  rintro ⟨selected, trace⟩
  cases selected <;> exact ⟨_, rfl⟩

theorem hashInputs_publicSigningWork_subset_signWithView (key : SecretKey) (known : Labels)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    hashInputs (publicSigningWork key.parameter key.root known words selections message) ⊆ hashInputs (signWithView key message) := by
  rw [hashInputs_publicSigningWork, publicDigestLoop_eq, signWithView]
  exact hashInputs_left_subset _ _

def accountWork (memory : ExternalMemory) (cost : Nat) : ExternalMemory :=
  { memory with hashCalls := memory.hashCalls + cost }

theorem applyBoundary_pow_none (memory : ExternalMemory) (cost : Nat) :
    applyBoundary memory ((FreeMonoid.of none : SigningBoundaryTrace) ^ cost) = accountWork memory cost := by
  simp only [applyBoundary, SigningBoundaryTrace.messageCalls_pow_none, SigningBoundaryTrace.hashCalls_pow_none, List.foldl_nil]
  rfl

end SphincsSecurity.Concrete.ResidualByteFrontend
