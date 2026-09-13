import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.PrefixByteRun
import SphincsSecurity.Proof.Reference.ReferenceJointPrior
import SphincsSecurity.Proof.Reference.ReferenceAuxiliarySigning
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs
set_option backward.isDefEq.respectTransparency false

def MessageOnly {Result : Type} (parameter : PublicParameter) (computation : OracleComp OracleWorld Result) : Prop :=
  ∀ input ∈ hashInputs computation, FtsProbeSimulation.MessageHashInput parameter input

theorem messageOnly_pure {Result : Type} (parameter : PublicParameter) (value : Result) :
    MessageOnly parameter (pure value) := by
  intro input hinput
  simp only [hashInputs_pure, Finset.notMem_empty] at hinput

theorem messageOnly_query_bind {Result : Type} (parameter : PublicParameter) (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld Result)
    (hhead : match input with | .inl _ => True | .inr input => FtsProbeSimulation.MessageHashInput parameter input)
    (htail : ∀ answer, MessageOnly parameter (next answer)) :
    MessageOnly parameter (liftM (OracleWorld.query input) >>= next) := by
  intro row hrow
  rw [hashInputs_query_bind, Finset.mem_union] at hrow
  rcases hrow with hheadRow | htailRow
  · cases input with
    | inl _ => simp only [Finset.notMem_empty] at hheadRow
    | inr input =>
        obtain rfl := Finset.mem_singleton.mp hheadRow
        exact hhead
  · obtain ⟨answer, _, hrow⟩ := Finset.mem_biUnion.mp htailRow
    exact htail answer row hrow

theorem messageOnly_bind {A B : Type} (parameter : PublicParameter) (first : OracleComp OracleWorld A)
    (next : A → OracleComp OracleWorld B) (hfirst : MessageOnly parameter first)
    (hnext : ∀ answer, MessageOnly parameter (next answer)) : MessageOnly parameter (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using hnext value
  | query_bind input tail ih =>
      rw [bind_assoc]
      apply messageOnly_query_bind parameter input _
      · cases input with
        | inl _ => trivial
        | inr input => exact hfirst input (mem_hashInputs_hash_bind input tail)
      · intro answer
        exact ih answer (fun row hrow => hfirst row ((hashInputs_next_subset input tail answer) hrow))

theorem messageOnly_lift_prob {Result : Type} (parameter : PublicParameter) (computation : ProbComp Result) :
    MessageOnly parameter (liftM computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rw [liftM_pure]; exact messageOnly_pure parameter value
  | query_bind input next ih =>
      rw [liftM_bind]
      exact messageOnly_query_bind parameter (.inl input) _ trivial ih

noncomputable def applyBoundary (memory : ExternalMemory) (trace : SigningBoundaryTrace) : ExternalMemory :=
  ⟨trace.messageCalls.foldl (fun cache entry => Function.update cache entry.1 (some entry.2)) memory.cache,
    memory.hashCalls + trace.hashCalls, memory.probes⟩

theorem applyBoundary_one (memory : ExternalMemory) : applyBoundary memory 1 = memory := by
  cases memory
  rfl

theorem applyBoundary_mul (memory : ExternalMemory) (left right : SigningBoundaryTrace) :
    applyBoundary memory (left * right) = applyBoundary (applyBoundary memory left) right := by
  simp only [applyBoundary, SigningBoundaryTrace.messageCalls_mul, SigningBoundaryTrace.hashCalls_mul,
    List.foldl_append, Nat.add_assoc]

noncomputable def messageStep (oracle : QueryImpl HashSpec Id) (input : HashInput) (memory : ExternalMemory) :
    Option HashOutput × ExternalMemory :=
  (some (oracle input), storeReply { memory with hashCalls := memory.hashCalls + 1 } input (oracle input))

theorem fixedBoundaryRun_query_bind {Result : Type} (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp OracleWorld Result) :
    fixedBoundaryRun parameter oracle (liftM (OracleWorld.query input) >>= next) =
      fixedHashWorld oracle input >>= fun answer =>
        (fun result => (result.1, signingBoundaryTrace parameter input answer * result.2)) <$>
          fixedBoundaryRun parameter oracle (next answer) := by
  simp [fixedBoundaryRun, QueryImpl.withTrace_apply]

theorem message_not_encoding (parameter : PublicParameter) (input : HashInput)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (position : EncodingPosition) :
    ¬AtEncodingPosition parameter input position := by
  obtain ⟨payload, rfl⟩ := hmessage
  rintro ⟨other, heq⟩
  have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).1
  simp only [EncodingPosition.domain, reduceCtorEq] at hdomain

theorem checkedFixedStep_message (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (oracle : QueryImpl HashSpec Id) (input : HashInput)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (memory : ExternalMemory) :
    checkedResult (PublicEncodingMatch.Match parameter messages words selections) input
      (fixedStep parameter words disclosed known actual oracle input memory) = messageStep oracle input memory := by
  have hdecode : decodePosition parameter input = none := by
    obtain ⟨payload, rfl⟩ := hmessage
    exact decodePosition_message parameter payload
  have hbad : ¬CanonicalProbeRouting.Bad parameter words disclosed actual input (oracle input) := by
    rintro ⟨position, hat, _⟩
    exact (decodePosition_none_iff parameter input).mp hdecode position hat
  have hmatch : ¬PublicEncodingMatch.Match parameter messages words selections input (oracle input) := by
    rintro ⟨position, hat, _⟩
    exact message_not_encoding parameter input hmessage position hat
  simp only [checkedResult, fixedStep, fixedAnswer, if_neg hbad, Option.bind_some, if_neg hmatch,
    Option.elim_some, messageStep, charge, route, hdecode, Option.elim_none]
  cases memory.cache input <;> simp only [Nat.add_zero]

end SphincsSecurity.Concrete.ResidualByteFrontend
