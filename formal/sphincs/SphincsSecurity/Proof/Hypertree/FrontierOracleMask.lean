import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.FrontierSignerErasure
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def PrivateOtsPrefixInput (parameter : PublicParameter) (words : OtsReferenceWords) (input : HashInput) : Prop :=
  ∃ lay tree leaf chainIdx step,
    step.val < (words lay tree leaf chainIdx).val ∧
      AtPosition parameter input (.chain lay tree leaf chainIdx step)

theorem privateOtsPrefixInput_chain_iff (parameter : PublicParameter) (words : OtsReferenceWords)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
    (payload : HashInput) :
    PrivateOtsPrefixInput parameter words
        (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload) ↔
      step.val < (words lay tree leaf chainIdx).val := by
  constructor
  · rintro ⟨otherLay, otherTree, otherLeaf, otherChain, otherStep, hlt, hat⟩
    have heq := atPosition_unique parameter
      (show AtPosition parameter (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload)
        (.chain lay tree leaf chainIdx step) from ⟨payload, rfl⟩) hat
    simp only [Position.chain.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
    exact hlt
  · intro hlt
    exact ⟨lay, tree, leaf, chainIdx, step, hlt, payload, rfl⟩

theorem not_privateOtsPrefixInput_of_tag (parameter : PublicParameter) (words : OtsReferenceWords)
    (domain : HashDomain) (htag : (hashDomainFields domain).tag ≠ 1#8) (payload : HashInput) :
    ¬ PrivateOtsPrefixInput parameter words (tweakableHashInput parameter domain payload) := by
  rintro ⟨lay, tree, leaf, chainIdx, step, _, prefixPayload, heq⟩
  exact htag (FtsProbeSimulation.tweakableHashInput_tag_eq parameter domain
    (.chain lay tree leaf chainIdx step) payload prefixPayload heq)

def AgreeOutsideOtsPrefixes (parameter : PublicParameter) (words : OtsReferenceWords)
    (f g : QueryImpl HashSpec Id) : Prop :=
  ∀ input, ¬ PrivateOtsPrefixInput parameter words input → f input = g input

theorem AgreeOutsideOtsPrefixes.chain {parameter : PublicParameter} {words : OtsReferenceWords}
    {f g : QueryImpl HashSpec Id} (h : AgreeOutsideOtsPrefixes parameter words f g)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
    (hstep : (words lay tree leaf chainIdx).val ≤ step.val) (payload : HashInput) :
    f (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload) =
      g (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload) := by
  apply h
  rw [privateOtsPrefixInput_chain_iff]
  exact not_lt_of_ge hstep

theorem AgreeOutsideOtsPrefixes.other {parameter : PublicParameter} {words : OtsReferenceWords}
    {f g : QueryImpl HashSpec Id} (h : AgreeOutsideOtsPrefixes parameter words f g)
    (domain : HashDomain) (htag : (hashDomainFields domain).tag ≠ 1#8) (payload : HashInput) :
    f (tweakableHashInput parameter domain payload) = g (tweakableHashInput parameter domain payload) :=
  h _ (not_privateOtsPrefixInput_of_tag parameter words domain htag payload)

noncomputable def maskOtsPrefixes (parameter : PublicParameter) (words : OtsReferenceWords)
    (f : QueryImpl HashSpec Id) : QueryImpl HashSpec Id :=
  fun input => if PrivateOtsPrefixInput parameter words input then 0 else f input

theorem maskOtsPrefixes_agrees (parameter : PublicParameter) (words : OtsReferenceWords)
    (f : QueryImpl HashSpec Id) : AgreeOutsideOtsPrefixes parameter words f (maskOtsPrefixes parameter words f) := by
  intro input hinput
  simp only [maskOtsPrefixes, if_neg hinput]

theorem maskOtsPrefixes_congr {parameter : PublicParameter} {words : OtsReferenceWords}
    {f g : QueryImpl HashSpec Id} (h : AgreeOutsideOtsPrefixes parameter words f g) :
    maskOtsPrefixes parameter words f = maskOtsPrefixes parameter words g := by
  funext input
  by_cases hinput : PrivateOtsPrefixInput parameter words input
  · simp only [maskOtsPrefixes, if_pos hinput]
  · simp only [maskOtsPrefixes, if_neg hinput, h input hinput]

end SphincsSecurity.Concrete
