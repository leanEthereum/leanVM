import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CanonicalCoordinateSampling
import SphincsSecurity.Proof.Hypertree.CanonicalProbeRouting
import SphincsSecurity.Proof.Residual.RetainedObservation
import SphincsSecurity.Proof.Fts.UniformPublicCoordinates
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting UniformTableCompletion
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

def initiallyExposed (words : OtsReferenceWords) (coordinate : CanonicalCoordinate) : Prop :=
  ¬CanonicalCoordinate.Hidden words (fun _ _ _ => False) coordinate

abbrev InitialPublicLabels (words : OtsReferenceWords) :=
  UniformPublicCoordinates.Public (initiallyExposed words) → Digest

noncomputable def initialKnown (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words) : Labels :=
  fun coordinate => if h : initiallyExposed words coordinate then exposedValues ⟨coordinate, h⟩ else 0

noncomputable def initialAllowed (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words) :
    CanonicalCoordinate → Finset Digest :=
  UniformPublicCoordinates.allowed (initiallyExposed words) exposedValues

theorem initialAllowed_nonempty (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words) :
    ∀ coordinate, (initialAllowed words exposedValues coordinate).Nonempty :=
  UniformPublicCoordinates.allowed_nonempty (initiallyExposed words) exposedValues

theorem initialAllowed_hidden (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words)
    (coordinate : CanonicalCoordinate) (hhidden : CanonicalCoordinate.Hidden words (fun _ _ _ => False) coordinate) :
    initialAllowed words exposedValues coordinate = Finset.univ := by
  unfold initialAllowed UniformPublicCoordinates.allowed
  exact dif_neg (not_not.mpr hhidden)

theorem initialAllowed_public (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words)
    (coordinate : CanonicalCoordinate) (hpublic : initiallyExposed words coordinate) :
    initialAllowed words exposedValues coordinate = {initialKnown words exposedValues coordinate} := by
  simp only [initialAllowed, UniformPublicCoordinates.allowed, initialKnown, dif_pos hpublic]

theorem initialKnown_agrees (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words)
    (labels : Labels) (hlabels : complete (initialAllowed words exposedValues) labels ≠ 0) :
    PublicAgreement words (fun _ _ _ => False) (initialKnown words exposedValues) labels := by
  intro coordinate hpublic
  have hmem := UniformPublicCoordinates.completion_member (initialAllowed words exposedValues) labels hlabels coordinate
  rw [initialAllowed_public words exposedValues coordinate hpublic, Finset.mem_singleton] at hmem
  exact hmem.symm

theorem initialKnown_graphReplies (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words)
    (labels : Labels) (hlabels : complete (initialAllowed words exposedValues) labels ≠ 0)
    (high : CanonicalGraphHighHalves) (position : Position)
    (hpublic : initiallyExposed words (.graph position)) :
    coordinateGraphLabels (initialKnown words exposedValues) high position = coordinateGraphLabels labels high position := by
  unfold coordinateGraphLabels
  rw [initialKnown_agrees words exposedValues labels hlabels (.graph position) hpublic]

theorem sampleSecretGraph_bind_public {Result : Type} (words : OtsReferenceWords)
    (next : InitialPublicLabels words → CanonicalGraphHighHalves →
      (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) →
      (Index → FtsTree → FtsLeaf → Digest) → CanonicalGraphLabels → SPMF Result) :
    (𝒟[sampleOtsSecrets] >>= fun ots => 𝒟[sampleFtsSecrets] >>= fun fts =>
      𝒟[PMF.uniformOfFintype CanonicalGraphLabels] >>= fun graph =>
        next (UniformPublicCoordinates.restrict (initiallyExposed words) (CanonicalCoordinate.value ots fts graph))
          (canonicalGraphHighHalves graph) ots fts graph) =
        (𝒟[PMF.uniformOfFintype CanonicalGraphHighHalves] >>= fun high =>
          𝒟[PMF.uniformOfFintype (InitialPublicLabels words)] >>= fun exposedValues =>
            complete (initialAllowed words exposedValues) >>= fun labels =>
              next exposedValues high (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) (coordinateGraphLabels labels high)) := by
  rw [sampleSecretGraph_bind_coordinates]
  simp only [coordinateGraphLabels_value, coordinateGraphLabels_high]
  rw [RetainedObservation.bind_comm]
  apply congrArg (𝒟[PMF.uniformOfFintype CanonicalGraphHighHalves] >>= ·)
  funext high
  exact UniformPublicCoordinates.uniform_bind_complete (initiallyExposed words)
    (fun exposedValues labels => next exposedValues high (coordinateOtsSecrets labels) (coordinateFtsSecrets labels)
      (coordinateGraphLabels labels high))

end SphincsSecurity.Concrete
