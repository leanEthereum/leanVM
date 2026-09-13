import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.CanonicalGraphSampling
import SphincsSecurity.Proof.Hypertree.FiniteGraphReplay
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling FiniteGraphSampling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalPayloadInputs canonicalGraphOrder instFintypePosition

noncomputable local instance residualGraphTableSampleable (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)

noncomputable local instance residualGraphLabelsSampleable : SampleableType CanonicalGraphLabels :=
  SampleableType.ofFintype CanonicalGraphLabels

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
  (inputs : Finset HashInput) (hinputs : canonicalGraphInputs parameter ⊆ inputs)

noncomputable def programCanonicalGraph (labels : CanonicalGraphLabels) (residual : inputs → HashOutput) : inputs → HashOutput :=
  patch (fun position => canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs position labels)
    labels residual canonicalGraphOrder

theorem canonicalGraphCell_injective (labels : CanonicalGraphLabels) :
    Function.Injective (fun position => canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs position labels) := by
  intro left right heq
  by_contra hne
  exact canonicalGraphCell_separated parameter otsSecret ftsSecret inputs hinputs left right hne labels labels heq

theorem programCanonicalGraph_at (labels : CanonicalGraphLabels) (residual : inputs → HashOutput) (position : Position) :
    programCanonicalGraph parameter otsSecret ftsSecret inputs hinputs labels residual
      (canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs position labels) = labels position :=
  patch_at _ (canonicalGraphCell_injective parameter otsSecret ftsSecret inputs hinputs labels)
    labels residual canonicalGraphOrder position (mem_canonicalGraphOrder position)

theorem programCanonicalGraph_other (labels : CanonicalGraphLabels) (residual : inputs → HashOutput)
    (input : inputs) (hne : ∀ position, input.val ≠ canonicalGraphInput parameter otsSecret ftsSecret position labels) :
    programCanonicalGraph parameter otsSecret ftsSecret inputs hinputs labels residual input = residual input := by
  apply patch_of_forall_ne
  intro position _ heq
  exact hne position (congrArg Subtype.val heq)

theorem replayCanonicalGraph_eq_patch (labels : CanonicalGraphLabels) (residual : inputs → HashOutput)
    (positions : List Position) (hsorted : positions.Pairwise (fun left right => left.depth ≤ right.depth))
    (before : CanonicalGraphLabels) (hagrees : ∀ position, position ∉ positions → before position = labels position) :
    replay (canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs)
      (fun position output values => Function.update values position output) labels residual positions before =
      (labels, patch (fun position => canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs position labels)
        labels residual positions) := by
  induction positions generalizing before with
  | nil =>
      have hbefore : before = labels := by
        funext position
        exact hagrees position (by simp)
      rw [hbefore]
      rfl
  | cons first rest ih =>
      obtain ⟨hdepth, hsorted⟩ := List.pairwise_cons.mp hsorted
      have hinput : canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs first before =
          canonicalGraphCell parameter otsSecret ftsSecret inputs hinputs first labels := by
        apply Subtype.ext
        apply canonicalGraphInput_congr
        intro child hchild
        apply congrArg truncateHash
        apply hagrees
        intro hmem
        have hlt := Position.depth_lt_of_mem_children hchild
        rcases List.mem_cons.mp hmem with heq | hmem
        · subst child
          omega
        · have := hdepth child hmem
          omega
      have hafter : ∀ position, position ∉ rest →
          Function.update before first (labels first) position = labels position := by
        intro position hposition
        by_cases heq : position = first
        · subst position
          rw [Function.update_self]
        · rw [Function.update_of_ne heq]
          exact hagrees position (fun hmem => (List.mem_cons.mp hmem).elim heq hposition)
      rw [replay, ih hsorted _ hafter, patch, hinput]

theorem evalDist_plantCanonicalGraph_eq_residual :
    𝒟[plantCanonicalGraph parameter otsSecret ftsSecret inputs hinputs] =
      𝒟[do
        let labels ← ($ᵗ CanonicalGraphLabels : ProbComp _)
        let residual ← sampleHashTable inputs
        pure (labels, programCanonicalGraph parameter otsSecret ftsSecret inputs hinputs labels residual)] := by
  rw [plantCanonicalGraph, evalDist_plant_eq_replay _ _ _ canonicalGraphOrder_nodup]
  simp only [sampleHashTable]
  apply evalDist_bind_congr_left
  intro labels
  apply evalDist_bind_congr_left
  intro residual
  rw [replayCanonicalGraph_eq_patch parameter otsSecret ftsSecret inputs hinputs labels residual
    canonicalGraphOrder canonicalGraphOrder_sorted _
    (fun position hposition => (hposition (mem_canonicalGraphOrder position)).elim)]
  rfl

theorem evalDist_plantCanonicalGraph_bind_eq_residual {Result : Type}
    (next : CanonicalGraphLabels → (inputs → HashOutput) → ProbComp Result) :
    𝒟[do let graph ← plantCanonicalGraph parameter otsSecret ftsSecret inputs hinputs; next graph.1 graph.2] =
      𝒟[do
        let labels ← ($ᵗ CanonicalGraphLabels : ProbComp _)
        let residual ← sampleHashTable inputs
        next labels (programCanonicalGraph parameter otsSecret ftsSecret inputs hinputs labels residual)] := by
  have h := congrArg (fun distribution : SPMF (CanonicalGraphLabels × (inputs → HashOutput)) =>
    distribution >>= fun graph => 𝒟[next graph.1 graph.2])
    (evalDist_plantCanonicalGraph_eq_residual parameter otsSecret ftsSecret inputs hinputs)
  simpa only [evalDist_bind, evalDist_pure, bind_assoc, pure_bind] using h

end SphincsSecurity.Concrete
