import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.CanonicalGraphResidual
import SphincsSecurity.Proof.Hypertree.CanonicalProbeRouting
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling CanonicalProbeRouting
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalPayloadInputs canonicalGraphOrder instFintypePosition

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

noncomputable local instance residualQueryTableSampleable (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)

noncomputable def programmedHash (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id) : QueryImpl HashSpec Id :=
  fun input => (decodePosition parameter input).elim (residual input) fun position =>
    if input = canonicalGraphInput parameter otsSecret ftsSecret position labels then labels position else residual input

theorem canonicalGraphInput_at (position : Position) (labels : CanonicalGraphLabels) :
    AtPosition parameter (canonicalGraphInput parameter otsSecret ftsSecret position labels) position := ⟨_, rfl⟩

theorem programmedHash_at (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id) (position : Position) :
    programmedHash parameter otsSecret ftsSecret labels residual
      (canonicalGraphInput parameter otsSecret ftsSecret position labels) = labels position := by
  simp only [programmedHash, (decodePosition_some_iff _ _ _).mpr
    (canonicalGraphInput_at parameter otsSecret ftsSecret position labels), Option.elim_some, if_true]

theorem programmedHash_other (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id) (input : HashInput)
    (hne : ∀ position, input ≠ canonicalGraphInput parameter otsSecret ftsSecret position labels) :
    programmedHash parameter otsSecret ftsSecret labels residual input = residual input := by
  rw [programmedHash]
  cases hdecode : decodePosition parameter input with
  | none => rfl
  | some position => simp only [Option.elim_some, if_neg (hne position)]

theorem canonicalGraphLabels_programmedHash (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id) :
    canonicalGraphLabels parameter otsSecret ftsSecret (programmedHash parameter otsSecret ftsSecret labels residual) = labels := by
  funext position
  induction hdepth : position.depth using Nat.strong_induction_on generalizing position with
  | h depth ih =>
      rw [canonicalGraphLabels_consistent]
      calc
        _ = programmedHash parameter otsSecret ftsSecret labels residual
            (canonicalGraphInput parameter otsSecret ftsSecret position labels) := by
          apply congrArg (programmedHash parameter otsSecret ftsSecret labels residual)
          apply canonicalGraphInput_congr
          intro child hchild
          apply congrArg truncateHash
          have hlt : child.depth < depth := by
            rw [← hdepth]
            exact Position.depth_lt_of_mem_children hchild
          exact ih child.depth hlt child rfl
        _ = labels position := programmedHash_at parameter otsSecret ftsSecret labels residual position

theorem noncanonical_at (labels : CanonicalGraphLabels) (input : HashInput) (position : Position)
    (hat : AtPosition parameter input position)
    (hne : input ≠ canonicalGraphInput parameter otsSecret ftsSecret position labels) :
    ∀ other, input ≠ canonicalGraphInput parameter otsSecret ftsSecret other labels := by
  intro other heq
  have hother : AtPosition parameter input other := ⟨_, heq⟩
  have hposition := atPosition_unique parameter hat hother
  subst other
  exact hne heq

variable (inputs : Finset HashInput) (hinputs : canonicalGraphInputs parameter ⊆ inputs)

theorem finiteHashAnswer_program_at (labels : CanonicalGraphLabels) (residual : inputs → HashOutput) (position : Position) :
    finiteHashAnswer ∅ inputs (programCanonicalGraph parameter otsSecret ftsSecret inputs hinputs labels residual)
      (canonicalGraphInput parameter otsSecret ftsSecret position labels) = labels position := by
  rw [finiteHashAnswer_none _ _ _ _ (hinputs (canonicalGraphInput_mem parameter otsSecret ftsSecret position labels)) (by simp)]
  exact programCanonicalGraph_at parameter otsSecret ftsSecret inputs hinputs labels residual position

theorem finiteHashAnswer_program_other (labels : CanonicalGraphLabels) (residual : inputs → HashOutput) (input : HashInput)
    (hne : ∀ position, input ≠ canonicalGraphInput parameter otsSecret ftsSecret position labels) :
    finiteHashAnswer ∅ inputs (programCanonicalGraph parameter otsSecret ftsSecret inputs hinputs labels residual) input =
      finiteHashAnswer ∅ inputs residual input := by
  by_cases hin : input ∈ inputs
  · rw [finiteHashAnswer_none _ _ _ _ hin (by simp), finiteHashAnswer_none _ _ _ _ hin (by simp)]
    exact programCanonicalGraph_other parameter otsSecret ftsSecret inputs hinputs labels residual ⟨input, hin⟩ hne
  · simp only [finiteHashAnswer, QueryCache.empty_apply, Option.getD_none, dif_neg hin]

theorem finiteHashAnswer_program_eq (labels : CanonicalGraphLabels) (residual : inputs → HashOutput) :
    finiteHashAnswer ∅ inputs (programCanonicalGraph parameter otsSecret ftsSecret inputs hinputs labels residual) =
      programmedHash parameter otsSecret ftsSecret labels (finiteHashAnswer ∅ inputs residual) := by
  funext input
  by_cases hcanonical : ∃ position, input = canonicalGraphInput parameter otsSecret ftsSecret position labels
  · obtain ⟨position, rfl⟩ := hcanonical
    rw [finiteHashAnswer_program_at, programmedHash_at]
  · have hne : ∀ position, input ≠ canonicalGraphInput parameter otsSecret ftsSecret position labels :=
      fun position heq => hcanonical ⟨position, heq⟩
    rw [finiteHashAnswer_program_other parameter otsSecret ftsSecret inputs hinputs labels residual input hne,
      programmedHash_other parameter otsSecret ftsSecret labels _ input hne]

end SphincsSecurity.Concrete
