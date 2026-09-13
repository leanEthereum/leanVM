import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.AdaptiveResidualErasure
import SphincsSecurity.Proof.Hypertree.CanonicalPublicPrior
import SphincsSecurity.Proof.Reference.ReferenceResidualSeeds
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec UniformTableCompletion ResidualTableCompletion
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

structure ReferenceEncodingAuxiliary where
  selections : ReferenceFamily
  rows : CanonicalEncodingRows

noncomputable def referenceEncodingAuxiliarySample : PMF ReferenceEncodingAuxiliary :=
  (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind (fun selections =>
    (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty selections).map
      (fun rows => ⟨selections, Function.uncurry rows⟩))

theorem referenceAuxiliarySample_bind_seed {Result : Type} (inputs : Finset HashInput)
    (next : ReferenceAuxiliary inputs → SPMF Result) :
    (𝒟[referenceAuxiliarySample inputs] >>= next) =
      (𝒟[referenceEncodingAuxiliarySample] >>= fun encoding =>
        completeRows (fun _ : inputs => none) >>= fun seed => next ⟨encoding.selections, encoding.rows, seed⟩) := by
  rw [completeRows_empty]
  simp only [referenceAuxiliarySample, referenceEncodingAuxiliarySample,
    ← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map, evalDist_bind,
    map_eq_bind_pure_comp, Function.comp_def, evalDist_pure, bind_assoc, pure_bind]

end SphincsSecurity.Concrete
