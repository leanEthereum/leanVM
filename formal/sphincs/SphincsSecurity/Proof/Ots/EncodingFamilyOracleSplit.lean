import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.FirstSuccessFamily
import SphincsSecurity.Proof.Reference.ReferenceOracleConditioning
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

namespace UniformTableSplit

theorem uniform_bind_firstSuccessFamily {Index Cell Answer Value Result : Type}
    [Fintype Index] [DecidableEq Index] [Fintype Cell] [DecidableEq Cell]
    [Fintype Answer] [DecidableEq Answer] [Nonempty Answer] [Fintype Value] {n : Nat}
    (embed : Index × Fin n → Cell) (hinj : Function.Injective embed) (decode : Answer → Option Value)
    (hinvalid : (FirstSuccessTable.invalid decode).Nonempty)
    (next : (Index → Option (Fin n × Value)) → (Cell → Answer) → PMF Result) :
    (PMF.uniformOfFintype (Cell → Answer)).bind (fun table =>
        next (fun index => FirstSuccessTable.select decode (fun counter => table (embed (index, counter)))) table) =
      (FirstSuccessFamily.selected decode n).bind (fun results =>
        (FirstSuccessFamily.afterSelect decode n hinvalid results).bind (fun rows =>
          (PMF.uniformOfFintype (Outside embed → Answer)).bind
            (fun outside => next results (join embed hinj (Function.uncurry rows) outside)))) := by
  rw [uniform_bind_split embed hinj]
  simp only [join_embed]
  have huncurry := PMF.uniformOfFintype_map_of_bijective (Equiv.curry Index (Fin n) Answer).symm
    (Equiv.curry Index (Fin n) Answer).symm.bijective
  rw [← huncurry, PMF.bind_map]
  exact FirstSuccessFamily.uniform_bind_eq_selected decode n hinvalid
    (fun results rows => (PMF.uniformOfFintype (Outside embed → Answer)).bind
      (fun outside => next results (join embed hinj (Function.uncurry rows) outside)))

end UniformTableSplit

abbrev ReferenceFamily := EncodingPosition → ReferenceSelection

noncomputable def referenceFamilyCell (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (row : EncodingRow) : canonicalEncodingInputs parameter :=
  referenceCounterCell parameter row.1 (messages row.1) row.2

theorem referenceFamilyCell_injective (parameter : PublicParameter) (messages : EncodingPosition → Digest) :
    Function.Injective (referenceFamilyCell parameter messages) := by
  rintro ⟨left, first⟩ ⟨right, second⟩ heq
  have hbytes := congrArg Subtype.val heq
  have hposition : left = right := atEncodingPosition_unique
    (show AtEncodingPosition parameter (encodingRetryInput parameter left (messages left) first.val) left from ⟨_, rfl⟩)
    (show AtEncodingPosition parameter (encodingRetryInput parameter left (messages left) first.val) right from ⟨_, hbytes⟩)
  subst right
  exact Prod.ext rfl (referenceCounterCell_injective parameter left (messages left) heq)

noncomputable def referenceFamilyOracleTable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (outside : NonencodingRows key.parameter inputs hencoding)
    (rows : EncodingPosition → Fin encodingAttemptLimit → HashOutput)
    (remaining : UniformTableSplit.Outside
      (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding outside)) → HashOutput) :
    inputs → HashOutput :=
  joinEncodingTable key.parameter inputs hencoding
    (UniformTableSplit.join
      (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding outside))
      (referenceFamilyCell_injective key.parameter (outsideGraphMessage key inputs hencoding outside))
      (Function.uncurry rows) remaining) outside

end SphincsSecurity.Concrete
