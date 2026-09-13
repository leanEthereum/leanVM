import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.CheckedByteExecution
import SphincsSecurity.Proof.Ots.PrefixByteAction
import SphincsSecurity.Proof.Ots.PublicEncodingMatch
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev prefixEnvironment (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) :=
  environment parameter inputs words disclosed known
    (freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows)

end SphincsSecurity.Concrete.ResidualByteFrontend
