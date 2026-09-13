import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.ReferencePrefixSigning
import SphincsSecurity.Proof.Residual.ResidualSigningDisclosure
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting ResidualByteAction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def jointSigningProgram (inputs : Finset HashInput) (parameter : PublicParameter) (root : Digest)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    OracleComp (World inputs) ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) := do
  let work ← simulateQ (checkedTranslate inputs (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections))
    (publicSigningWork parameter root known words selections message)
  jointCompleteSigningWork work

end SphincsSecurity.Concrete.ResidualByteFrontend
