import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.CanonicalResidualRouting
import SphincsSecurity.Proof.Residual.PublicResidualLookup
namespace SphincsSecurity.Concrete.ResidualByteAction

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

inductive Action (inputs : Finset HashInput) where
  | known (answer : HashOutput)
  | read (input : inputs)
  | probe (input : inputs) (test : Probe CanonicalCoordinate)

def Local {inputs : Finset HashInput} (input : inputs) : Action inputs → Prop
  | .known _ => True
  | .read row => row = input
  | .probe row _ => row = input

noncomputable def eval {inputs : Finset HashInput} (labels : Labels) (seed : inputs → HashOutput) : Action inputs → Option HashOutput
  | .known answer => some answer
  | .read input => some (seed input)
  | .probe input test => if test.keep labels (seed input) then some (seed input) else none

end SphincsSecurity.Concrete.ResidualByteAction
