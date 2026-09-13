import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateTerminalGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def proposalPrefixStop : CertificateStopRule :=
  fun input state length record => decide (
    targetProposalOverhead * (state.2.log ++ signingLogFragment input record.output).length + 131072 <
      ((state.2.proposals + length : Nat) : ENNReal))

end SphincsSecurity.Concrete
