module

public import Quantum.SufCma.Game
public import Quantum.Xmss.Keccak
public import Statement.LeanSphincs

@[expose] public section

/-!
# The quantum SUF-CMA statement of leanSPHINCS in the QRPM

`LeanSphincsQrpmSecurity bound`: the statement's leanSPHINCS over `π`
(`Sphincs.RandomPermutationModel.sufCmaScheme`), its Keccak-f a uniform permutation `φ` of the
sponge state `X × Z` (`keccakStateEquiv`), is strongly unforgeable against quantum adversaries
making at most `q` calls of `φ` and `φ⁻¹` and at most `signatureLimit` signing requests on every
path, with winning probability at most `bound q` (`Quantum.SufCma.QuantumStronglyUnforgeable`,
the statement leanXMSS's `leanXmss_qrpm_security` instantiates).

The bound `sphincsQrpmBound` and the theorem
`leanSphincs_qrpm_security : LeanSphincsQrpmSecurity sphincsQrpmBound` are the security slice's
(`Quantum.Sphincs.Assembly.Security`); neither is defined or claimed here.
-/

open scoped ENNReal

open Quantum.SufCma

namespace Quantum.Sphincs

/-- **leanSPHINCS is quantum SUF-CMA secure in the QRPM with the bound `bound`**: every adversary
making at most `q` permutation calls and at most `signatureLimit` signing requests on every path
forges with probability at most `bound q`. -/
def LeanSphincsQrpmSecurity (bound : ℕ → ℝ≥0∞) : Prop :=
  QuantumStronglyUnforgeable _root_.Sphincs.RandomPermutationModel.sufCmaScheme
    Quantum.Xmss.keccakStateEquiv _root_.Sphincs.signatureLimit bound

end Quantum.Sphincs

end
