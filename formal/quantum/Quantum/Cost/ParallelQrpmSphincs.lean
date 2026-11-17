module

public import Quantum.Cost.Parallel
public import Quantum.Sphincs.Assembly.Depth.Security
public import Quantum.Sphincs.Assembly.Depth.BoundValue

@[expose] public section

/-!
# Gate-and-depth security of leanSPHINCS in the QRPM

Parallel's transfer `Qrpm.gateDepthSecure_of` applied to leanSPHINCS's depth-aware QRPM theorem
(`Sphincs.Assembly.leanSphincs_qrpm_depth_security`): a parallel gate-set adversary within `G`
gates (`GK` per call of the permutation `φ` or `φ⁻¹`, that is per Keccak-f[1600] query) and depth
charge `MD` (`DK` per round) forges with probability at most
`sphincsQrpmDepthBound (G / GK) (MD / DK)`.

The closed form (`leanSphincs_qrpm_gateDepth_closed`) holds for at most `2^88` permutation calls,
`G / GK ≤ 2^88`, the range of `Sphincs.Assembly.sphincsQrpmDepthBound_le`; that hypothesis is
explicit.
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.Cost.Qrpm

open _root_.Sphincs

/-- A parallel gate-set adversary against leanSPHINCS in the QRPM. -/
abbrev SphincsParGateAdversary (Γ : GateSet) :=
  ParGateAdversary Γ PublicKey HashSig.Message (Option Signature) Forgery (Xmss.X × Xmss.Z)

/-- **leanSPHINCS in the QRPM, in gates and depth**: within `G` gates (`GK` per permutation
call), depth charge `MD` (`DK` per round) and `signatureLimit` signing requests, forging succeeds
with probability at most `sphincsQrpmDepthBound (G / GK) (MD / DK)`. -/
theorem leanSphincs_qrpm_gateDepth {GK DK : ℕ} (hGK : 0 < GK) (hDK : 0 < DK) :
    GateDepthSecure RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv signatureLimit GK
      DK Sphincs.Assembly.sphincsQrpmDepthBound :=
  gateDepthSecure_of hGK hDK Sphincs.Assembly.leanSphincs_qrpm_depth_security

/-- **leanSPHINCS in the QRPM, in gates and depth, closed form**: with `q = G / GK ≤ 2^88`
permutation calls and `d = MD / DK`, forging succeeds with probability at most
`((1566 √(q · min d q) + q / 2^25 + 641 √q + 57 · 2^30) / 2^64)²`. -/
theorem leanSphincs_qrpm_gateDepth_closed {GK DK : ℕ} (hGK : 0 < GK) (hDK : 0 < DK)
    (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ) (G MD : ℕ) (A : SphincsParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk) (gateCharge Γ (permGatesPar GK)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk) (opCharge δ (permDepthPar DK)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) signatureLimit)
    (hq : G / GK ≤ 2 ^ 88) :
    Quantum.SufCma.winProbPar RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
        A.toAdversary ≤
      ENNReal.ofReal (((1566 * √(((G / GK : ℕ) : ℝ) * (min (MD / DK) (G / GK) : ℕ)) +
        ((G / GK : ℕ) : ℝ) / 2 ^ 25 + 641 * √((G / GK : ℕ) : ℝ) + 57 * 2 ^ 30) / 2 ^ 64) ^ 2) :=
  (leanSphincs_qrpm_gateDepth hGK hDK Γ δ G MD A hG hD hS).trans
    (Sphincs.Assembly.sphincsQrpmDepthBound_le hq)

end Quantum.Cost.Qrpm

end
