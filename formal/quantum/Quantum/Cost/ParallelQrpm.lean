module

public import Quantum.Cost.Parallel
public import Quantum.Xmss.Assembly.Depth.Security

@[expose] public section

/-!
# Gate-and-depth security of leanXMSS in the QRPM

Parallel's transfer `Qrpm.gateDepthSecure_of` applied to leanXMSS's depth-aware QRPM theorem
(`Xmss.Assembly.leanXmss_qrpm_depth_security`): a parallel gate-set adversary within `G` gates
(`GK` per call of the permutation `φ` or `φ⁻¹`, that is per Keccak-f[1600] query, not per sponge
evaluation of Keccak-256) and depth charge `MD` (`DK` per round) forges with probability at most
`qrpmDepthBound (G / GK) (MD / DK)`.

The closed form (`leanXmss_qrpm_gateDepth_closed`) holds for at most `2^84` permutation calls,
`G / GK ≤ 2^84`, the range of `Xmss.Assembly.qrpmDepthBound_le`; that hypothesis is explicit.
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.Cost.Qrpm

open LeanXmss HashSig

/-- A parallel gate-set adversary against leanXMSS in the QRPM. -/
abbrev XmssParGateAdversary (Γ : GateSet) :=
  ParGateAdversary Γ PublicKey SigningRequest (Option Signature) Forgery (Xmss.X × Xmss.Z)

/-- **leanXMSS in the QRPM, in gates and depth**: within `G` gates (`GK` per permutation call),
depth charge `MD` (`DK` per round) and `lifetime` signing requests, forging succeeds with
probability at most `qrpmDepthBound (G / GK) (MD / DK)`. -/
theorem leanXmss_qrpm_gateDepth {GK DK : ℕ} (hGK : 0 < GK) (hDK : 0 < DK) :
    GateDepthSecure RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv lifetime GK DK
      Xmss.Assembly.qrpmDepthBound :=
  gateDepthSecure_of hGK hDK Xmss.Assembly.leanXmss_qrpm_depth_security

/-- **leanXMSS in the QRPM, in gates and depth, closed form**: with `q = G / GK ≤ 2^84`
permutation calls and `d = MD / DK`, forging succeeds with probability at most
`((20.4 √(q · min d q) + 11 q / 2^28 + 21 · 2^14 √q + 75 · 2^30) / 2^64)²`. -/
theorem leanXmss_qrpm_gateDepth_closed {GK DK : ℕ} (hGK : 0 < GK) (hDK : 0 < DK)
    (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ) (G MD : ℕ) (A : XmssParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk) (gateCharge Γ (permGatesPar GK)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk) (opCharge δ (permDepthPar DK)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) lifetime)
    (hq : G / GK ≤ 2 ^ 84) :
    Quantum.SufCma.winProbPar RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
        A.toAdversary ≤
      ENNReal.ofReal (((102 / 5 * √(((G / GK : ℕ) : ℝ) * (min (MD / DK) (G / GK) : ℕ)) +
        11 * ((G / GK : ℕ) : ℝ) / 2 ^ 28 + 21 * 2 ^ 14 * √((G / GK : ℕ) : ℝ) + 75 * 2 ^ 30) /
          2 ^ 64) ^ 2) :=
  (leanXmss_qrpm_gateDepth hGK hDK Γ δ G MD A hG hD hS).trans
    (Xmss.Assembly.qrpmDepthBound_le hq)

end Quantum.Cost.Qrpm

end
