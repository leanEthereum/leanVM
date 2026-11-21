module

public import Quantum.Cost.Parallel
public import Quantum.Qrom.Sphincs.DepthSecurity

@[expose] public section

/-!
# Gate-and-depth security of leanSPHINCS in the QROM

Parallel's transfer `Qrom.gateDepthSecure_of` applied to leanSPHINCS's depth-aware QROM theorem
(`leanSphincs_qrom_depth_security`) and its closed form (`leanSphincs_qrom_depth_security_closed`):
a parallel gate-set adversary within `G` gates (`GK` per call of `H`) and depth charge `MD` (`DK`
per round) forges with probability at most the bound at `G / GK` calls in `MD / DK` rounds.
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.Cost.Qrom

open Quantum.Qrom

/-- **leanSPHINCS in the QROM, in gates and depth**: within `G` gates (`GK` per call of `H`),
depth charge `MD` (`DK` per round) and `signatureLimit` signing requests, forging succeeds with
probability at most `sphincsQromDepthBound (G / GK) (MD / DK)`. -/
theorem leanSphincs_qrom_gateDepth {GK DK : ℕ} (hGK : 0 < GK) (hDK : 0 < DK) :
    GateDepthSecure Sphincs.sphincsRom _root_.Sphincs.signatureLimit GK DK
      Sphincs.sphincsQromDepthBound :=
  gateDepthSecure_of hGK hDK Sphincs.leanSphincs_qrom_depth_security

/-- **leanSPHINCS in the QROM, in gates and depth, closed form**: with `q = G / GK` and
`d = MD / DK`, forging succeeds with probability at most
`((5.86 √(q · min d q) + 2^-55 q + 257.3 √q + 1.818 · 2^32) / 2^64)²`, for every `G` and `MD`. -/
theorem leanSphincs_qrom_gateDepth_closed {GK DK : ℕ} (hGK : 0 < GK) (hDK : 0 < DK) :
    GateDepthSecure Sphincs.sphincsRom _root_.Sphincs.signatureLimit GK DK fun q d ↦
      ENNReal.ofReal (((5.86 * √((q : ℝ) * (min d q : ℕ)) + (2 ^ 55)⁻¹ * q +
        257.3 * √(q : ℝ) + 1.818 * 2 ^ 32) / 2 ^ 64) ^ 2) :=
  gateDepthSecure_of hGK hDK Sphincs.leanSphincs_qrom_depth_security_closed

end Quantum.Cost.Qrom

end
