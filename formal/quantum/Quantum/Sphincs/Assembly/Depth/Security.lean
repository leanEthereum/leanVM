module

public import Quantum.Sphincs.Assembly.Depth.Parallel
public import Quantum.Sphincs.Assembly.Depth.Caps

@[expose] public section

/-!
# leanSPHINCS is quantum SUF-CMA secure against depth-limited adversaries in the QRPM

Parallel's `winProbPar_le_of_cls` with Caps' classical cap for every number of calls
(`uavg_twPR_le_esD`, `clsBoundSD q`): the bound

`sphincsQrpmDepthBound q d = (√(eventTermSphD q d) + √(4 · 10 min d q · 6q kappaSph) +
√readCapS)² + stageCap`,

`eventTermSphD q d = (advAD q d + √(advBD q d² covPS) + √(clsBoundSD q + verLinSD q +
3 verifyBlocks covPS))² + readError + 2^-189 + hConflictCap + 2 goodESCap + 2^-777 + winChgCap +
stageCap`, with `advAD q d = √(24 · 2^-128 min d q · q) + capTermSD q + 3 verifyBlocks √freshKD`
(the `h` rounds at `2^-128`, the `k`, `k'` calls at the capacity rate, the verification's reads)
and `advBD q d = √(24 min d q · q) + 3 verifyBlocks` (the coverage Half event `2^16 price S★`,
averaged to `covPS`). Final theorem: `leanSphincs_qrpm_depth_security`.
-/

open IPFunctor
open scoped ENNReal

open Quantum QuantumRuntime Sphincs Common Common.SufCma
open Quantum.SufCma (serialize isChargeBound_toSeq_perm isChargeBound_toSeq_sign winProbPar
  cmdChargePar signChargePar QuantumStronglyUnforgeablePar)
open Quantum.Xmss (keccakStateEquiv)

namespace Quantum.Sphincs.Assembly

/-- **The depth-aware event term**: Chain's `eventTermSphG` at the depth amplitudes and the
classical cap `clsBoundSD q`. -/
noncomputable def eventTermSphD (q d : ℕ) : ℝ≥0∞ :=
  eventTermSphG (advAD q d) (advBD q d) (clsBoundSD q) (verLinSD q)

/-- **The depth-aware leanSPHINCS QRPM bound**: `(√(eventTermSphD q d) + √(4 · 10 min d q · 6q
kappaSph) + √readCapS)² + stageCap`. -/
noncomputable def sphincsQrpmDepthBound (q d : ℕ) : ℝ≥0∞ :=
  (eventTermSphD q d ^ (2⁻¹ : ℝ) + hybTermSD q d kappaSph readCapS) ^ 2 + stageCap

set_option synthInstance.maxSize 2000 in
/-- **The depth-aware bound for a parallel adversary** of total width `q`, at most `d` rounds
and `signatureLimit` signing requests (Parallel's `winProbPar_le_of_cls` with Caps'
`uavg_twPR_le_esD` on the serialized adversary). -/
theorem winProbPar_le_sphincsQrpmDepthBound (Ap : SAdversaryPar) {q d : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (Ap pk) (cmdChargePar Quantum.SufCma.widthCharge) q)
    (hd : ∀ pk, IFreeM.IsChargeBound (Ap pk) (cmdChargePar Quantum.SufCma.roundCharge) d)
    (hs : ∀ pk, IFreeM.IsChargeBound (Ap pk) (cmdChargePar signChargePar) signatureLimit) :
    winProbPar RandomPermutationModel.sufCmaScheme keccakStateEquiv Ap ≤
      sphincsQrpmDepthBound q d :=
  winProbPar_le_of_cls Ap hq hd hs fun par perm hk hπ ↦
    uavg_twPR_le_esD (fun pk ↦ isChargeBound_toSeq_perm (hq pk))
      (fun pk ↦ isChargeBound_toSeq_sign (hs pk)) par perm hk hπ

/-- **leanSPHINCS is quantum SUF-CMA secure against depth-limited parallel adversaries in the
QRPM** with bound `sphincsQrpmDepthBound q d`: a parallel adversary making at most `q`
permutation calls in at most `d` rounds and at most `signatureLimit` signing requests forges
with probability at most `sphincsQrpmDepthBound q d` (closed form: BoundValue's
`sphincsQrpmDepthBound_le`). -/
theorem leanSphincs_qrpm_depth_security :
    QuantumStronglyUnforgeablePar RandomPermutationModel.sufCmaScheme keccakStateEquiv
      signatureLimit sphincsQrpmDepthBound :=
  fun _ _ Ap hq hd hs ↦ winProbPar_le_sphincsQrpmDepthBound Ap hq hd hs

end Quantum.Sphincs.Assembly

end
