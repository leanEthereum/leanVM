module

public import Quantum.Qrom.Xmss.DepthEnd

@[expose] public section

/-!
# leanXMSS is quantum SUF-CMA secure in the QROM against parallel adversaries

The assembly of Security's chain for a parallel adversary `A` (`SufCma.AdversaryPar`) making at
most `q` calls of `H` in at most `d` rounds. Its game is the game of its serialization
(`SufCma.winProbPar_eq`), and every step of the sequential chain runs on the serialized adversary
except two, which run on the game with rounds (`gameQPar`, `gameQ_serialize`):

0. **No leaf reuse** (NoReuse's `winProb_le_winProb_refuse`): the serialization of `refusePar A`
   refuses reused leaves (`refuse_serialize`), with the same budgets
   (`isChargeBound_refuseFromPar`).
1. **The hybrid with rounds** (DepthHybrid's `winProb_le_hybrid_depth`):
   `winProb ≤ (√(E p2Q) + hybTermQD q d)²`, `hybTermQD q d = 2√(q · min d q)·2^-64 + √(v·2^-128)`.
2. **The event with rounds** (DepthEnd's `uavg_p2Q_le_of` at `ewPrefixQD_le`):
   `E p2Q ≤ (advTermQD q d + verTermQ + √(clsBoundQ q + verLinQ))² + readErrQ`,
   `advTermQD q d = √(6 · 2^-128 · min d q · q)`.
3. **The prefix's classical costs** (Costs' `uavg_twPQ_le` on the serialized adversary):
   `clsBoundQ q`, unchanged.

`xmssQromDepthBound q d = (√eventTermQD q d + hybTermQD q d)²` with
`eventTermQD q d = (advTermQD q d + verTermQ + √(clsBoundQ q + verLinQ))² + readErrQ`: Security's
bound with `q · √(6 · 2^-128)` replaced by `√(6 · 2^-128 · min d q · q)` and `2q · 2^-64` by
`2√(q · min d q) · 2^-64`.
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Xmss.Hybrid
open LeanXmss HashSig

/-! ## The bound -/

/-- **The bound on runtime 2's averaged win, with rounds** (DepthEnd's `uavg_p2Q_le_of` at
`clsBoundQ`). -/
noncomputable def eventTermQD (q d : ℕ) : ℝ≥0∞ :=
  (advTermQD q d + verTermQ + (clsBoundQ q + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ

/-- **The depth-aware leanXMSS QROM bound**: `(√eventTermQD q d + hybTermQD q d)²` for `q` calls
of `H` in `d` rounds. -/
noncomputable def xmssQromDepthBound (q d : ℕ) : ℝ≥0∞ :=
  (eventTermQD q d ^ (2⁻¹ : ℝ) + hybTermQD q d) ^ 2

/-! ## The proof -/

/-- **The depth-aware bound for one parallel adversary whose serialization reuses no leaf.** -/
theorem winProb_le_xmssQromDepthBound (A : AdversaryPar) {q d : ℕ}
    (hw : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.widthCharge) q)
    (hr : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.roundCharge) d)
    (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.signChargePar) lifetime)
    (hleaf : NoLeafReuse (SufCma.serialize A)) :
    SufCma.winProb xmssRom (SufCma.serialize A) ≤ xmssQromDepthBound q d := by
  have hhash : ∀ pk, IFreeM.IsChargeBound (SufCma.serialize A pk)
      (SufCma.cmdCharge SufCma.hashCharge) q :=
    fun pk ↦ SufCma.isChargeBound_toSeq_hash (hw pk)
  have hsign : ∀ pk, IFreeM.IsChargeBound (SufCma.serialize A pk)
      (SufCma.cmdCharge SufCma.signCharge) lifetime :=
    fun pk ↦ SufCma.isChargeBound_toSeq_sign (hs pk)
  refine (winProb_le_hybrid_depth A hw hr hs).trans ?_
  unfold xmssQromDepthBound eventTermQD
  gcongr
  exact uavg_p2Q_le_of (SufCma.serialize A) hhash hsign
    (fun θ ↦ ewPrefixQD_le A hw hr hs (honQ θ) θ)
    (uavg_twPQ_le (SufCma.serialize A) hhash hsign hleaf)

/-- **leanXMSS is quantum SUF-CMA secure in the QROM against parallel adversaries**, with the
depth-aware bound `xmssQromDepthBound`: an adversary making at most `q` calls of `H` in at most `d`
rounds of parallel calls and at most `lifetime` signing requests forges with probability at most
`xmssQromDepthBound q d`. -/
theorem leanXmss_qrom_depth_security :
    SufCma.QuantumStronglyUnforgeablePar xmssRom lifetime xmssQromDepthBound := by
  intro q d A hw hr hs
  rw [SufCma.winProbPar_eq]
  refine (winProb_le_winProb_refuse (SufCma.serialize A)).trans ?_
  rw [refuse_serialize]
  refine winProb_le_xmssQromDepthBound (refusePar A)
    (fun pk ↦ isChargeBound_refuseFromPar (A pk) ∅ (hw pk))
    (fun pk ↦ isChargeBound_refuseFromPar (A pk) ∅ (hr pk))
    (fun pk ↦ isChargeBound_refuseFromPar (A pk) ∅ (hs pk)) ?_
  rw [← refuse_serialize]
  exact noLeafReuse_refuse _

end Quantum.Qrom.Xmss

end
