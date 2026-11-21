module

public import Quantum.Qrom.Sphincs.DepthEnd
public import Quantum.Qrom.Sphincs.DepthHybrid
public import Quantum.Qrom.Sphincs.DepthCommute
public import Quantum.Qrom.Sphincs.DepthBoundValue

@[expose] public section

/-!
# leanSPHINCS is quantum SUF-CMA secure in the QROM against parallel adversaries

The assembly of Security's chain for a parallel adversary `A` (`SufCma.AdversaryPar`) making at
most `q` calls of `H` in at most `d` rounds. Its game is the game of its serialization
(`SufCma.winProbPar_eq`), and every step of the sequential chain runs on the serialized adversary
except two, which run on the game with rounds (`gameQPar`). The challenger regroups each call of
`H` into a call of `F` with an isometry before and its adjoint after; on a round these are
reordered (all isometries, the round's calls of `F`, all adjoints), which runs alike against
every runtime (DepthCommute's `roundsCommute`), so the serialized game runs as the serialization
of the game with rounds (DepthGame's `runTWEq_gameQ`).

1. **The hybrid with rounds** (DepthHybrid's `winProb_le_hybrid_depth`):
   `winProb ≤ (√(E p2Q) + hybTermQD q d)²`,
   `hybTermQD q d = 2√(q · min d q)·2^-64 + √(clsCapQ·2^-128)`.
2. **The event with rounds** (DepthEnd's `uavg_p2Q_le_depth` at `ewPrefixQD_le`):
   `E p2Q ≤ (advBarQD q d + verBarQ + √(clsBoundQ q + verLinBarQ))² + readErrQ`,
   `advBarQD q d = √(6 · epsBarQ · min d q · q)` (the stream averaging is linear in `epsQ`).
3. **The prefix's classical costs** (Costs' `uavg_twPQ_le` on the serialized adversary):
   `clsBoundQ q`, unchanged.

`sphincsQromDepthBound q d = (√eventTermQD q d + hybTermQD q d)²` (DepthBound).
-/

open IPFunctor
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Xmss.Hybrid

attribute [local irreducible] sphincsRom

/-- **The interleaved and the batched rounds of leanSPHINCS's challenger run alike** against
every runtime. -/
theorem roundsCommute_sphincs (R : QuantumRuntime (RSpecS SelMem)) :
    RoundsCommute TPos SelMem hmsgRoute R :=
  roundsCommute (S := TPos) (M' := SelMem) hmsgRoute R

/-- **The depth-aware bound for one parallel adversary.** -/
theorem winProb_le_sphincsQromDepthBound (A : SAdversaryPar) {q d : ℕ}
    (hw : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.widthCharge) q)
    (hr : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.roundCharge) d)
    (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.signChargePar)
      signatureLimit) :
    SufCma.winProb sphincsRom (SufCma.serialize A) ≤ sphincsQromDepthBound q d := by
  have hhash : ∀ pk, IFreeM.IsChargeBound (SufCma.serialize A pk)
      (SufCma.cmdCharge SufCma.hashCharge) q :=
    fun pk ↦ SufCma.isChargeBound_toSeq_hash (hw pk)
  have hsign : ∀ pk, IFreeM.IsChargeBound (SufCma.serialize A pk)
      (SufCma.cmdCharge SufCma.signCharge) signatureLimit :=
    fun pk ↦ SufCma.isChargeBound_toSeq_sign (hs pk)
  refine (winProb_le_hybrid_depth roundsCommute_sphincs A hw hr hs).trans ?_
  unfold sphincsQromDepthBound eventTermQD
  gcongr
  exact uavg_p2Q_le_depth (SufCma.serialize A) d hhash hsign
    (fun θ ↦ ewPrefixQD_le roundsCommute_sphincs A hw hr hs (pkQ θ) (honQ θ) (starQ θ) θ)
    (uavg_twPQ_le starQ strPol noVal_strPol (SufCma.serialize A) hhash hsign)

/-- **leanSPHINCS is quantum SUF-CMA secure in the QROM against parallel adversaries**, with the
depth-aware bound `sphincsQromDepthBound`: an adversary making at most `q` calls of `H` in at
most `d` rounds of parallel calls and at most `signatureLimit` signing requests forges with
probability at most `sphincsQromDepthBound q d`. -/
theorem leanSphincs_qrom_depth_security :
    SufCma.QuantumStronglyUnforgeablePar sphincsRom signatureLimit sphincsQromDepthBound := by
  intro q d A hw hr hs
  rw [SufCma.winProbPar_eq]
  exact winProb_le_sphincsQromDepthBound A hw hr hs

/-! ## Consequences -/

/-- **Consistency**: at `d = q` (a sequential adversary) the depth-aware bound is the sequential
bound `sphincsQromBound q`. -/
theorem sphincsQromDepthBound_self (q : ℕ) : sphincsQromDepthBound q q = sphincsQromBound q := by
  have ha : advBarQD q q = advBarQ q := by
    unfold advBarQD advBarQ
    rw [min_self]
    ring_nf
  have hh : hybTermQD q q = hybTermQ q := by
    unfold hybTermQD hybTermQ
    rw [min_self]
  unfold sphincsQromDepthBound sphincsQromBound eventTermQD eventTermQ eventTermOf
  rw [ha, hh]

/-- **leanSPHINCS against parallel adversaries, in closed form**: at most `q` calls of `H` in at
most `d` rounds, `Pr ≤ ((5.86 √(q · min d q) + 2^-55 q + 257.3 √q + 1.818 · 2^32) / 2^64)²`. -/
theorem leanSphincs_qrom_depth_security_closed :
    SufCma.QuantumStronglyUnforgeablePar sphincsRom signatureLimit fun q d ↦
      ENNReal.ofReal (((5.86 * √((q : ℝ) * (min d q : ℕ)) + (2 ^ 55)⁻¹ * q +
        257.3 * √(q : ℝ) + 1.818 * 2 ^ 32) / 2 ^ 64) ^ 2) :=
  fun q d A hw hr hs ↦
    (leanSphincs_qrom_depth_security q d A hw hr hs).trans (sphincsQromDepthBound_le q d)

/-- **NIST's MAXDEPTH `2^40`**: a parallel adversary making at most `2^64` calls of `H` in at most
`2^40` rounds and at most `signatureLimit` signing requests forges with probability at most
`2^-18`. -/
theorem leanSphincs_qrom_maxDepth_two_pow_40 {q d : ℕ} (hq : q ≤ 2 ^ 64) (hd : d ≤ 2 ^ 40)
    (A : SAdversaryPar)
    (hw : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.widthCharge) q)
    (hr : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.roundCharge) d)
    (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.signChargePar)
      signatureLimit) :
    SufCma.winProbPar sphincsRom A ≤ (2 ^ 18 : ℝ≥0∞)⁻¹ :=
  (leanSphincs_qrom_depth_security q d A hw hr hs).trans
    (sphincsQromDepthBound_two_pow_64_40_le hq hd)

/-- **`2^80` calls in `2^28` rounds** (MAXDEPTH `2^40` at a Keccak-f depth of `2^12`): the forging
probability is at most `2^-14`. -/
theorem leanSphincs_qrom_two_pow_80_28 {q d : ℕ} (hq : q ≤ 2 ^ 80) (hd : d ≤ 2 ^ 28)
    (A : SAdversaryPar)
    (hw : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.widthCharge) q)
    (hr : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.roundCharge) d)
    (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.signChargePar)
      signatureLimit) :
    SufCma.winProbPar sphincsRom A ≤ (2 ^ 14 : ℝ≥0∞)⁻¹ :=
  (leanSphincs_qrom_depth_security q d A hw hr hs).trans
    (sphincsQromDepthBound_two_pow_80_28_le hq hd)

end Quantum.Qrom.Sphincs

end
