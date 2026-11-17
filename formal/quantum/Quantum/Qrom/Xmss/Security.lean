module

public import Quantum.Qrom.Xmss.End
public import Quantum.Qrom.Xmss.NoReuse
public import Quantum.Qrom.Xmss.Costs.Total

@[expose] public section

/-!
# leanXMSS is quantum SUF-CMA secure in the QROM

The assembly of the chain of games (design, sections 0 and 2), Keccak-256 as one random
function `H` on `HashDomain`:

0. **No leaf reuse** (NoReuse's `winProb_le_winProb_refuse`): the adversary that refuses its own
   reused requests wins at least as often, within the same budgets (`isChargeBound_refuse`) and
   with no reused leaf (`noLeafReuse_refuse`).
1. **Runtime 1 against runtime 2** (Hybrid's `winProb_le_hybrid_qrom`):
   `winProb ≤ (√(E p2Q) + hybTermQ q)²`, `hybTermQ q = 2q·2^-64 + √(verifyCalls · 2^-128)`.
2. **Runtime 2's win** (End's `uavg_p2Q_le`): the event at the end of the game, the verification
   reads graded like sponge calls, and the read error:
   `E p2Q ≤ (advTermQ q + verTermQ + √(clsBoundQ q + verLinQ))² + readErrQ`.
3. **The prefix's classical costs** (Costs' `uavg_twPQ_le`, without leaf reuse): averaged over the
   hidden values at most `clsBoundQ q = twBoundQ q clsCapQ clsCapQ clsCapQ`.

`xmssQromBound q = (√eventTermQ q + hybTermQ q)²` with
`eventTermQ q = (advTermQ q + verTermQ + √(clsBoundQ q + verLinQ))² + readErrQ`.
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Xmss.Hybrid
open LeanXmss HashSig

/-! ## The bound -/

/-- **The prefix's averaged classical costs** (Costs' `uavg_twPQ_le`): the classical calls,
the re-grind reads and the recorded hits, each at most `clsCapQ`. -/
noncomputable def clsBoundQ (q : ℕ) : ℝ≥0∞ :=
  twBoundQ q clsCapQ clsCapQ clsCapQ

/-- **The bound on runtime 2's averaged win** (End's `uavg_p2Q_le` at `clsBoundQ`). -/
noncomputable def eventTermQ (q : ℕ) : ℝ≥0∞ :=
  (advTermQ q + verTermQ + (clsBoundQ q + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ

/-- **The leanXMSS QROM bound**: `(√eventTermQ q + hybTermQ q)²`. -/
noncomputable def xmssQromBound (q : ℕ) : ℝ≥0∞ :=
  (eventTermQ q ^ (2⁻¹ : ℝ) + hybTermQ q) ^ 2

/-! ## The proof -/

/-- **The leanXMSS bound for one adversary without leaf reuse.** -/
theorem winProb_le_xmssQromBound (A : Adversary) {q : ℕ}
    (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) lifetime)
    (hleaf : NoLeafReuse A) :
    SufCma.winProb xmssRom A ≤ xmssQromBound q := by
  refine (winProb_le_hybrid_qrom A hhash hsign).trans ?_
  unfold xmssQromBound eventTermQ
  gcongr
  exact uavg_p2Q_le A hhash hsign (uavg_twPQ_le A hhash hsign hleaf)

/-- **leanXMSS is quantum SUF-CMA secure in the QROM** with bound `xmssQromBound`: an adversary
making at most `q` calls of `H` and at most `lifetime` signing requests forges with probability
at most `xmssQromBound q`. Refusing reused leaves does not lower the win probability and keeps
the budgets (NoReuse). -/
theorem leanXmss_qrom_security :
    SufCma.QuantumStronglyUnforgeable xmssRom lifetime xmssQromBound :=
  fun _ A hq hs ↦
    (winProb_le_winProb_refuse A).trans (winProb_le_xmssQromBound (refuse A)
      (fun pk ↦ isChargeBound_refuse (hq pk)) (fun pk ↦ isChargeBound_refuse (hs pk))
      (noLeafReuse_refuse A))

end Quantum.Qrom.Xmss

end
