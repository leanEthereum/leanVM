module

public import Quantum.Qrom.Sphincs.End
public import Quantum.Qrom.Sphincs.Costs.Total

@[expose] public section

/-!
# leanSPHINCS is quantum SUF-CMA secure in the QROM

The assembly of the chain of games (design, sections 0 and 2), Keccak-256 as one random
function `H` on `HashDomain`, the two `H_msg` calls of a message regrouped into one cell:

1. **Runtime 1 against runtime 2** (Hybrid's `winProb_le_hybrid_qrom`, with the stream
   reindexing to `strPol`): `winProb ≤ (√(E p2Q strPol) + hybTermQ q)²`,
   `hybTermQ q = 2q·2^-64 + √(clsCapQ · 2^-128)`.
2. **Runtime 2's win** (End's `uavg_p2Q_le`): the event at the end of the game, the verification
   reads graded like adversary calls, Minkowski over the stream cover, and the read error:
   `E p2Q ≤ (advBarQ q + verBarQ + √(clsBoundQ q + verLinBarQ))² + readErrQ`.
3. **The prefix's classical costs** (Costs' `uavg_twPQ_le`): averaged over the hidden values at
   most `clsBoundQ q`.

`sphincsQromBound q = (√eventTermQ q + hybTermQ q)²` with
`eventTermQ q = (advBarQ q + verBarQ + √(clsBoundQ q + verLinBarQ))² + readErrQ`.
-/

open IPFunctor
open scoped ENNReal
open Sphincs (signatureLimit)

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Xmss.Hybrid

/-! ## The bound -/

/-- **The prefix's averaged classical costs** (Costs' `uavg_twPQ_le`). -/
noncomputable def clsBoundQ (q : ℕ) : ℝ≥0∞ :=
  twBoundQ encC encEps q clsCapQ (tauU q clsCapQ) clsCapQ clsCapQ

/-- **The bound on runtime 2's averaged win** (End's `uavg_p2Q_le` at `T`). -/
noncomputable def eventTermOf (T : ℝ≥0∞) (q : ℕ) : ℝ≥0∞ :=
  (advBarQ q + verBarQ + (T + verLinBarQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ

/-- The event term at the prefix's averaged costs. -/
noncomputable def eventTermQ (q : ℕ) : ℝ≥0∞ :=
  eventTermOf (clsBoundQ q) q

/-- **The leanSPHINCS QROM bound**: `(√eventTermQ q + hybTermQ q)²`. -/
noncomputable def sphincsQromBound (q : ℕ) : ℝ≥0∞ :=
  (eventTermQ q ^ (2⁻¹ : ℝ) + hybTermQ q) ^ 2

/-! ## The proof -/

/-- **The bound for one adversary, from a bound `T` on the prefix's averaged costs.** -/
theorem winProb_le_of_cost (A : SAdversary) {q : ℕ}
    (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge)
      signatureLimit) {T : ℝ≥0∞}
    (hcost : uavg (fun θ : TVals ↦ twPQ (pkQ θ) (honQ θ) (starQ θ) strPol A θ) ≤ T) :
    SufCma.winProb sphincsRom A ≤ (eventTermOf T q ^ (2⁻¹ : ℝ) + hybTermQ q) ^ 2 := by
  refine (winProb_le_hybrid_qrom A hhash hsign).trans ?_
  unfold eventTermOf
  gcongr
  exact uavg_p2Q_le A hhash hsign hcost

/-- **The leanSPHINCS bound for one adversary.** -/
theorem winProb_le_sphincsQromBound (A : SAdversary) {q : ℕ}
    (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge)
      signatureLimit) :
    SufCma.winProb sphincsRom A ≤ sphincsQromBound q :=
  winProb_le_of_cost A hhash hsign (uavg_twPQ_le starQ strPol noVal_strPol A hhash hsign)

/-- **leanSPHINCS is quantum SUF-CMA secure in the QROM** with bound `sphincsQromBound`: an
adversary making at most `q` calls of `H` and at most `signatureLimit` signing requests forges
with probability at most `sphincsQromBound q`. -/
theorem leanSphincs_qrom_security :
    SufCma.QuantumStronglyUnforgeable sphincsRom signatureLimit sphincsQromBound :=
  fun _ A hq hs ↦ winProb_le_sphincsQromBound A hq hs

end Quantum.Qrom.Sphincs

end
