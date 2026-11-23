module

public import Quantum.Qrom.Sphincs.Multi.End
public import Quantum.Qrom.Sphincs.Multi.Hybrid
public import Quantum.Qrom.Sphincs.Multi.Costs.Total

@[expose] public section

/-!
# leanSPHINCS is multi-user quantum SUF-CMA secure in the QROM

The assembly of the `n`-user chain of games, Keccak-256 as one random function `H` on
`HashDomain` (the two `H_msg` calls of a message regrouped into one cell), `n` users, at most `q`
calls of `H`, at most `signatureLimit` signing requests per user and `total` overall:

1. **Runtime 1 against runtime 2** (Hybrid's `muWinProb_le_hybridSN`): the collisions of public
   seeds and master seeds (`collTermSN n`), then the masked hybrid on distinct public seeds,
   reads of encoding cells free:
   `muWinProb ≤ collTermSN n + (√(E p2SN) + hybTermSN n q)²`.
2. **Runtime 2's win** (End's `uavg_p2SN_le`): the event at the end of the game, the verification
   reads graded like adversary calls, the worst user's coverage price averaged (`rhoMaxQ n`), and
   the read error.
3. **The prefix's classical costs** (Costs' `uavg_twMaskSN_le`; with the memo no counter search
   reads a selected key, so no re-grind term): at most `clsBoundSN total q`.

`sphincsQromMuBound n total q = collTermSN n + (√eventTermSN n total q + hybTermSN n q)²` with
`eventTermSN n total q = (advBarN n q + verBarN n + √(clsBoundSN total q + verLinBarN n))² +
readErrQ`. For `n = 1` the theorem is a single-user bound (`leanSphincs_qrom_security_one`).
-/

open IPFunctor
open scoped ENNReal
open Sphincs (signatureLimit)

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Xmss.Hybrid
open Quantum.Qrom.SufCma.Multi (cmdCharge hashCharge signCharge signChargeAt muWinProb)

attribute [local irreducible] sphincsRom

/-! ## The bound -/

/-- **The bound on runtime 2's averaged win** (End's `uavg_p2SN_le` at `clsBoundSN`). -/
noncomputable def eventTermSN (n total q : ℕ) : ℝ≥0∞ :=
  (advBarN n q + verBarN n + (clsBoundSN total q + verLinBarN n) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ

/-- **The multi-user leanSPHINCS QROM bound**:
`collTermSN n + (√eventTermSN n total q + hybTermSN n q)²`. -/
noncomputable def sphincsQromMuBound (n total q : ℕ) : ℝ≥0∞ :=
  collTermSN n + (eventTermSN n total q ^ (2⁻¹ : ℝ) + hybTermSN n q) ^ 2

/-! ## The proof -/

/-- **The multi-user leanSPHINCS bound for one adversary.** -/
theorem muWinProb_le_sphincsQromMuBound {n : ℕ} (A : MuAdversaryS n) {q total : ℕ}
    (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
    (hsignAt : ∀ pks i, IFreeM.IsChargeBound (A pks) (cmdCharge (signChargeAt i))
      signatureLimit)
    (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total) :
    muWinProb sphincsRom sphincsValid n A ≤ sphincsQromMuBound n total q := by
  refine (muWinProb_le_hybridSN sphincsValid A hhash hsign).trans ?_
  unfold sphincsQromMuBound eventTermSN
  gcongr
  exact uavg_p2SN_le sphincsValid A hhash hsign hsignAt (uavg_twMaskSN_le A hhash hsign)

/-- **leanSPHINCS is multi-user quantum SUF-CMA secure in the QROM** with bound
`sphincsQromMuBound n total`: an adversary against `n` users making at most `q` calls of `H`, at
most `signatureLimit` signing requests to each user and `total` overall forges for some user with
probability at most `sphincsQromMuBound n total q`. -/
theorem leanSphincs_qrom_mu_security (n total : ℕ) :
    SufCma.Multi.MuQuantumStronglyUnforgeable sphincsRom sphincsValid n signatureLimit total
      (sphincsQromMuBound n total) :=
  fun _ A hq hu hs ↦ muWinProb_le_sphincsQromMuBound A hq hu hs

/-- **One user**: the multi-user theorem at `n = 1` is a single-user bound. -/
theorem leanSphincs_qrom_security_one :
    SufCma.QuantumStronglyUnforgeable sphincsRom signatureLimit
      (sphincsQromMuBound 1 signatureLimit) :=
  sphincs_muQuantumStronglyUnforgeable_one_iff.mp
    (leanSphincs_qrom_mu_security 1 signatureLimit)

end Quantum.Qrom.Sphincs.Multi

end
