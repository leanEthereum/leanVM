module

public import Quantum.Qrom.Xmss.Multi.End
public import Quantum.Qrom.Xmss.Multi.Hybrid
public import Quantum.Qrom.Xmss.Multi.Costs.Total
public import Quantum.Qrom.Xmss.Security

@[expose] public section

/-!
# leanXMSS is multi-user quantum SUF-CMA secure in the QROM

The assembly of the `n`-user chain of games, Keccak-256 as one random function `H` on
`HashDomain`, `n` users, at most `q` calls of `H` and at most `total` signing requests overall:

0. **No leaf reuse** (NoReuse's `muWinProb_le_refuseMu`): the adversary that refuses its own
   reused requests of each user wins at least as often, within the same budgets
   (`isChargeBound_refuseMu`) and with no reused leaf (`noLeafReuseMu_refuseMu`).
1. **Runtime 1 against runtime 2** (Hybrid's `muWinProb_le_hybridN`): the collisions of public
   parameters and seed halves (`collTermN n`), then the hybrid on the masked tables `GoodN`:
   `muWinProb ≤ collTermN n + (√(E[1_GoodN p2QN]) + hybTermQ q)²`.
2. **Runtime 2's win** (End): per good table the event at the end of the game, the verification
   reads graded like sponge calls, and the read error; averaged with Jensen against the costs
   on the tables with distinct public parameters (`twMaskN`).
3. **The prefix's classical costs** (Costs' `uavg_twMaskN_le`, without leaf reuse; no selected
   key is read again, so no re-grind term): at most `clsBoundQN n total q = twBoundQ q (clsCapN n
   total) 0 0`.

`xmssQromMuBound n total q = collTermN n + (√eventTermQN n total q + hybTermQ q)²` with
`eventTermQN n total q = (advTermQ q + verTermQ + √(clsBoundQN n total q + verLinQ))² + readErrQ`.
The per-user limit does not enter the bound. For `n = 1` the theorem is a single-user bound
(`leanXmss_qrom_security_one`).
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Qrom.SufCma.Multi (cmdCharge hashCharge signCharge muWinProb)

/-! ## The bound -/

/-- **The prefix's averaged classical costs** (Costs' `uavg_twMaskN_le`): the classical calls of
`n` users, no re-grind reads and no recorded hits. -/
noncomputable def clsBoundQN (n total q : ℕ) : ℝ≥0∞ :=
  twBoundQ q (clsCapN n total) 0 0

/-- **The bound on runtime 2's averaged win** (End's `uavg_ite_le_of_forall` at `clsBoundQN`). -/
noncomputable def eventTermQN (n total q : ℕ) : ℝ≥0∞ :=
  (advTermQ q + verTermQ + (clsBoundQN n total q + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ

/-- **The multi-user leanXMSS QROM bound**: `collTermN n + (√eventTermQN n total q + hybTermQ q)²`.
-/
noncomputable def xmssQromMuBound (n total q : ℕ) : ℝ≥0∞ :=
  collTermN n + (eventTermQN n total q ^ (2⁻¹ : ℝ) + hybTermQ q) ^ 2

/-! ## The proof -/

section adversary

variable {n : ℕ} (A : MuAdversary n) {q total : ℕ}
  (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
  (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
include hhash hsign

/-- **Runtime 2's win at a masked table**: the event `BadRQN` at the end of the game (End), its
weight at the end of the prefix by Costs' `ewPrefixQN_le`. -/
theorem p2QN_le (θ : HPosN n → Digest) (hG : GoodN θ) :
    p2QN xmssValid A θ ≤
      (advTermQ q + verTermQ + (twMaskN A θ + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ := by
  rw [twMaskN_of_pDistinct A hG.1.2]
  exact (evalDistMap_muGameQN_le_eventWeight xmssValid A θ (BadRQN (honQN θ) (parQN θ))
    (fun _ h ↦ mem_badRQN_iff.2 h) hG.1).trans
    (add_le_add (ewMuGameQN_le xmssValid A hhash hsign _
      (fun W m ↦ upClosed_slice_badRQN W m) (fun W m t ↦ freshBound_slice_badRQN W m t) θ _
      (ewPrefixQN_le _ _ A θ (advCalls_prefixQN cwUpdN A hhash hsign θ)
        (clsCalls_prefixQN cwUpdN A hhash hsign θ))) le_rfl)

/-- **The multi-user leanXMSS bound for one adversary without leaf reuse.** -/
theorem muWinProb_le_xmssQromMuBound (hleaf : NoLeafReuseMu A) :
    muWinProb xmssRom xmssValid n A ≤ xmssQromMuBound n total q := by
  refine (muWinProb_le_hybridN xmssValid A hhash hsign).trans ?_
  unfold xmssQromMuBound eventTermQN
  gcongr
  exact uavg_ite_le_of_forall GoodN (p2QN xmssValid A) (twMaskN A) _ (p2QN_le A hhash hsign)
    (uavg_twMaskN_le A hhash hsign hleaf)

end adversary

/-- **leanXMSS is multi-user quantum SUF-CMA secure in the QROM** with bound
`xmssQromMuBound n total`: an adversary against `n` users making at most `q` calls of `H` and at
most `total` signing requests overall forges for some user with probability at most
`xmssQromMuBound n total q`, whatever the per-user limit. -/
theorem leanXmss_qrom_mu_security (n perUser total : ℕ) :
    SufCma.Multi.MuQuantumStronglyUnforgeable xmssRom xmssValid n perUser total
      (xmssQromMuBound n total) :=
  fun _ A hq _ hs ↦
    (muWinProb_le_refuseMu A).trans (muWinProb_le_xmssQromMuBound (refuseMu A)
      (fun pks ↦ isChargeBound_refuseMu (hq pks)) (fun pks ↦ isChargeBound_refuseMu (hs pks))
      (noLeafReuseMu_refuseMu A))

/-- **One user**: the multi-user theorem at `n = 1` is a single-user bound. -/
theorem leanXmss_qrom_security_one :
    SufCma.QuantumStronglyUnforgeable xmssRom lifetime (xmssQromMuBound 1 lifetime) :=
  xmss_muQuantumStronglyUnforgeable_one_iff.mp (leanXmss_qrom_mu_security 1 lifetime lifetime)

end Quantum.Qrom.Xmss.Multi

end
