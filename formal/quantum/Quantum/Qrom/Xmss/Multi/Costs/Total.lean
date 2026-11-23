module

public import Quantum.Qrom.Xmss.Multi.Costs.Bound
public import Quantum.Qrom.Xmss.Multi.Costs.PrefixInv
public import Quantum.Qrom.Xmss.Multi.Costs.Enc
public import Quantum.Qrom.Xmss.Multi.Costs.RecU

@[expose] public section

/-!
# The classical costs of the `n`-user runtime 2: the final bound

For an adversary with at most `q` hash calls and `total` signing requests that never reuses a
user's leaf, the classical costs of the challenge prefix on the tables with distinct public
parameters (`twMaskN`), averaged over the hidden values:

* `uavg_twMaskN_le`: at most `twBoundQ q (clsCapN n total) 0 0` (PrefixInv's `prefixInvQN`,
  Enc's `encPreN_le`, RecU's `uavg_recUPreN_le`, GameTCalls' call counts); the re-grind terms of
  the single-user bound vanish with the memo.
* `uavg_twMaskN_le_closed`: for `total, q ≤ 2^64`, at most `((0.6 · 2^17 √q + 1) / 2^64)²`.
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.Qrom.Xmss.Multi

open Quantum Quantum.Sponge LeanXmss HashSig
open Quantum.Xmss.Assembly (recSpec extCls uavg_const_le)
open Quantum.Xmss.Hybrid (uavg)
open Quantum.Qrom.SufCma.Multi (cmdCharge hashCharge signCharge)

attribute [local irreducible] xmssRom

/-- **Distinct public parameters bound the users**: `n ≤ 2^128`. -/
theorem le_of_pDistinct {n : ℕ} {w : QTableN n} (h : PDistinct w) : n ≤ 2 ^ 128 := by
  have hc := Fintype.card_le_of_injective _ h
  rw [Fintype.card_fin] at hc
  exact hc.trans_eq ((Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _))

variable {n : ℕ} (A : MuAdversary n) {q total : ℕ}
  (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
  (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
include hhash hsign

/-- The adversary calls of the challenge prefix (GameTCalls' `advCalls_prefixQN`). -/
theorem advCalls_prefixQN' (θ : HPosN n → Digest) :
    IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 0 else 1)
      q :=
  advCalls_prefixQN cwUpdN A hhash hsign θ

/-- The classical calls of the challenge prefix (GameTCalls' `clsCalls_prefixQN`). -/
theorem clsCalls_prefixQN' (θ : HPosN n → Digest) :
    IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 1 else 0)
      (clsCapN n total) :=
  clsCalls_prefixQN cwUpdN A hhash hsign θ

/-- **The averaged recorded unselected weights** on the tables with distinct parameters: RecU's
`uavg_recUPreN_le`; beyond `2^128` users no table has distinct parameters. -/
theorem uavg_recUMaskN_le : uavg (recUMaskN A) ≤ tauU q (clsCapN n total) := by
  by_cases hn : n ≤ 2 ^ 128
  · exact uavg_recUPreN_le A hn (advCalls_prefixQN' A hhash hsign)
      (clsCalls_prefixQN' A hhash hsign)
  · have h0 : recUMaskN A = fun _ ↦ 0 := funext fun θ ↦ by
      classical
      unfold recUMaskN
      exact ite_eq_right fun h ↦ hn (le_of_pDistinct h)
    rw [h0]
    exact (uavg_const_le 0).trans zero_le

/-- **The averaged classical costs of the challenge prefix** on the tables with distinct public
parameters. -/
theorem uavg_twMaskN_le (hleaf : NoLeafReuseMu A) :
    uavg (twMaskN A) ≤ twBoundQ q (clsCapN n total) 0 0 :=
  uavg_twMaskN_le_of A (fun θ hP ↦ prefixInvQN A hleaf θ hP) (clsCalls_prefixQN' A hhash hsign)
    (fun θ hP ↦ encPreN_le A θ (prefixInvQN A hleaf θ hP) (advCalls_prefixQN' A hhash hsign θ)
      (clsCalls_prefixQN' A hhash hsign θ))
    (uavg_recUMaskN_le A hhash hsign)

/-- **The averaged classical costs of the challenge prefix in closed form** (`total, q ≤ 2^64`):
`((0.6 · 2^17 √q + 1) / 2^64)²`. -/
theorem uavg_twMaskN_le_closed (hleaf : NoLeafReuseMu A) (ht : total ≤ 2 ^ 64)
    (hq : q ≤ 2 ^ 64) :
    uavg (twMaskN A) ≤ ENNReal.ofReal (((0.6 * 2 ^ 17 * √q + 1) / 2 ^ 64) ^ 2) :=
  (uavg_twMaskN_le A hhash hsign hleaf).trans (twBoundQ_le_mu hq (clsCapN_le ht))

end Quantum.Qrom.Xmss.Multi

end
