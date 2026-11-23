module

public import Quantum.Qrom.Sphincs.Multi.Costs.Bound
public import Quantum.Qrom.Sphincs.Multi.Costs.PrefixInv
public import Quantum.Qrom.Sphincs.Multi.Costs.Enc
public import Quantum.Qrom.Sphincs.Multi.Costs.RecU

@[expose] public section

/-!
# The classical costs of the `n`-user leanSPHINCS runtime 2: the final bound

For an adversary with at most `q` hash calls and `total` signing requests, the classical costs of
the challenge prefix on the tables with distinct `PK.seed`s (`twMaskSN`), averaged over the hidden
values:

* `uavg_twMaskSN_le`: at most `clsBoundSN total q` (PrefixInv's `prefixInvQSN`, Enc's
  `encPreSN_le`, RecU's `uavg_recUPreSN_le`, GameTCalls' call counts); the re-grind terms of the
  single-user bound vanish with the memo.
* `clsBoundSN_le`: for `total, q ≤ 2^64`, at most `((257.1 √q + 0.1) / 2^64)²`.
-/

open IPFunctor
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

open Quantum Quantum.Sponge
open Quantum.Xmss.Assembly (recSpec extCls uavg_const_le)
open Quantum.Xmss.Hybrid (uavg)
open Quantum.Qrom.SufCma.Multi (cmdCharge hashCharge signCharge)

attribute [local irreducible] sphincsRom

/- Instance search for the registers over `Finset (TPosN n)` exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-- **The closed form of the averaged costs** (`total, q ≤ 2^64`):
`clsBoundSN total q ≤ ((257.1 √q + 0.1) / 2^64)²`. -/
theorem clsBoundSN_le {total q : ℕ} (ht : total ≤ 2 ^ 64) (hq : q ≤ 2 ^ 64) :
    clsBoundSN total q ≤ ENNReal.ofReal (((257.1 * √(q : ℝ) + 0.1) / 2 ^ 64) ^ 2) :=
  twBoundQ_tauUN_le hq (clsCapSN_le ht)

variable {n : ℕ} (A : MuAdversaryS n) {q total : ℕ}
  (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
  (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
include hhash hsign

/-- **The averaged recorded unselected weights** on the tables with distinct `PK.seed`s: RecU's
`uavg_recUPreSN_le`; beyond `2^128` users no table has distinct `PK.seed`s. -/
theorem uavg_recUMaskSN_le : uavg (recUMaskSN A) ≤ tauUN q (clsCapSN total) := by
  by_cases hn : n ≤ 2 ^ 128
  · exact uavg_recUPreSN_le A hn
      (advCalls_prefixQS (M := SelMemN n) cwUpdN (strPolN n) A hhash hsign)
      (clsCalls_prefixQS (M := SelMemN n) cwUpdN (strPolN n) A hhash hsign)
  · have h0 : recUMaskSN A = fun _ ↦ 0 := funext fun θ ↦ by
      classical
      unfold recUMaskSN
      exact ite_eq_right fun h ↦ hn (le_of_pDistinctS h)
    rw [h0]
    exact (uavg_const_le 0).trans zero_le

/-- **The averaged classical costs of the challenge prefix** on the tables with distinct
`PK.seed`s: at most `clsBoundSN total q`. -/
theorem uavg_twMaskSN_le : uavg (twMaskSN A) ≤ clsBoundSN total q :=
  uavg_twMaskSN_le_of A (fun θ hP ↦ prefixInvQSN A θ hP)
    (clsCalls_prefixQS (M := SelMemN n) cwUpdN (strPolN n) A hhash hsign)
    (fun θ hP ↦ encPreSN_le A θ (prefixInvQSN A θ hP)
      (advCalls_prefixQS (M := SelMemN n) cwUpdN (strPolN n) A hhash hsign θ)
      (clsCalls_prefixQS (M := SelMemN n) cwUpdN (strPolN n) A hhash hsign θ))
    (uavg_recUMaskSN_le A hhash hsign)

end Quantum.Qrom.Sphincs.Multi

end
