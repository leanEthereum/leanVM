module

public import Quantum.Qrom.Xmss.Costs.Bound
public import Quantum.Qrom.Xmss.Costs.PrefixInv
public import Quantum.Qrom.Xmss.Costs.Enc
public import Quantum.Qrom.Xmss.Costs.RecU
public import Quantum.Qrom.Xmss.Costs.RegrindSel
public import Quantum.Qrom.Xmss.GameTCalls

@[expose] public section

/-!
# The classical costs of runtime 2: the final bound

For an adversary with at most `q` hash calls and `lifetime` signing requests that never reuses a
leaf, the classical costs of the challenge prefix, averaged over the hidden values:

* `clsCapQ_le`: the classical calls of the game, `clsCapQ ≤ 2^65 + 2^41`;
* `uavg_twPQ_le`: `uavg twPQ ≤ twBoundQ q clsCapQ clsCapQ clsCapQ` (PrefixInv's `prefixInvQ`,
  Enc's `encPre_le`, RecU's `uavg_recUPre_le'`, RegrindSel's `selPre_le_small`, Regrind's
  `recSPre_le`, GameTCalls' call counts);
* `uavg_twPQ_le_closed`: for `q ≤ 2^64`, at most `((0.523 · 2^17 √q + 0.708 · 2^33) / 2^64)²`.
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.Qrom.Xmss

open Quantum Quantum.Sponge LeanXmss HashSig

open Quantum.Xmss.Assembly (recSpec extCls)
open Quantum.Xmss.Hybrid (uavg)

attribute [local irreducible] xmssRom

theorem clsCapQ_le : clsCapQ ≤ 2 ^ 65 + 2 ^ 41 := by
  rw [clsCapQ, progCapQ, layerProgCap, verifyCalls_eq]
  norm_num [randomizerAttemptLimit, lifetime, layerCount, layerHeight, chainCount, chainLength,
    winternitzBits]

variable (A : Adversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) lifetime)
include hhash hsign

/-- The adversary calls of the challenge prefix (GameTCalls' `advCalls_prefixQ`). -/
theorem advCalls_prefixQ' (θ : HPos → Digest) :
    IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 0 else 1) q :=
  advCalls_prefixQ cwUpd A hhash hsign θ

/-- The classical calls of the challenge prefix (GameTCalls' `clsCalls_prefixQ`). -/
theorem clsCalls_prefixQ' (θ : HPos → Digest) :
    IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0) clsCapQ :=
  clsCalls_prefixQ cwUpd A hhash hsign θ

/-- **The averaged classical costs of the challenge prefix.** -/
theorem uavg_twPQ_le (hleaf : NoLeafReuse A) :
    uavg (fun θ : HPos → Digest ↦ twPQ (honQ θ) A θ) ≤
      twBoundQ q clsCapQ clsCapQ clsCapQ :=
  uavg_twPQ_le_of A (fun θ ↦ prefixInvQ A θ) (clsCalls_prefixQ' A hhash hsign)
    (fun θ ↦ encPre_le A θ (prefixInvQ A θ) (advCalls_prefixQ' A hhash hsign θ)
      (clsCalls_prefixQ' A hhash hsign θ))
    (uavg_recUPre_le' A (advCalls_prefixQ' A hhash hsign) (clsCalls_prefixQ' A hhash hsign))
    (fun θ ↦ selPre_le_small A hleaf θ (clsCalls_prefixQ' A hhash hsign θ))
    (fun θ ↦ recSPre_le A hleaf θ (clsCalls_prefixQ' A hhash hsign θ))

/-- **The averaged classical costs of the challenge prefix in closed form** (`q ≤ 2^64`):
`((0.523 · 2^17 √q + 0.708 · 2^33) / 2^64)²`. -/
theorem uavg_twPQ_le_closed (hleaf : NoLeafReuse A) (hq : q ≤ 2 ^ 64) :
    uavg (fun θ : HPos → Digest ↦ twPQ (honQ θ) A θ) ≤
      ENNReal.ofReal (((0.523 * 2 ^ 17 * √q + 0.708 * 2 ^ 33) / 2 ^ 64) ^ 2) :=
  (uavg_twPQ_le A hhash hsign hleaf).trans (twBoundQ_le hq clsCapQ_le clsCapQ_le clsCapQ_le)

end Quantum.Qrom.Xmss

end
