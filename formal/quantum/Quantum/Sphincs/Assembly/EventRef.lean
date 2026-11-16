module

public import Quantum.Sphincs.Assembly.EventSqrt
public import Quantum.Sphincs.Assembly.CostRefined

@[expose] public section

/-!
# leanSPHINCS's event bound with the refined read cost

leanXMSS's `ewPrefix_le_ref` and `ewR_le_sqrt_ref` (`Quantum.Xmss.Assembly.CostRefined`) on
GameR's canonical game `gameR pol A p v` at template data `(p, v)` (contract C4), for every digest
policy, with the event `Bad (evData p v) progCap` (CostRun's `BadR`).

* **The prefix** (`ewPrefix_le_ref`): leanXMSS's `eventWeight_runtimeR_le` with GameR's fresh
  bounds `advEps v n` (`freshBound_slice_badR`), the read ports priced with ReadCost's refined cost
  (`potential_hwReadKraus_le_refinedT`, CostRefined's `dRref`), the program ports with CostRun's
  `dPof`: at `PermGood π 18`, the prefix's event weight is at most `(advTerm v q + √twPR)²`.
* **The game** (`ewR_le_sqrt_ref_sph`): EventSqrt's `ewR_le_sqrt_sph` at `T = twPR`:
  `ewR ≤ (advTerm v q + verTerm v q + √(twPR + verLin v q))²`.
* **The fresh bounds at Keccak sizes** (`capRate_le_keccak`, `advEps_le_keccak`,
  `verEps_le_keccak`): for `q ≤ 2^64` every database grade involved is below `2^68`
  (`verEntries_le_sph`: `progCap + 6q + clsCap + 3 verifyBlocks + 2 ≤ 2^68`), so the capacity rate
  is at most `2^-302` and `advEps v n`, `verEps v q ≤ 2^-128 + 2 · 2^-302 + 2^16 price S★(v)`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open Quantum.Xmss (X Z)
open Quantum.Xmss.Assembly (runtimeR eventWeight_runtimeR_le natCast_div_le_inv_two_pow card_Z)

namespace Quantum.Sphincs.Assembly

/-! ## The fresh bounds at Keccak sizes -/

section numbers

/-- The entries below which the verification's fresh bound is taken: below `2^68` for
`q ≤ 2^64`. -/
theorem verEntries_le_sph {q : ℕ} (hq : q ≤ 2 ^ 64) :
    progCap + (6 * q + clsCap + 3 * verifyBlocks + 1) + 1 ≤ 2 ^ 68 := by
  have hc : progCap + clsCap + 3 * verifyBlocks + 2 ≤ 2 ^ 68 - 6 * 2 ^ 64 := by
    rw [clsCap_eq, progCap_eq, verifyBlocks_eq]
    norm_num [signatureLimit]
  omega

/-- The entries below which the `n`-th adversary call's fresh bound is taken: below `2^68` for
`n < 6q`, `q ≤ 2^64`. -/
theorem advEntries_le_sph {q n : ℕ} (hq : q ≤ 2 ^ 64) (hn : n < 6 * q) :
    progCap + (n + clsCap + 1) + 1 ≤ 2 ^ 68 :=
  le_trans (by omega) (verEntries_le_sph hq)

set_option exponentiation.threshold 1100 in
/-- **The capacity rate at Keccak sizes**: `capRate T 18 ≤ 2^-302` below `2^68` entries
(`3 · 18 (T+1)³ / 2^512`). -/
theorem capRate_le_keccak {T : ℕ} (hT : T + 1 ≤ 2 ^ 68) : capRate T 18 ≤ (2 ^ 302 : ℝ≥0∞)⁻¹ := by
  have hc : 3 * 18 * (T + 1) ^ 3 * 2 ^ 302 ≤ 2 ^ 512 :=
    calc 3 * 18 * (T + 1) ^ 3 * 2 ^ 302 ≤ 3 * 18 * (2 ^ 68) ^ 3 * 2 ^ 302 := by gcongr
      _ ≤ 2 ^ 6 * (2 ^ 68) ^ 3 * 2 ^ 302 := by gcongr; norm_num
      _ = 2 ^ 512 := by rw [← pow_mul, ← pow_add, ← pow_add]
  unfold capRate
  rw [card_Z]
  refine max_le (natCast_div_le_inv_two_pow ?_) (natCast_div_le_inv_two_pow ?_)
  · exact le_trans (Nat.mul_le_mul_right _ (rateK_le T 18)) hc
  · exact le_trans (Nat.mul_le_mul_right _ (rateK'_le (by norm_num) T)) hc

/-- **The adversary's fresh bound at Keccak sizes**: for `n < 6q`, `q ≤ 2^64`,
`advEps v n ≤ 2^-128 + 2 · 2^-302 + 2^16 price S★(v)`. -/
theorem advEps_le_keccak (v : (s : HPos) → XD s) {q n : ℕ} (hq : q ≤ 2 ^ 64) (hn : n < 6 * q) :
    advEps v n ≤ (2 ^ 128)⁻¹ + 2 * (2 ^ 302 : ℝ≥0∞)⁻¹ +
      ENNReal.ofReal ((2 ^ 16 * price (coverOf v) : ℚ) : ℝ) :=
  (advEps_le v n).trans (by gcongr; exact capRate_le_keccak (advEntries_le_sph hq hn))

/-- **The verification's fresh bound at Keccak sizes**: for `q ≤ 2^64`,
`verEps v q ≤ 2^-128 + 2 · 2^-302 + 2^16 price S★(v)`. -/
theorem verEps_le_keccak (v : (s : HPos) → XD s) {q : ℕ} (hq : q ≤ 2 ^ 64) :
    verEps v q ≤ (2 ^ 128)⁻¹ + 2 * (2 ^ 302 : ℝ≥0∞)⁻¹ +
      ENNReal.ofReal ((2 ^ 16 * price (coverOf v) : ℚ) : ℝ) :=
  (verEps_le v q).trans (by gcongr; exact capRate_le_keccak (verEntries_le_sph hq))

end numbers

/-! ## The event bound with the refined read cost -/

section event

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

set_option synthInstance.maxSize 2000 in
/-- **The event bound at the end of the challenge prefix, with the refined read cost**
(`eventWeight_runtimeR_le` with ReadCost's `potential_hwReadKraus_le_refinedT`): at data with
`PermGood π 18`, for every digest policy, the prefix's event weight is at most
`(advTerm v q + √twPR)²`. -/
theorem ewPrefix_le_ref (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) :
    (runtimeR m0R).eventWeight .instruments (hwProjector (BadR p v progCap)) (prefixR pol A p v)
        initR ≤
      (advTerm v q + twPR pol A p v ^ (2⁻¹ : ℝ)) ^ 2 :=
  eventWeight_runtimeR_le (q := 6 * q) (K := clsCap) (BadR p v progCap)
    (labelFree_badR p v progCap)
    (fun W m ↦ upClosed_slice_bad (d := evData p v) (N := progCap) W m) m0R
    (not_mem_bad_empty (d := evData p v) (N := progCap) m0R) (advEps v)
    (fun n _ ↦ advEps_ne_top v n)
    (fun n _ W m ↦ freshBound_slice_badR p v hπ (n + clsCap + 1) W m)
    (dRref p v) (dPof p v)
    (fun c σ hσ ↦ potential_hwReadKraus_le_refinedT (BadR p v progCap) c σ hσ)
    (fun c σ hσ ↦ potential_hwProgKraus_le (BadR p v progCap) (fun _ ↦ 0)
      (fun _ ↦ conjTranspose_zero) (fun _ ↦ mul_zero 0) c σ hσ)
    .instruments (prefixR pol A p v) (advCalls_prefixR hperm hsign pol p v)
    (clsCalls_prefixR hperm hsign pol p v) (SubState.basis ())

set_option synthInstance.maxSize 2000 in
/-- **The event bound over the whole game with the refined read cost** (EventSqrt's
`ewR_le_sqrt_sph` at `T = twPR`, `ewPrefix_le_ref`): at data with `PermGood π 18`, for every
digest policy, `ewR ≤ (advTerm v q + verTerm v q + √(twPR + verLin v q))²`. -/
theorem ewR_le_sqrt_ref_sph (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) :
    ewR p v (gameR pol A p v) ≤
      (advTerm v q + verTerm v q + (twPR pol A p v + verLin v q) ^ (2⁻¹ : ℝ)) ^ 2 :=
  @ewR_le_sqrt_sph q A hperm hsign pol p v (badRDec p v progCap) hπ (twPR pol A p v)
    (ewPrefix_le_ref hperm hsign pol p v hπ)

end event

end Quantum.Sphincs.Assembly

end
