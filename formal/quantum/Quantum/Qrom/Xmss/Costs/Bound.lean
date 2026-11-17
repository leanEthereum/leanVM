module

public import Quantum.Qrom.Xmss.Costs.Ports

@[expose] public section

/-!
# The classical costs of runtime 2: the event bound and the averaged costs

* **The event bound at the end of the challenge prefix** (`ewPrefixQ_le`): with at most `q`
  adversary calls and `K` classical calls, the weight of `BadRQ hon` is at most
  `(advTermQ q + √twPQ)²`, `advTermQ q = q √(6 · 2^-128)` (Assembly's `eventWeight_runtimeR_le`,
  fresh bound `2^-128`, the refined read cost, programs and records as classical ports).
* **The averaged costs** (`uavg_twPQ_le_of`): from the per-table split of Ports' `twPQ_le`, the
  Enc bound (linear in the recorded unselected mass), the averaged recorded unselected mass `tauU`,
  the re-grind weights `2^-128 S` and the recorded hits `2^-128 R`, the average over the hidden
  values of `twPQ (honQ θ) A θ` is at most `twBoundQ q K S R = (√aCap + √pCap)²` (Jensen for
  `(√f + √g)²`, `uavg_sq_rpow_add_le`); in closed form `twBoundQ_le`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR extWeight sumWeight extCls
  eventWeight_runtimeR_le uavg_sq_rpow_add_le uavg_const_le)
open Quantum.Xmss.Hybrid (uavg uavg_mono uavg_add uavg_const_mul totalWeight_le_totalWeight)

attribute [local irreducible] xmssRom

/-! ## The event bound at the end of the prefix -/

/-- **The adversary term**: `∑_{n < q} √(6 · 2^-128)`. -/
noncomputable def advTermQ (q : ℕ) : ℝ≥0∞ :=
  ∑ _n ∈ Finset.range q, (6 * (2 ^ 128 : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)

/-- **The event bound at the end of the challenge prefix**: with at most `q` adversary calls and
`K` classical calls, `ew ≤ (advTermQ q + √twPQ)²`. -/
theorem ewPrefixQ_le (hon : HonestCells) (A : Adversary) (θ : HPos → Digest) {q K : ℕ}
    (hq : IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 0 else 1) q)
    (hK : IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0) K) :
    (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon)) (prefixQ A θ) initQ ≤
      (advTermQ q + twPQ hon A θ ^ (2⁻¹ : ℝ)) ^ 2 :=
  eventWeight_runtimeR_le (q := q) (K := K) (BadRQ hon) (labelFree_badRQ hon)
    (fun W m ↦ upClosed_slice_badRQ W m) m0Q (empty_not_mem_badRQ m0Q)
    (fun _ ↦ (2 ^ 128 : ℝ≥0∞)⁻¹) (fun _ _ ↦ ENNReal.inv_ne_top.mpr (by positivity))
    (fun _ _ W m ↦ freshBound_slice_badRQ W m _)
    (fun c σ ↦ readCostT (BadRQ hon) c σ) (fun c σ ↦ flipCost (BadRQ hon) (hwProgKraus c) 0 σ)
    (fun c σ hσ ↦ potential_hwReadKraus_le_refinedT (BadRQ hon) c σ hσ)
    (fun c σ hσ ↦ potential_hwProgKraus_le (BadRQ hon) (fun _ ↦ 0)
      (fun _ ↦ conjTranspose_zero) (fun _ ↦ mul_zero 0) c σ hσ)
    .instruments (prefixQ A θ) hq hK (SubState.basis ())

/-! ## The averaged costs -/

/-- **The averaged recorded unselected mass** (RecU's `uavg_recUPre_le'`): the first reveals,
`2^32` bases per adversary entry out of `2^128`, and the failed searches. -/
noncomputable def tauU (q K : ℕ) : ℝ≥0∞ :=
  q * 2 ^ 32 * (2 ^ 128 : ℝ≥0∞)⁻¹ + K * (2 ^ 1000 : ℝ≥0∞)⁻¹

/-- **The Enc weights against an averaged recorded mass `τ`** (Enc's `encPre_le`). -/
noncomputable def encCap (q K : ℕ) (τ : ℝ≥0∞) : ℝ≥0∞ :=
  2 ^ 22 * ((q : ℝ≥0∞) + 4 * ((q + K : ℕ) : ℝ≥0∞) * τ +
    ((q + K : ℕ) : ℝ≥0∞) * K * (2 ^ 250 : ℝ≥0∞)⁻¹)

/-- **The averaged linear charge**: the Enc weights and the re-grind weights (at most
`2^-128 S`) at `2^-127`, and `2/|Y|` per classical call. -/
noncomputable def aCap (q K S : ℕ) : ℝ≥0∞ :=
  (2 ^ 127 : ℝ≥0∞)⁻¹ * (encCap q K (tauU q K) + (2 ^ 128 : ℝ≥0∞)⁻¹ * S) +
    ENNReal.ofReal (2 / Fintype.card HashOutput) * K

/-- **The averaged recorded flip mass**: `tauU` and the recorded hits, `2^-128` per re-grind
read (at most `R`). -/
noncomputable def pCap (q K R : ℕ) : ℝ≥0∞ :=
  tauU q K + (2 ^ 128 : ℝ≥0∞)⁻¹ * R

/-- **The bound on the averaged classical costs**: `(√aCap + √pCap)²`. -/
noncomputable def twBoundQ (q K S R : ℕ) : ℝ≥0∞ :=
  (aCap q K S ^ (2⁻¹ : ℝ) + pCap q K R ^ (2⁻¹ : ℝ)) ^ 2

/-- **The averaged classical costs of the prefix**, from the slices' bounds: the prefix
invariant, the Enc bound per table, the averaged recorded unselected mass, the re-grind weights
(at most `2^-128 S`, RegrindSel's `selPre_le_small`) and the recorded hits (at most `2^-128 R`) per
table. -/
theorem uavg_twPQ_le_of (A : Adversary) {q K S R : ℕ}
    (hinv : ∀ θ, PrefixInvQ (honQ θ) A θ)
    (hK : ∀ θ, IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0) K)
    (henc : ∀ θ, encPre A θ ≤ 2 ^ 22 * ((q : ℝ≥0∞) + 4 * ((q + K : ℕ) : ℝ≥0∞) * recUPre A θ +
      ((q + K : ℕ) : ℝ≥0∞) * K * (2 ^ 250 : ℝ≥0∞)⁻¹))
    (hU : uavg (fun θ : HPos → Digest ↦ recUPre A θ) ≤ tauU q K)
    (hSel : ∀ θ, selPre A θ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * S)
    (hS : ∀ θ, recSPre A θ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * R) :
    uavg (fun θ : HPos → Digest ↦ twPQ (honQ θ) A θ) ≤ twBoundQ q K S R := by
  set c₀ : ℝ≥0∞ := ENNReal.ofReal (2 / Fintype.card HashOutput) * K
  set a : (HPos → Digest) → ℝ≥0∞ := fun θ ↦
    (2 ^ 127 : ℝ≥0∞)⁻¹ * (encCap q K (recUPre A θ) + (2 ^ 128 : ℝ≥0∞)⁻¹ * S) + c₀
  set p : (HPos → Digest) → ℝ≥0∞ := fun θ ↦ recUPre A θ + (2 ^ 128 : ℝ≥0∞)⁻¹ * R
  have hpt : ∀ θ, twPQ (honQ θ) A θ ≤ (a θ ^ (2⁻¹ : ℝ) + p θ ^ (2⁻¹ : ℝ)) ^ 2 := fun θ ↦ by
    have h1 : (2 ^ 127 : ℝ≥0∞)⁻¹ * (encPre A θ + selPre A θ) + c₀ ≤ a θ :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add (henc θ) (hSel θ)) zero_le) le_rfl
    have h2 : recUPre A θ + recSPre A θ ≤ p θ := add_le_add le_rfl (hS θ)
    exact (twPQ_le (honQ θ) A θ (hinv θ) (hK θ)).trans (pow_le_pow_left₀ zero_le
      (add_le_add (ENNReal.rpow_le_rpow h1 (by norm_num))
        (ENNReal.rpow_le_rpow h2 (by norm_num))) 2)
  refine (uavg_mono hpt).trans ((uavg_sq_rpow_add_le a p).trans ?_)
  have hua : uavg a ≤ aCap q K S := by
    have e : a = fun θ ↦ ((2 ^ 127 : ℝ≥0∞)⁻¹ * (2 ^ 22 * 4 * ((q + K : ℕ) : ℝ≥0∞))) *
        recUPre A θ + ((2 ^ 127 : ℝ≥0∞)⁻¹ * (2 ^ 22 * ((q : ℝ≥0∞) +
          ((q + K : ℕ) : ℝ≥0∞) * K * (2 ^ 250 : ℝ≥0∞)⁻¹) + (2 ^ 128 : ℝ≥0∞)⁻¹ * S) + c₀) := by
      funext θ
      simp only [a, encCap]
      ring
    rw [e, uavg_add, uavg_const_mul]
    refine (add_le_add (mul_le_mul_of_nonneg_left hU zero_le) (uavg_const_le _)).trans_eq ?_
    simp only [aCap, encCap]
    ring
  have hup : uavg p ≤ pCap q K R := by
    rw [uavg_add]
    exact add_le_add hU (uavg_const_le _)
  unfold twBoundQ
  gcongr

/-! ## The closed form -/

/-- `tauU` as a real number. -/
noncomputable def tauR (q K : ℕ) : ℝ :=
  q * 2 ^ 32 * (2 ^ 128)⁻¹ + K * (2 ^ 1000)⁻¹

/-- `aCap` as a real number. -/
noncomputable def aR (q K S : ℕ) : ℝ :=
  (2 ^ 127)⁻¹ * (2 ^ 22 * ((q : ℝ) + 4 * ((q + K : ℕ) : ℝ) * tauR q K +
    ((q + K : ℕ) : ℝ) * K * (2 ^ 250)⁻¹) + (2 ^ 128)⁻¹ * S) + 2 / Fintype.card HashOutput * K

/-- `pCap` as a real number. -/
noncomputable def pR (q K R : ℕ) : ℝ :=
  tauR q K + (2 ^ 128)⁻¹ * R

theorem tauR_nonneg (q K : ℕ) : 0 ≤ tauR q K := by
  unfold tauR
  positivity

/-- Rewrite `ENNReal.ofReal` of a nonnegative arithmetic expression into `ℝ≥0∞` arithmetic. -/
macro "ofReal_push" : tactic => `(tactic| (
  repeat (first
    | rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    | rw [ENNReal.ofReal_mul (by positivity)]
    | rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    | rw [ENNReal.ofReal_pow (by norm_num)])
  simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]))

theorem tauU_eq (q K : ℕ) : tauU q K = ENNReal.ofReal (tauR q K) := by
  rw [tauU, tauR]
  ofReal_push

theorem aCap_eq (q K S : ℕ) : aCap q K S = ENNReal.ofReal (aR q K S) := by
  rw [aCap, encCap, tauU, aR, tauR]
  ofReal_push

theorem pCap_eq (q K R : ℕ) : pCap q K R = ENNReal.ofReal (pR q K R) := by
  rw [pCap, tauU, pR, tauR]
  ofReal_push

/-- `√(a + b) ≤ √a + √b`. -/
theorem sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  rw [Real.sqrt_le_left (by positivity), add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- `√(c² x + d²) ≤ c √x + d`. -/
theorem sqrt_sq_mul_add_sq_le {c d x : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hx : 0 ≤ x) :
    √(c ^ 2 * x + d ^ 2) ≤ c * √x + d := by
  refine (sqrt_add_le_add_sqrt (by positivity) (by positivity)).trans_eq ?_
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc, Real.sqrt_sq hd]

set_option exponentiation.threshold 2048 in
/-- **The linear charge, numerically**: for `q ≤ 2^64`, `K ≤ 2^65 + 2^41`,
`aR ≤ (0.7072 · 2^-52)² q + 2^-255 S + 2^-188`. -/
theorem aR_le {q K S : ℕ} (hq : q ≤ 2 ^ 64) (hK : K ≤ 2 ^ 65 + 2 ^ 41) :
    aR q K S ≤ (0.7072 * (2 ^ 52)⁻¹) ^ 2 * q + ((2 ^ 255)⁻¹ * S + (2 ^ 188)⁻¹) := by
  have hqR : (q : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hq
  have hKR : (K : ℝ) ≤ 2 ^ 65 + 2 ^ 41 := by exact_mod_cast hK
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hqK : ((q + K : ℕ) : ℝ) ≤ 2 ^ 66 := by push_cast; linarith
  have hqK0 : (0 : ℝ) ≤ ((q + K : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht0 := tauR_nonneg q K
  have ht : tauR q K ≤ (2 ^ 96)⁻¹ * q + 2 ^ 66 * (2 ^ 1000)⁻¹ := by
    unfold tauR
    have : (K : ℝ) * (2 ^ 1000)⁻¹ ≤ 2 ^ 66 * (2 ^ 1000)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e : (q : ℝ) * 2 ^ 32 * (2 ^ 128)⁻¹ = (2 ^ 96)⁻¹ * q := by ring
    linarith
  have h2 : ((q + K : ℕ) : ℝ) * tauR q K ≤ 2 ^ 66 * tauR q K :=
    mul_le_mul_of_nonneg_right hqK ht0
  have h3 : ((q + K : ℕ) : ℝ) * K ≤ 2 ^ 66 * 2 ^ 66 :=
    mul_le_mul hqK (by linarith) hK0 (by positivity)
  have hc : (2 : ℝ) / Fintype.card HashOutput = 2 * (2 ^ 256)⁻¹ := by
    rw [card_hashOutput, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
  unfold aR
  rw [hc]
  nlinarith

set_option exponentiation.threshold 2048 in
/-- **The recorded flip mass, numerically**: `pR ≤ (2^-48)² q + 2^-128 R + 2^-900`. -/
theorem pR_le {q K R : ℕ} (hK : K ≤ 2 ^ 65 + 2 ^ 41) :
    pR q K R ≤ ((2 ^ 48)⁻¹) ^ 2 * q + ((2 ^ 128)⁻¹ * R + (2 ^ 900)⁻¹) := by
  have hKR : (K : ℝ) ≤ 2 ^ 65 + 2 ^ 41 := by exact_mod_cast hK
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  unfold pR tauR
  nlinarith

/-- **The closed form from square bounds**: `aR ≤ c₁² q + a₀²` and `pR ≤ c₂² q + p₀²` give
`twBoundQ ≤ ((c₁ + c₂) √q + a₀ + p₀)²`. -/
theorem twBoundQ_le_of {q K S R : ℕ} {c₁ c₂ a₀ p₀ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (ha₀ : 0 ≤ a₀) (hp₀ : 0 ≤ p₀) (ha : aR q K S ≤ c₁ ^ 2 * q + a₀ ^ 2)
    (hp : pR q K R ≤ c₂ ^ 2 * q + p₀ ^ 2) :
    twBoundQ q K S R ≤ ENNReal.ofReal (((c₁ + c₂) * √q + a₀ + p₀) ^ 2) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have ha' := (Real.sqrt_le_sqrt ha).trans (sqrt_sq_mul_add_sq_le hc₁ ha₀ hq0)
  have hp' := (Real.sqrt_le_sqrt hp).trans (sqrt_sq_mul_add_sq_le hc₂ hp₀ hq0)
  have hsum : √(aR q K S) + √(pR q K R) ≤ (c₁ + c₂) * √q + a₀ + p₀ := by linarith
  unfold twBoundQ
  rw [aCap_eq, pCap_eq, ENNReal.ofReal_rpow_inv_two, ENNReal.ofReal_rpow_inv_two,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_pow (by positivity)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hsum 2)

set_option exponentiation.threshold 2048 in
/-- **The closed form**: for `q ≤ 2^64` and `K, S, R ≤ 2^65 + 2^41`,
`twBoundQ ≤ ((0.523 · 2^17 √q + 0.708 · 2^33) / 2^64)²` (`0.523 < 2^-0.934`,
`0.708 < 2^-0.497`). -/
theorem twBoundQ_le {q K S R : ℕ} (hq : q ≤ 2 ^ 64) (hK : K ≤ 2 ^ 65 + 2 ^ 41)
    (hS : S ≤ 2 ^ 65 + 2 ^ 41) (hR : R ≤ 2 ^ 65 + 2 ^ 41) :
    twBoundQ q K S R ≤
      ENNReal.ofReal (((0.523 * 2 ^ 17 * √q + 0.708 * 2 ^ 33) / 2 ^ 64) ^ 2) := by
  have hSR : (S : ℝ) ≤ 2 ^ 65 + 2 ^ 41 := by exact_mod_cast hS
  have hRR : (R : ℝ) ≤ 2 ^ 65 + 2 ^ 41 := by exact_mod_cast hR
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  refine (twBoundQ_le_of (c₁ := 0.7072 * (2 ^ 52)⁻¹) (c₂ := (2 ^ 48)⁻¹)
    (a₀ := (2 ^ 93)⁻¹) (p₀ := 0.7072 * (2 ^ 31)⁻¹) (by positivity) (by positivity)
    (by positivity) (by positivity) ((aR_le hq hK).trans ?_) ((pR_le hK).trans ?_)).trans ?_
  · nlinarith
  · nlinarith
  · refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 2)
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg (q : ℝ)]

end Quantum.Qrom.Xmss

end
