module

public import Quantum.Qrom.Sphincs.Costs.Ports

@[expose] public section

/-!
# The classical costs of leanSPHINCS's runtime 2: the event bound and the averaged costs

* **The event bound at the end of the challenge prefix** (`ewPrefixQ_le`): with at most `q`
  adversary calls and `K` classical calls, the weight of `BadRQ pk hon S` is at most
  `(advTermQ q S + √twPQ)²`, `advTermQ q S = q √(6 (2^-128 + price S))` (Assembly's
  `eventWeight_runtimeR_le`, Events' fresh bound, the refined read cost, programs and records as
  classical ports).
* **The averaged costs** (`uavg_twPQ_le_of`): from the per-table split of Ports' `twPQ_le`, an
  Enc bound `encPre ≤ cE (q + 4 (q + K) recUPre + (q + K) K εE)`, the averaged recorded unselected
  mass `τ`, the re-grind weights `2^-128 Sl` and the recorded hits `2^-128 R`, the average over the
  hidden values of `twPQ` (at the canonical public key and honest cells, any disclosures `Sθ θ`)
  is at most `twBoundQ cE εE q K τ Sl R = (√aCap + √pCap)²` (Jensen for `(√f + √g)²`,
  `uavg_sq_rpow_add_le`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR extWeight sumWeight extCls
  eventWeight_runtimeR_le uavg_sq_rpow_add_le uavg_const_le)
open Quantum.Xmss.Hybrid (uavg uavg_mono uavg_add uavg_const_mul)

attribute [local irreducible] sphincsRom

/-! ## The event bound at the end of the prefix -/

/-- **The fresh fraction of the event**: `2^-128` (Struct, Enc) plus the price of `S` (Cov). -/
noncomputable def epsQ (S : Quantum.Sphincs.Disclosures) : ℝ≥0∞ :=
  (2 ^ 128 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (Quantum.Sphincs.price S)

theorem epsQ_ne_top (S : Quantum.Sphincs.Disclosures) : epsQ S ≠ ⊤ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.mpr (by positivity), ENNReal.ofReal_ne_top⟩

/-- **The adversary term**: `∑_{n < q} √(6 (2^-128 + price S))`. -/
noncomputable def advTermQ (q : ℕ) (S : Quantum.Sphincs.Disclosures) : ℝ≥0∞ :=
  ∑ _n ∈ Finset.range q, (6 * epsQ S) ^ (2⁻¹ : ℝ)

/-- **The event bound at the end of the challenge prefix**: with at most `q` adversary calls and
`K` classical calls, `ew ≤ (advTermQ q S + √twPQ)²`. -/
theorem ewPrefixQ_le (pk : PublicKey) (hon : HonestCells) (S : Quantum.Sphincs.Disclosures)
    (pol : DigestPolicy) (A : SAdversary) (θ : TVals) {q K : ℕ}
    (hq : IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 0 else 1) q)
    (hK : IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0) K) :
    (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S)) (prefixQ pol A θ)
        initQ ≤
      (advTermQ q S + twPQ pk hon S pol A θ ^ (2⁻¹ : ℝ)) ^ 2 :=
  eventWeight_runtimeR_le (q := q) (K := K) (BadRQ pk hon S) (labelFree_badRQ pk hon S)
    (fun W m ↦ upClosed_slice_badRQ W m) m0Q (empty_not_mem_badRQ m0Q)
    (fun _ ↦ epsQ S) (fun _ _ ↦ epsQ_ne_top S)
    (fun _ _ W m ↦ freshBound_slice_badRQ W m _)
    (fun c σ ↦ readCostT (BadRQ pk hon S) c σ)
    (fun c σ ↦ flipCost (BadRQ pk hon S) (hwProgKraus c) 0 σ)
    (fun c σ hσ ↦ potential_hwReadKraus_le_refinedT (BadRQ pk hon S) c σ hσ)
    (fun c σ hσ ↦ potential_hwProgKraus_le (BadRQ pk hon S) (fun _ ↦ 0)
      (fun _ ↦ conjTranspose_zero) (fun _ ↦ mul_zero 0) c σ hσ)
    .instruments (prefixQ pol A θ) hq hK (SubState.basis ())

/-! ## The averaged costs -/

/-- **The Enc weights against an averaged recorded mass `τ`**: `cE (q + 4 (q + K) τ + (q + K) K εE)`
(Enc's bound at the constants `cE`, `εE`). -/
noncomputable def encCap (cE εE : ℝ≥0∞) (q K : ℕ) (τ : ℝ≥0∞) : ℝ≥0∞ :=
  cE * ((q : ℝ≥0∞) + 4 * ((q + K : ℕ) : ℝ≥0∞) * τ + ((q + K : ℕ) : ℝ≥0∞) * K * εE)

/-- **The averaged linear charge**: the Enc weights and the re-grind weights (at most
`2^-128 Sl`) at `2^-127`, and `2/|Y × Y|` per classical call. -/
noncomputable def aCap (cE εE : ℝ≥0∞) (q K : ℕ) (τ : ℝ≥0∞) (Sl : ℕ) : ℝ≥0∞ :=
  (2 ^ 127 : ℝ≥0∞)⁻¹ * (encCap cE εE q K τ + (2 ^ 128 : ℝ≥0∞)⁻¹ * Sl) +
    ENNReal.ofReal (2 / Fintype.card PairOut) * K

/-- **The averaged recorded flip mass**: `τ` and the recorded hits, `2^-128` per re-grind read
(at most `R`). -/
noncomputable def pCap (τ : ℝ≥0∞) (R : ℕ) : ℝ≥0∞ :=
  τ + (2 ^ 128 : ℝ≥0∞)⁻¹ * R

/-- **The bound on the averaged classical costs**: `(√aCap + √pCap)²`. -/
noncomputable def twBoundQ (cE εE : ℝ≥0∞) (q K : ℕ) (τ : ℝ≥0∞) (Sl R : ℕ) : ℝ≥0∞ :=
  (aCap cE εE q K τ Sl ^ (2⁻¹ : ℝ) + pCap τ R ^ (2⁻¹ : ℝ)) ^ 2

/-- **The averaged classical costs of the prefix**, from the slices' bounds: the prefix invariant,
the Enc bound per table, the averaged recorded unselected mass, the re-grind weights (at most
`2^-128 Sl`) and the recorded hits (at most `2^-128 R`) per table; any disclosures `Sθ θ`. -/
theorem uavg_twPQ_le_of (Sθ : TVals → Quantum.Sphincs.Disclosures) (pol : DigestPolicy)
    (A : SAdversary) {q K Sl R : ℕ} {cE εE τ : ℝ≥0∞}
    (hinv : ∀ θ, PrefixInvQ (pkQ θ) (honQ θ) pol A θ)
    (hK : ∀ θ, IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0) K)
    (henc : ∀ θ, encPre pol A θ ≤ encCap cE εE q K (recUPre pol A θ))
    (hU : uavg (fun θ : TVals ↦ recUPre pol A θ) ≤ τ)
    (hSel : ∀ θ, selPre pol A θ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * Sl)
    (hS : ∀ θ, recSPre pol A θ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * R) :
    uavg (fun θ : TVals ↦ twPQ (pkQ θ) (honQ θ) (Sθ θ) pol A θ) ≤ twBoundQ cE εE q K τ Sl R := by
  set c₀ : ℝ≥0∞ := ENNReal.ofReal (2 / Fintype.card PairOut) * K
  set a : TVals → ℝ≥0∞ := fun θ ↦
    (2 ^ 127 : ℝ≥0∞)⁻¹ * (encCap cE εE q K (recUPre pol A θ) + (2 ^ 128 : ℝ≥0∞)⁻¹ * Sl) + c₀
  set p : TVals → ℝ≥0∞ := fun θ ↦ recUPre pol A θ + (2 ^ 128 : ℝ≥0∞)⁻¹ * R
  have hpt : ∀ θ, twPQ (pkQ θ) (honQ θ) (Sθ θ) pol A θ ≤
      (a θ ^ (2⁻¹ : ℝ) + p θ ^ (2⁻¹ : ℝ)) ^ 2 := fun θ ↦ by
    have h1 : (2 ^ 127 : ℝ≥0∞)⁻¹ * (encPre pol A θ + selPre pol A θ) + c₀ ≤ a θ :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add (henc θ) (hSel θ)) zero_le) le_rfl
    have h2 : recUPre pol A θ + recSPre pol A θ ≤ p θ := add_le_add le_rfl (hS θ)
    exact (twPQ_le (honQ θ) (Sθ θ) pol A θ (hinv θ) (hK θ)).trans (pow_le_pow_left₀ zero_le
      (add_le_add (ENNReal.rpow_le_rpow h1 (by norm_num))
        (ENNReal.rpow_le_rpow h2 (by norm_num))) 2)
  refine (uavg_mono hpt).trans ((uavg_sq_rpow_add_le a p).trans ?_)
  have hua : uavg a ≤ aCap cE εE q K τ Sl := by
    have e : a = fun θ ↦ ((2 ^ 127 : ℝ≥0∞)⁻¹ * (cE * 4 * ((q + K : ℕ) : ℝ≥0∞))) *
        recUPre pol A θ + ((2 ^ 127 : ℝ≥0∞)⁻¹ * (cE * ((q : ℝ≥0∞) +
          ((q + K : ℕ) : ℝ≥0∞) * K * εE) + (2 ^ 128 : ℝ≥0∞)⁻¹ * Sl) + c₀) := by
      funext θ
      simp only [a, encCap]
      ring
    rw [e, uavg_add, uavg_const_mul]
    refine (add_le_add (mul_le_mul_of_nonneg_left hU zero_le) (uavg_const_le _)).trans_eq ?_
    simp only [aCap, encCap]
    ring
  have hup : uavg p ≤ pCap τ R := by
    rw [uavg_add]
    exact add_le_add hU (uavg_const_le _)
  unfold twBoundQ
  gcongr

/-! ## Towards the closed form -/

/-- `√(c² x + d²) ≤ c √x + d`. -/
theorem sqrt_sq_mul_add_sq_le' {c d x : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hx : 0 ≤ x) :
    √(c ^ 2 * x + d ^ 2) ≤ c * √x + d := by
  rw [Real.sqrt_le_left (by positivity), add_sq, mul_pow, Real.sq_sqrt hx]
  nlinarith [Real.sqrt_nonneg x, mul_nonneg (mul_nonneg hc hd) (Real.sqrt_nonneg x)]

/-- **The closed form from square bounds**: `aCap ≤ c₁² q + a₀²` and `pCap ≤ c₂² q + p₀²` give
`twBoundQ ≤ ((c₁ + c₂) √q + a₀ + p₀)²`. -/
theorem twBoundQ_le_of {cE εE τ : ℝ≥0∞} {q K Sl R : ℕ} {c₁ c₂ a₀ p₀ : ℝ} (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (ha₀ : 0 ≤ a₀) (hp₀ : 0 ≤ p₀)
    (ha : aCap cE εE q K τ Sl ≤ ENNReal.ofReal (c₁ ^ 2 * q + a₀ ^ 2))
    (hp : pCap τ R ≤ ENNReal.ofReal (c₂ ^ 2 * q + p₀ ^ 2)) :
    twBoundQ cE εE q K τ Sl R ≤ ENNReal.ofReal (((c₁ + c₂) * √q + a₀ + p₀) ^ 2) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have ha' : aCap cE εE q K τ Sl ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (c₁ * √q + a₀) := by
    refine (ENNReal.rpow_le_rpow ha (by norm_num)).trans ?_
    rw [ENNReal.ofReal_rpow_inv_two]
    exact ENNReal.ofReal_le_ofReal (sqrt_sq_mul_add_sq_le' hc₁ ha₀ hq0)
  have hp' : pCap τ R ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (c₂ * √q + p₀) := by
    refine (ENNReal.rpow_le_rpow hp (by norm_num)).trans ?_
    rw [ENNReal.ofReal_rpow_inv_two]
    exact ENNReal.ofReal_le_ofReal (sqrt_sq_mul_add_sq_le' hc₂ hp₀ hq0)
  unfold twBoundQ
  refine (pow_le_pow_left₀ zero_le (add_le_add ha' hp') 2).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_pow (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

end Quantum.Qrom.Sphincs

end
