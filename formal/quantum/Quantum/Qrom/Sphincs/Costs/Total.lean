module

public import Quantum.Qrom.Sphincs.Costs.Bound
public import Quantum.Qrom.Sphincs.Costs.PrefixInv
public import Quantum.Qrom.Sphincs.Costs.Enc
public import Quantum.Qrom.Sphincs.Costs.RecU
public import Quantum.Qrom.Sphincs.Costs.Regrind
public import Quantum.Qrom.Sphincs.Costs.RegrindSel
public import Quantum.Qrom.Sphincs.GameTCalls

@[expose] public section

/-!
# The classical costs of leanSPHINCS's runtime 2: the final bound

For an adversary with at most `q` hash calls and `signatureLimit` signing requests, a digest
policy revealing no value coordinate, and any disclosures `Sθ θ` of the event:

* `clsCapQ_le`: the classical calls of the game, `clsCapQ ≤ 0.826 · 2^64`;
* `uavg_twPQ_le`: averaged over the hidden values, the classical costs of the challenge prefix
  are at most `twBoundQ encC encEps q clsCapQ (tauU q clsCapQ) clsCapQ clsCapQ` (PrefixInv's
  `prefixInvQ`, Enc's `encPre_le`, RecU's `uavg_recUPre_le`, RegrindSel's `selPre_le_small`,
  Regrind's `recSPre_le`, GameTCalls' call counts); no adversary hypothesis beyond the counts;
* `twBoundQ_le_closed`, `twBoundQ_clsCap_le`, `uavg_twPQ_le_closed`: for `q ≤ 2^64`, at most
  `((257.3 √q + 0.909 · 2^32) / 2^64)²`. The floor `0.909 · 2^32` is the recorded re-grind hits,
  `2^-128` per classical call.
-/

open IPFunctor
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum Quantum.Sponge
open Quantum.Xmss.Assembly (recSpec extCls)
open Quantum.Xmss.Hybrid (uavg)

attribute [local irreducible] sphincsRom

/-- The classical calls of the game: `clsCapQ ≤ 0.826 · 2^64` (about `2^63.72`). -/
theorem clsCapQ_le : (clsCapQ : ℝ) ≤ 0.826 * 2 ^ 64 := by
  rw [clsCapQ_eq]
  norm_num [signatureLimit]

theorem clsCapQ_le_two_pow : clsCapQ ≤ 2 ^ 64 := by
  have h := clsCapQ_le
  have h' : (clsCapQ : ℝ) ≤ 2 ^ 64 := h.trans (by norm_num)
  exact_mod_cast h'

/-! ## The closed form -/

theorem card_pairOut_real : (Fintype.card PairOut : ℝ) = 2 ^ 256 * 2 ^ 256 := by
  rw [Fintype.card_prod, Quantum.Qrom.Xmss.card_hashOutput]
  push_cast
  ring

/-- Rewrite `ENNReal.ofReal` of a nonnegative arithmetic expression into `ℝ≥0∞` arithmetic. -/
macro "ofReal_pushS" : tactic => `(tactic| (
  repeat (first
    | rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    | rw [ENNReal.ofReal_mul (by positivity)]
    | rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    | rw [ENNReal.ofReal_pow (by norm_num)])
  simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]))

/-- The recorded unselected mass in the form RecU gives: `cU q 2^-128 + K 2^-200`. -/
noncomputable def tauS (cU q K : ℕ) : ℝ≥0∞ :=
  cU * q * (2 ^ 128 : ℝ≥0∞)⁻¹ + K * (2 ^ 200 : ℝ≥0∞)⁻¹

/-- `aCap` at `tauS`, over the reals. -/
noncomputable def aRS (cU q K : ℕ) : ℝ :=
  (2 ^ 127)⁻¹ * (2 ^ 15 * ((q : ℝ) + 4 * ((q + K : ℕ) : ℝ) * (cU * q * (2 ^ 128)⁻¹ +
    K * (2 ^ 200)⁻¹) + ((q + K : ℕ) : ℝ) * K * (2 ^ 510)⁻¹) + (2 ^ 128)⁻¹ * K) +
    2 / Fintype.card PairOut * K

theorem aCap_tauS_eq (cU q K : ℕ) :
    aCap encC encEps q K (tauS cU q K) K = ENNReal.ofReal (aRS cU q K) := by
  rw [aCap, encCap, encC, encEps, tauS, aRS]
  ofReal_pushS

theorem pCap_tauS_eq (cU q K : ℕ) :
    pCap (tauS cU q K) K = ENNReal.ofReal (cU * q * (2 ^ 128)⁻¹ + K * (2 ^ 200)⁻¹ +
      (2 ^ 128)⁻¹ * K) := by
  rw [pCap, tauS]
  ofReal_pushS

set_option exponentiation.threshold 2048 in
theorem aRS_le {cU q K : ℕ} (hcU : cU ≤ 256) (hq : q ≤ 2 ^ 64) (hK : K ≤ 2 ^ 64) :
    aRS cU q K ≤ (1.001 * (2 ^ 56)⁻¹) ^ 2 * q + ((2 ^ 89)⁻¹) ^ 2 := by
  have hqR : (q : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hq
  have hKR : (K : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hK
  have hcR : (cU : ℝ) ≤ 256 := by exact_mod_cast hcU
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hc0 : (0 : ℝ) ≤ cU := Nat.cast_nonneg cU
  have hqK : ((q + K : ℕ) : ℝ) ≤ 2 ^ 65 := by push_cast; linarith
  have hqK0 : (0 : ℝ) ≤ ((q + K : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((q + K : ℕ) : ℝ) * ((cU : ℝ) * q) ≤ 2 ^ 65 * (256 * q) :=
    mul_le_mul hqK (mul_le_mul_of_nonneg_right hcR hq0) (by positivity) (by positivity)
  have h2 : ((q + K : ℕ) : ℝ) * K ≤ 2 ^ 65 * 2 ^ 64 := mul_le_mul hqK hKR hK0 (by positivity)
  have hc : (2 : ℝ) / Fintype.card PairOut = 2 * (2 ^ 512)⁻¹ := by
    rw [card_pairOut_real, div_eq_mul_inv]
    norm_num
  unfold aRS
  rw [hc]
  nlinarith

set_option exponentiation.threshold 2048 in
theorem pRS_le {cU q K : ℕ} (hK : (K : ℝ) ≤ 0.826 * 2 ^ 64) :
    (cU : ℝ) * q * (2 ^ 128)⁻¹ + K * (2 ^ 200)⁻¹ + (2 ^ 128)⁻¹ * K ≤
      (√(cU : ℝ) * (2 ^ 64)⁻¹) ^ 2 * q + (0.9089 * (2 ^ 32)⁻¹) ^ 2 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg cU)]
  nlinarith

set_option exponentiation.threshold 2048 in
/-- **The closed form of the averaged costs**: for `q ≤ 2^64`, `K ≤ 0.826 · 2^64` and a recorded
unselected mass `τ ≤ cU q 2^-128 + K 2^-200` with `cU ≤ 256`,
`twBoundQ ≤ (((256.3 + √cU) √q + 0.909 · 2^32) / 2^64)²`. -/
theorem twBoundQ_le_closed {cU q K : ℕ} {τ : ℝ≥0∞} (hcU : cU ≤ 256) (hq : q ≤ 2 ^ 64)
    (hK : (K : ℝ) ≤ 0.826 * 2 ^ 64) (hτ : τ ≤ tauS cU q K) :
    twBoundQ encC encEps q K τ K K ≤
      ENNReal.ofReal ((((256.3 + √(cU : ℝ)) * √q + 0.909 * 2 ^ 32) / 2 ^ 64) ^ 2) := by
  have hKn : K ≤ 2 ^ 64 := by
    have : (K : ℝ) ≤ 2 ^ 64 := hK.trans (by norm_num)
    exact_mod_cast this
  have hmono : twBoundQ encC encEps q K τ K K ≤ twBoundQ encC encEps q K (tauS cU q K) K K := by
    unfold twBoundQ aCap encCap pCap
    gcongr
  refine hmono.trans ((twBoundQ_le_of (c₁ := 1.001 * (2 ^ 56)⁻¹) (c₂ := √(cU : ℝ) * (2 ^ 64)⁻¹)
    (a₀ := (2 ^ 89)⁻¹) (p₀ := 0.9089 * (2 ^ 32)⁻¹) (by positivity) (by positivity)
    (by positivity) (by positivity) ?_ ?_).trans ?_)
  · rw [aCap_tauS_eq]
    exact ENNReal.ofReal_le_ofReal (aRS_le hcU hq hKn)
  · rw [pCap_tauS_eq]
    exact ENNReal.ofReal_le_ofReal (pRS_le hK)
  · refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 2)
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg (q : ℝ), Real.sqrt_nonneg (cU : ℝ),
      mul_nonneg (Real.sqrt_nonneg (cU : ℝ)) (Real.sqrt_nonneg (q : ℝ))]

/-- **The closed form of the bound** at the game's classical calls (`q ≤ 2^64`):
`twBoundQ ≤ ((257.3 √q + 0.909 · 2^32) / 2^64)²`. -/
theorem twBoundQ_clsCap_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    twBoundQ encC encEps q clsCapQ (tauU q clsCapQ) clsCapQ clsCapQ ≤
      ENNReal.ofReal (((257.3 * √q + 0.909 * 2 ^ 32) / 2 ^ 64) ^ 2) := by
  have h := twBoundQ_le_closed (cU := 1) (τ := tauU q clsCapQ) (by norm_num) hq clsCapQ_le
    (tauU_le q clsCapQ)
  rw [Nat.cast_one, Real.sqrt_one] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

section calls

variable (pol : DigestPolicy) (A : SAdversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge)
    signatureLimit)
include hhash hsign

/-- The classical calls of the challenge prefix (GameTCalls' `clsCalls_prefixT`). -/
theorem clsCalls_prefixQ' (θ : TVals) :
    IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0) clsCapQ :=
  clsCalls_prefixT cwUpd pol A hhash hsign θ

end calls

/-- **The averaged classical costs of the challenge prefix**, for any disclosures `Sθ θ` of the
event and a digest policy revealing no value coordinate (`strPol`: `noVal_strPol`). -/
theorem uavg_twPQ_le (Sθ : TVals → Quantum.Sphincs.Disclosures) (pol : DigestPolicy)
    (hpol : pol.NoVal) (A : SAdversary) {q : ℕ}
    (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge)
      signatureLimit) :
    uavg (fun θ : TVals ↦ twPQ (pkQ θ) (honQ θ) (Sθ θ) pol A θ) ≤
      twBoundQ encC encEps q clsCapQ (tauU q clsCapQ) clsCapQ clsCapQ :=
  uavg_twPQ_le_of Sθ pol A (fun θ ↦ prefixInvQ pol A θ) (clsCalls_prefixQ' pol A hhash hsign)
    (fun θ ↦ encPre_le pol A θ (prefixInvQ pol A θ) (advCalls_prefixQ pol A hhash hsign θ)
      (clsCalls_prefixQ' pol A hhash hsign θ))
    (uavg_recUPre_le pol A hpol (advCalls_prefixQ pol A hhash hsign)
      (clsCalls_prefixQ' pol A hhash hsign))
    (fun θ ↦ selPre_le_small pol A θ (clsCalls_prefixQ' pol A hhash hsign θ))
    (fun θ ↦ recSPre_le pol A θ (clsCalls_prefixQ' pol A hhash hsign θ))

/-- **The averaged classical costs of the challenge prefix in closed form** (`q ≤ 2^64`):
`((257.3 √q + 0.909 · 2^32) / 2^64)²`. -/
theorem uavg_twPQ_le_closed (Sθ : TVals → Quantum.Sphincs.Disclosures) (pol : DigestPolicy)
    (hpol : pol.NoVal) (A : SAdversary) {q : ℕ}
    (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge)
      signatureLimit) (hq : q ≤ 2 ^ 64) :
    uavg (fun θ : TVals ↦ twPQ (pkQ θ) (honQ θ) (Sθ θ) pol A θ) ≤
      ENNReal.ofReal (((257.3 * √q + 0.909 * 2 ^ 32) / 2 ^ 64) ^ 2) :=
  (uavg_twPQ_le Sθ pol hpol A hhash hsign).trans (twBoundQ_clsCap_le hq)

end Quantum.Qrom.Sphincs

end
