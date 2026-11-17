module

public import Quantum.Cost.Parallel

@[expose] public section

/-!
# NIST category 1: leanXMSS in the QROM against AES-128 key search

NIST's category 1 asks that forging be as hard as AES-128 key search, which costs `K / MAXDEPTH`
quantum gates at circuit depth `MAXDEPTH` (`K = 2^170` in the 2016 call, `aesK2016`, from Grassl
et al. 2016; `K = 2^157` in the 2022 call for additional signatures, `aesK2022`, from Jaques,
Naehrig, Roetteler, Virdia 2020), with `MAXDEPTH` between `2^40` and `2^96` (`MaxDepthRange`).
Below the threshold, inner-parallel Grover search with `G` gates in depth `MD` succeeds with
probability about `G · MD / K` (`aesCurve`), the reference curve.

* **The comparison** (`parBound_le_aesCurve`, real algebra): with `q ≤ G / GK` calls in
  `d ≤ MD / DK` rounds, a parallel bound `((a √(q · min d q) + e q + b √q + c) / 2^64)²` is at
  most `(μ · √(G · MD / K) + e G / (GK 2^64) + c / 2^64)²`, `μ = mu a b K GK DK MD`.
* **leanXMSS** (`leanXmss_qrom_nist`): the depth-aware QROM bound in this form, for every
  per-call gate cost `GK` and depth `DK`.
* **Keccak-f[1600] circuits from the literature** (documentation instances, the modelling step
  that no theorem can remove: an attacker evaluates Keccak-f no more cheaply than these
  circuits): Song, Jang, Seo 2023, low depth, 1,282,646 gates (`2^20.29`) at depth 2,020;
  Amy et al. 2016, in place, 34,974,805 gates (`2^25.06`) at depth 11,040. A clean query
  computes, copies out (3,200 gates, depth 2) and uncomputes (`cleanQueryGates`,
  `cleanQueryDepth`), as JNRV count the AES oracle.
* **The factor** (`mu_xmss_lowDepth_le`, `mu_xmss_inPlace_le`): against `2^157` on all of
  `MaxDepthRange`, `μ ≤ 1.96` with the low-depth query and `μ ≤ 0.265` with the in-place query.
* **Category 1** (`leanXmss_qrom_cat1_lowDepth`, `leanXmss_qrom_cat1_inPlace`): within NIST's
  2022 threshold (`G · MD ≤ 2^157`), forging succeeds with probability at most
  `4.14 · G · MD / 2^157 + 2^-28` with the low-depth query, which is **not** category 1 (a loss of
  the factor `4.14 = 2^2.05` against AES-128), and at most `0.072 · G · MD / 2^157 + 2^-32` with
  the in-place query, which is. Against the 2016 threshold `2^170` the in-place query gives only
  `590 · G · MD / 2^170 + 2^-32` (`leanXmss_qrom_cat1_inPlace_2016`).
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.Cost.Nist

open LeanXmss HashSig

/-! ## AES-128 and the comparison -/

/-- NIST Call for Proposals (2016) §4.A.5, from Grassl et al. 2016: AES-128 key search costs
`2^170 / MAXDEPTH` quantum gates. -/
noncomputable def aesK2016 : ℝ := 2 ^ 170

/-- NIST Call for Additional Digital Signature Schemes (2022) §4.B.3, from Jaques, Naehrig,
Roetteler, Virdia 2020: `2^157 / MAXDEPTH` quantum gates. -/
noncomputable def aesK2022 : ℝ := 2 ^ 157

/-- NIST's range of the maximal circuit depth: from `2^40` to `2^96`. -/
def MaxDepthRange (MD : ℝ) : Prop := 2 ^ 40 ≤ MD ∧ MD ≤ 2 ^ 96

/-- **The AES-128 reference success**: inner-parallel Grover key search with `G` gates in depth
`MD` succeeds with probability about `G · MD / K` (it reaches `1` at NIST's threshold
`G = K / MD`). -/
noncomputable def aesCurve (K G MD : ℝ) : ℝ := G * MD / K

/-- The two curves: `G · MD / 2^157 = 2^13 · G · MD / 2^170`. -/
theorem aesCurve_aesK2022 (G MD : ℝ) :
    aesCurve aesK2022 G MD = 2 ^ 13 * aesCurve aesK2016 G MD := by
  unfold aesCurve aesK2022 aesK2016
  ring

/-- **The comparison factor** of a parallel bound `((a √(q · min d q) + e q + b √q + c) / 2^64)²`
at `GK` gates and depth `DK` per call, against `K / MD`. -/
noncomputable def mu (a b K GK DK MD : ℝ) : ℝ :=
  a * √(K / (GK * DK * 2 ^ 128)) + b * √(K / (GK * 2 ^ 128 * MD))

theorem sqrt_div_two_pow_64 (x : ℝ) : √x / 2 ^ 64 = √(x / 2 ^ 128) := by
  rw [Real.sqrt_div' x (show (0 : ℝ) ≤ 2 ^ 128 by positivity),
    show (2 : ℝ) ^ 128 = (2 ^ 64) ^ 2 by norm_num, Real.sqrt_sq (by positivity)]

/-- **The comparison inequality**: with `q ≤ G / GK` calls in `d ≤ MD / DK` rounds,
`(a √(q · min d q) + e q + b √q + c) / 2^64 ≤ μ √(G · MD / K) + e G / (GK 2^64) + c / 2^64`,
squared. -/
theorem parBound_le_aesCurve {a e b c K GK DK G MD q d : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hK : 0 < K) (hGK : 0 < GK) (hDK : 0 < DK) (hMD : 0 < MD)
    (hq0 : 0 ≤ q) (hd0 : 0 ≤ d) (hq : q ≤ G / GK) (hd : d ≤ MD / DK) :
    ((a * √(q * min d q) + e * q + b * √q + c) / 2 ^ 64) ^ 2 ≤
      (mu a b K GK DK MD * √(aesCurve K G MD) + e * (G / GK) / 2 ^ 64 + c / 2 ^ 64) ^ 2 := by
  have hG0 : 0 ≤ G / GK := hq0.trans hq
  have hK' := hK.ne'
  have hs1 : √(K / (GK * DK * 2 ^ 128)) * √(aesCurve K G MD) =
      √(G / GK * (MD / DK) / 2 ^ 128) := by
    rw [← Real.sqrt_mul (show 0 ≤ K / (GK * DK * 2 ^ 128) by positivity)]
    congr 1
    unfold aesCurve
    rw [div_mul_div_comm, mul_comm K, mul_div_mul_right _ _ hK']
    ring
  have hs2 : √(K / (GK * 2 ^ 128 * MD)) * √(aesCurve K G MD) = √(G / GK / 2 ^ 128) := by
    rw [← Real.sqrt_mul (show 0 ≤ K / (GK * 2 ^ 128 * MD) by positivity)]
    congr 1
    unfold aesCurve
    rw [div_mul_div_comm, mul_comm K, mul_div_mul_right _ _ hK',
      mul_div_mul_right _ _ hMD.ne']
    ring
  have t1 : √(q * min d q) / 2 ^ 64 ≤ √(G / GK * (MD / DK) / 2 ^ 128) := by
    rw [sqrt_div_two_pow_64]
    refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ?_ (by positivity))
    calc q * min d q ≤ q * d := mul_le_mul_of_nonneg_left (min_le_left d q) hq0
      _ ≤ G / GK * (MD / DK) := mul_le_mul hq hd hd0 hG0
  have t2 : √q / 2 ^ 64 ≤ √(G / GK / 2 ^ 128) := by
    rw [sqrt_div_two_pow_64]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hq (by positivity))
  have t3 : e * q / 2 ^ 64 ≤ e * (G / GK) / 2 ^ 64 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq he) (by positivity)
  have hL : 0 ≤ (a * √(q * min d q) + e * q + b * √q + c) / 2 ^ 64 := by positivity
  refine pow_le_pow_left₀ hL ?_ 2
  unfold mu
  have e1 : (a * √(q * min d q) + e * q + b * √q + c) / 2 ^ 64 =
      a * (√(q * min d q) / 2 ^ 64) + e * q / 2 ^ 64 + b * (√q / 2 ^ 64) + c / 2 ^ 64 := by
    ring
  rw [e1, add_mul, mul_assoc a, mul_assoc b, hs1, hs2]
  have u1 := mul_le_mul_of_nonneg_left t1 ha
  have u2 := mul_le_mul_of_nonneg_left t2 hb
  linarith

/-! ## Keccak-f[1600] circuits -/

/-- Song, Jang, Seo, "Improved Low-Depth SHA3 Quantum Circuit for Fault-Tolerant Quantum
Computers", Appl. Sci. 13(6):3558, 2023, Tables 3, 4: one Keccak-f[1600] out of place in
1,282,646 Clifford+T gates (`2^20.29`, 38,400 Toffoli at 16 gates each). -/
def keccakfGatesLowDepth : ℕ := 1282646

/-- The same circuit's full depth: 2,020. -/
def keccakfDepthLowDepth : ℕ := 2020

/-- Amy, Di Matteo, Gheorghiu, Mosca, Parent, Schanck, "Estimating the cost of generic quantum
pre-image attacks on SHA-2 and SHA-3", SAC 2016, Table 2: one Keccak-f[1600] in place in
34,974,805 Clifford+T gates (`2^25.06`). -/
def keccakfGatesInPlace : ℕ := 34974805

/-- The same circuit's depth: 11,040. -/
def keccakfDepthInPlace : ℕ := 11040

/-- A clean query `|x, y⟩ ↦ |x, y ⊕ f x⟩` from a circuit of `g` gates: compute, copy out the
1600-bit state (3,200 gates) and uncompute, as JNRV count the AES-128 oracle. -/
def cleanQueryGates (g : ℕ) : ℕ := 2 * g + 3200

/-- The depth of a clean query from a circuit of depth `t`. -/
def cleanQueryDepth (t : ℕ) : ℕ := 2 * t + 2

/-- A clean low-depth Keccak-f query: 2,568,492 gates (`2^21.29`). -/
abbrev keccakQueryGatesLowDepth : ℕ := cleanQueryGates keccakfGatesLowDepth

/-- A clean low-depth Keccak-f query: depth 4,042 (`2^11.98`). -/
abbrev keccakQueryDepthLowDepth : ℕ := cleanQueryDepth keccakfDepthLowDepth

/-- A clean in-place Keccak-f query: 69,952,810 gates (`2^26.06`). -/
abbrev keccakQueryGatesInPlace : ℕ := cleanQueryGates keccakfGatesInPlace

/-- A clean in-place Keccak-f query: depth 22,082 (`2^14.43`). -/
abbrev keccakQueryDepthInPlace : ℕ := cleanQueryDepth keccakfDepthInPlace

theorem keccakQueryGatesLowDepth_eq : (keccakQueryGatesLowDepth : ℝ) = 2568492 := by
  norm_num [cleanQueryGates, keccakfGatesLowDepth]

theorem keccakQueryDepthLowDepth_eq : (keccakQueryDepthLowDepth : ℝ) = 4042 := by
  norm_num [cleanQueryDepth, keccakfDepthLowDepth]

theorem keccakQueryGatesInPlace_eq : (keccakQueryGatesInPlace : ℝ) = 69952810 := by
  norm_num [cleanQueryGates, keccakfGatesInPlace]

theorem keccakQueryDepthInPlace_eq : (keccakQueryDepthInPlace : ℝ) = 22082 := by
  norm_num [cleanQueryDepth, keccakfDepthInPlace]

/-! ## The factors -/

/-- `√x ≤ s` from `x ≤ s²`. -/
theorem sqrt_le_of_le_sq {x s : ℝ} (hs : 0 ≤ s) (h : x ≤ s ^ 2) : √x ≤ s :=
  (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq hs)

/-- The `b` part of the factor decreases with the depth: its value at `MD ≥ 2^40` is at most its
value at `2^40`. -/
theorem div_le_div_maxDepth {K GK MD : ℝ} (hK : 0 ≤ K) (hGK : 0 < GK) (hMD : 2 ^ 40 ≤ MD) :
    K / (GK * 2 ^ 128 * MD) ≤ K / (GK * 2 ^ 128 * 2 ^ 40) :=
  div_le_div_of_nonneg_left hK (by positivity)
    (mul_le_mul_of_nonneg_left hMD (by positivity))

set_option exponentiation.threshold 200 in
/-- **The leanXMSS factor at the low-depth query** against `2^157`: `μ ≤ 1.96` on
`MaxDepthRange`. -/
theorem mu_xmss_lowDepth_le {MD : ℝ} (hMD : MaxDepthRange MD) :
    mu 4.45 (0.523 * 2 ^ 17) aesK2022 keccakQueryGatesLowDepth keccakQueryDepthLowDepth MD ≤
      1.96 := by
  have h1 : √(aesK2022 / ((keccakQueryGatesLowDepth : ℝ) * keccakQueryDepthLowDepth * 2 ^ 128))
      ≤ 0.22741 := by
    refine sqrt_le_of_le_sq (by norm_num) ?_
    rw [keccakQueryGatesLowDepth_eq, keccakQueryDepthLowDepth_eq, aesK2022]
    norm_num
  have h2 : √(aesK2022 / ((keccakQueryGatesLowDepth : ℝ) * 2 ^ 128 * MD)) ≤ 1.3788e-5 := by
    refine sqrt_le_of_le_sq (by norm_num) ((div_le_div_maxDepth (by norm_num [aesK2022])
      (by norm_num [keccakQueryGatesLowDepth_eq]) hMD.1).trans ?_)
    rw [keccakQueryGatesLowDepth_eq, aesK2022]
    norm_num
  unfold mu
  nlinarith

set_option exponentiation.threshold 200 in
/-- **The leanXMSS factor at the in-place query** against `2^157`: `μ ≤ 0.265` on
`MaxDepthRange`. -/
theorem mu_xmss_inPlace_le {MD : ℝ} (hMD : MaxDepthRange MD) :
    mu 4.45 (0.523 * 2 ^ 17) aesK2022 keccakQueryGatesInPlace keccakQueryDepthInPlace MD ≤
      0.265 := by
  have h1 : √(aesK2022 / ((keccakQueryGatesInPlace : ℝ) * keccakQueryDepthInPlace * 2 ^ 128))
      ≤ 0.018643 := by
    refine sqrt_le_of_le_sq (by norm_num) ?_
    rw [keccakQueryGatesInPlace_eq, keccakQueryDepthInPlace_eq, aesK2022]
    norm_num
  have h2 : √(aesK2022 / ((keccakQueryGatesInPlace : ℝ) * 2 ^ 128 * MD)) ≤ 2.6421e-6 := by
    refine sqrt_le_of_le_sq (by norm_num) ((div_le_div_maxDepth (by norm_num [aesK2022])
      (by norm_num [keccakQueryGatesInPlace_eq]) hMD.1).trans ?_)
    rw [keccakQueryGatesInPlace_eq, aesK2022]
    norm_num
  unfold mu
  nlinarith

theorem mu_nonneg {a b K GK DK MD : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ mu a b K GK DK MD := by
  unfold mu
  positivity

/-! ## From the comparison to a multiple of the AES curve -/

/-- The linear term against the AES curve: for `MD ≥ 2^40`,
`c G / (GK 2^64) ≤ E · G · MD / 2^157` once `c 2^117 / (GK 2^64) ≤ E`. -/
theorem linTerm_le_aesCurve {c GK G MD E : ℝ} (hc : 0 ≤ c) (hGK : 0 < GK) (hG : 0 ≤ G)
    (hMD : 2 ^ 40 ≤ MD) (hE : c / GK / 2 ^ 64 * 2 ^ 117 ≤ E) :
    c * (G / GK) / 2 ^ 64 ≤ E * aesCurve aesK2022 G MD := by
  have hE0 : 0 ≤ c / GK / 2 ^ 64 * 2 ^ 117 := by positivity
  have h4 : 0 ≤ G * 2 ^ 40 / 2 ^ 157 := by positivity
  have e1 : c * (G / GK) / 2 ^ 64 = c / GK / 2 ^ 64 * 2 ^ 117 * (G * 2 ^ 40 / 2 ^ 157) := by
    ring
  rw [e1]
  unfold aesCurve aesK2022
  calc c / GK / 2 ^ 64 * 2 ^ 117 * (G * 2 ^ 40 / 2 ^ 157)
      ≤ E * (G * 2 ^ 40 / 2 ^ 157) := mul_le_mul_of_nonneg_right hE h4
    _ ≤ E * (G * MD / 2 ^ 157) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hMD hG) (by positivity))
        (hE0.trans hE)

/-- **Below the threshold, a multiple of the AES curve**: for `0 ≤ p ≤ 1`, `μ ≤ M`, `t ≤ E p`,
`(μ √p + t + y)² ≤ m p + r` once `(M + E)² ≤ m` and `2 (M + E) y + y² ≤ r`. -/
theorem sq_le_lin_of_le_one {μ M E y m r p t : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ M) (hE : 0 ≤ E)
    (hy : 0 ≤ y) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : (M + E) ^ 2 ≤ m)
    (hr : 2 * (M + E) * y + y ^ 2 ≤ r) (ht0 : 0 ≤ t) (ht : t ≤ E * p) :
    (μ * √p + t + y) ^ 2 ≤ m * p + r := by
  have hs0 := Real.sqrt_nonneg p
  have hs1 : √p ≤ 1 := (Real.sqrt_le_sqrt hp1).trans_eq Real.sqrt_one
  have hsq := Real.sq_sqrt hp0
  have hps : p ≤ √p := by nlinarith [mul_le_mul_of_nonneg_left hs1 hs0]
  have hME : 0 ≤ M + E := by linarith
  have h1 : μ * √p ≤ M * √p := mul_le_mul_of_nonneg_right hμ hs0
  have h2 : E * p ≤ E * √p := mul_le_mul_of_nonneg_left hps hE
  have hb : μ * √p + t + y ≤ (M + E) * √p + y := by linarith
  calc (μ * √p + t + y) ^ 2 ≤ ((M + E) * √p + y) ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
    _ = (M + E) ^ 2 * √p ^ 2 + 2 * (M + E) * y * √p + y ^ 2 := by ring
    _ ≤ m * p + r := by
        rw [hsq]
        have h3 : 2 * (M + E) * y * √p ≤ 2 * (M + E) * y :=
          mul_le_of_le_one_right (mul_nonneg (mul_nonneg (by norm_num) hME) hy) hs1
        have h4 : (M + E) ^ 2 * p ≤ m * p := mul_le_mul_of_nonneg_right hm hp0
        linarith

/-- The AES-128 success below NIST's 2022 threshold is a probability. -/
theorem aesCurve_mem_unit {G MD : ℝ} (hG : 0 ≤ G) (hMD : 0 ≤ MD) (hGM : G * MD ≤ 2 ^ 157) :
    0 ≤ aesCurve aesK2022 G MD ∧ aesCurve aesK2022 G MD ≤ 1 := by
  unfold aesCurve aesK2022
  exact ⟨by positivity, (div_le_one (by positivity)).2 hGM⟩

/-! ## leanXMSS in the QROM against AES-128 -/

/-- A parallel gate-set adversary against leanXMSS in the QROM. -/
abbrev XmssParGateAdversary (Γ : GateSet) :=
  Qrom.ParGateAdversary Γ PublicKey SigningRequest (Option Signature) Forgery

/-- **leanXMSS in the QROM against AES-128**, for any per-call cost of `GK` gates and depth
`DK`: an adversary within `G` gates and depth charge `MD > 0` forges with probability at most
`(μ √(G · MD / K) + 0.7072 · 2^-35 G / (GK 2^64) + 0.709 · 2^33 / 2^64)²`,
`μ = mu 4.45 (0.523 · 2^17) K GK DK MD`. -/
theorem leanXmss_qrom_nist {GK DK : ℕ} (hGK : 0 < GK) (hDK : 0 < DK) (Γ : GateSet)
    (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ) (G MD : ℕ) (A : XmssParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk) (gateCharge Γ (Qrom.hashGatesPar GK)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk) (opCharge δ (Qrom.hashDepthPar DK)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdChargePar Quantum.Qrom.SufCma.signChargePar) lifetime)
    (hMD : 0 < MD) {K : ℝ} (hK : 0 < K) :
    Quantum.Qrom.SufCma.winProbPar Quantum.Qrom.Xmss.xmssRom A.toAdversary ≤
      ENNReal.ofReal ((mu 4.45 (0.523 * 2 ^ 17) K GK DK MD * √(aesCurve K G MD) +
        0.7072 * (2 ^ 35)⁻¹ * (G / GK) / 2 ^ 64 + 0.709 * 2 ^ 33 / 2 ^ 64) ^ 2) := by
  refine (Qrom.leanXmss_qrom_gateDepth_closed hGK hDK Γ δ G MD A hG hD hS).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [Nat.cast_min]
  exact parBound_le_aesCurve (by norm_num) (by positivity) (by positivity) (by positivity) hK
    (by exact_mod_cast hGK) (by exact_mod_cast hDK) (by exact_mod_cast hMD) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) Nat.cast_div_le Nat.cast_div_le

set_option exponentiation.threshold 200 in
/-- **Category 1 at the low-depth Keccak query** (Song, Jang, Seo 2023, clean query
`2^21.29` gates at depth `2^11.98`): within NIST's 2022 threshold, `G · MD ≤ 2^157`, for every
`MD` in `MaxDepthRange`, forging succeeds with probability at most
`4.14 · G · MD / 2^157 + 2^-28`. This is **not** category 1: against the AES-128 success
`G · MD / 2^157` it loses the factor `4.14 = 2^2.05` (`μ ≤ 1.96`). -/
theorem leanXmss_qrom_cat1_lowDepth (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ)
    (G MD : ℕ) (A : XmssParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk)
      (gateCharge Γ (Qrom.hashGatesPar keccakQueryGatesLowDepth)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk)
      (opCharge δ (Qrom.hashDepthPar keccakQueryDepthLowDepth)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdChargePar Quantum.Qrom.SufCma.signChargePar) lifetime)
    (hMD : MaxDepthRange (MD : ℝ)) (hGM : (G : ℝ) * MD ≤ 2 ^ 157) :
    Quantum.Qrom.SufCma.winProbPar Quantum.Qrom.Xmss.xmssRom A.toAdversary ≤
      ENNReal.ofReal (4.14 * aesCurve aesK2022 G MD + (2 ^ 28)⁻¹) := by
  have hMD0 : (0 : ℝ) < MD := lt_of_lt_of_le (by positivity) hMD.1
  have hp := aesCurve_mem_unit (Nat.cast_nonneg G) hMD0.le hGM
  refine (leanXmss_qrom_nist (by norm_num [cleanQueryGates, keccakfGatesLowDepth])
    (by norm_num [cleanQueryDepth, keccakfDepthLowDepth])
    Γ δ G MD A hG hD hS (by exact_mod_cast hMD0) (K := aesK2022)
    (by norm_num [aesK2022])).trans (ENNReal.ofReal_le_ofReal ?_)
  refine sq_le_lin_of_le_one (mu_nonneg (by norm_num) (by norm_num)) (mu_xmss_lowDepth_le hMD)
    (E := 0.0722) (by norm_num) (by positivity) hp.1 hp.2 (by norm_num) (by norm_num)
    (by positivity) (linTerm_le_aesCurve (by norm_num)
      (by norm_num [keccakQueryGatesLowDepth_eq])
      (Nat.cast_nonneg G) hMD.1 ?_)
  rw [keccakQueryGatesLowDepth_eq]
  norm_num

set_option exponentiation.threshold 200 in
/-- **Category 1 at the in-place Keccak query** (Amy et al. 2016, clean query `2^26.06` gates at
depth `2^14.43`): within NIST's 2022 threshold, `G · MD ≤ 2^157`, for every `MD` in
`MaxDepthRange`, forging succeeds with probability at most `0.072 · G · MD / 2^157 + 2^-32`,
below the AES-128 success `G · MD / 2^157` up to `2^-32` (`μ ≤ 0.265`). -/
theorem leanXmss_qrom_cat1_inPlace (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ)
    (G MD : ℕ) (A : XmssParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk)
      (gateCharge Γ (Qrom.hashGatesPar keccakQueryGatesInPlace)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk)
      (opCharge δ (Qrom.hashDepthPar keccakQueryDepthInPlace)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdChargePar Quantum.Qrom.SufCma.signChargePar) lifetime)
    (hMD : MaxDepthRange (MD : ℝ)) (hGM : (G : ℝ) * MD ≤ 2 ^ 157) :
    Quantum.Qrom.SufCma.winProbPar Quantum.Qrom.Xmss.xmssRom A.toAdversary ≤
      ENNReal.ofReal (0.072 * aesCurve aesK2022 G MD + (2 ^ 32)⁻¹) := by
  have hMD0 : (0 : ℝ) < MD := lt_of_lt_of_le (by positivity) hMD.1
  have hp := aesCurve_mem_unit (Nat.cast_nonneg G) hMD0.le hGM
  refine (leanXmss_qrom_nist (by norm_num [cleanQueryGates, keccakfGatesInPlace])
    (by norm_num [cleanQueryDepth, keccakfDepthInPlace])
    Γ δ G MD A hG hD hS (by exact_mod_cast hMD0) (K := aesK2022)
    (by norm_num [aesK2022])).trans (ENNReal.ofReal_le_ofReal ?_)
  refine sq_le_lin_of_le_one (mu_nonneg (by norm_num) (by norm_num)) (mu_xmss_inPlace_le hMD)
    (E := 0.00266) (by norm_num) (by positivity) hp.1 hp.2 (by norm_num) (by norm_num)
    (by positivity) (linTerm_le_aesCurve (by norm_num)
      (by norm_num [keccakQueryGatesInPlace_eq])
      (Nat.cast_nonneg G) hMD.1 ?_)
  rw [keccakQueryGatesInPlace_eq]
  norm_num

/-- **Against NIST's 2016 threshold** (`2^170 / MAXDEPTH`, Grassl et al.), the in-place query
gives only `590 · G · MD / 2^170 + 2^-32` within `G · MD ≤ 2^157`: not category 1 in the 2016
metric (as for every 128-bit digest, ideal Grover search included). -/
theorem leanXmss_qrom_cat1_inPlace_2016 (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ)
    (G MD : ℕ) (A : XmssParGateAdversary Γ)
    (hG : ∀ pk, IFreeM.IsChargeBound (A pk)
      (gateCharge Γ (Qrom.hashGatesPar keccakQueryGatesInPlace)) G)
    (hD : ∀ pk, IFreeM.IsChargeBound (A pk)
      (opCharge δ (Qrom.hashDepthPar keccakQueryDepthInPlace)) MD)
    (hS : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdChargePar Quantum.Qrom.SufCma.signChargePar) lifetime)
    (hMD : MaxDepthRange (MD : ℝ)) (hGM : (G : ℝ) * MD ≤ 2 ^ 157) :
    Quantum.Qrom.SufCma.winProbPar Quantum.Qrom.Xmss.xmssRom A.toAdversary ≤
      ENNReal.ofReal (590 * aesCurve aesK2016 G MD + (2 ^ 32)⁻¹) := by
  refine (leanXmss_qrom_cat1_inPlace Γ δ G MD A hG hD hS hMD hGM).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h0 : 0 ≤ aesCurve aesK2016 G MD := by
    unfold aesCurve aesK2016
    positivity
  rw [aesCurve_aesK2022]
  nlinarith

end Quantum.Cost.Nist

end
