module

public import Quantum.Qrom.Sphincs.Multi.Costs.Ports
public import Quantum.Qrom.Sphincs.Multi.Costs.Numeric
public import Quantum.Qrom.Sphincs.Multi.GameTCalls

@[expose] public section

/-!
# The classical costs of the `n`-user leanSPHINCS runtime 2: the event bound and the averages

* **The event bound at the end of the challenge prefix** (`ewPrefixQSN_le`): with at most `q`
  adversary calls and `K` classical calls, the weight of `BadRQN pk hon S` is at most
  `(advTermQN q S + √twPQSN)²`, `advTermQN q S = q √(6 epsQN S)` (fresh fraction
  `epsQN S = 2^-128 + ⨆ i, price (S i)`).
* **The averaged costs** (`uavg_twMaskSN_le_of`): on the tables with distinct `PK.seed`s
  (`twMaskSN`, `0` elsewhere), from the per-table split of Ports' `twPQSN_le`, an Enc bound
  `encPreSN ≤ encCap cE εE q K recUPreSN` and the averaged recorded unselected mass `τ`, the
  average is at most `twBoundQ cE εE q K τ 0 0` (no re-grind weights: the single-user
  `Sl = R = 0`).
* `clsBoundSN total q`: that bound at the Enc constants, `K = clsCapSN total`, `τ = tauUN q K`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (Key keyOf msgPos Disclosures)

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR extWeight sumWeight extCls
  eventWeight_runtimeR_le uavg_sq_rpow_add_le uavg_const_le)
open Quantum.Xmss.Hybrid (uavg uavg_mono uavg_add uavg_const_mul)

attribute [local irreducible] sphincsRom

/- Instance search for the registers over `Finset (TPosN n)` exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

/-! ## The event bound at the end of the prefix -/

theorem epsQN_ne_top (S : Fin n → Disclosures) : epsQN S ≠ ⊤ := by
  refine ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.mpr (by positivity), ?_⟩
  have h : (⨆ i, ENNReal.ofReal (Quantum.Sphincs.price (S i))) ≤
      ∑ i, ENNReal.ofReal (Quantum.Sphincs.price (S i)) :=
    iSup_le fun i ↦ Finset.single_le_sum
      (f := fun i ↦ ENNReal.ofReal (Quantum.Sphincs.price (S i))) (fun _ _ ↦ zero_le)
      (Finset.mem_univ i)
  exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.ofReal_ne_top) h

/-- **The adversary term**: `∑_{k < q} √(6 epsQN S)`. -/
noncomputable def advTermQN (q : ℕ) (S : Fin n → Disclosures) : ℝ≥0∞ :=
  ∑ _k ∈ Finset.range q, (6 * epsQN S) ^ (2⁻¹ : ℝ)

/-- **The event bound at the end of the challenge prefix**: with at most `q` adversary calls and
`K` classical calls, `ew ≤ (advTermQN q S + √twPQSN)²`. -/
theorem ewPrefixQSN_le (pk : Fin n → PublicKey) (hon : Fin n → HonestCells)
    (S : Fin n → Disclosures) (A : MuAdversaryS n) (θ : TValsN n) {q K : ℕ}
    (hq : IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 0
        else 1) q)
    (hK : IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 1
        else 0) K) :
    (runtimeR (m0SN (n := n))).eventWeight .instruments (hwProjector (BadRQN pk hon S))
        (prefixQSN (strPolN n) A θ) initQSN ≤
      (advTermQN q S + twPQSN pk hon S A θ ^ (2⁻¹ : ℝ)) ^ 2 :=
  eventWeight_runtimeR_le (q := q) (K := K) (BadRQN pk hon S) (labelFree_badRQN pk hon S)
    (fun W m ↦ upClosed_slice_badRQN W m) m0SN (empty_not_mem_badRQN m0SN)
    (fun _ ↦ epsQN S) (fun _ _ ↦ epsQN_ne_top S)
    (fun _ _ W m ↦ freshBound_slice_badRQN W m _)
    (fun c σ ↦ readCostT (BadRQN pk hon S) c σ)
    (fun c σ ↦ flipCost (BadRQN pk hon S) (hwProgKraus c) 0 σ)
    (fun c σ hσ ↦ potential_hwReadKraus_le_refinedT (BadRQN pk hon S) c σ hσ)
    (fun c σ hσ ↦ potential_hwProgKraus_le (BadRQN pk hon S) (fun _ ↦ 0)
      (fun _ ↦ conjTranspose_zero) (fun _ ↦ mul_zero 0) c σ hσ)
    .instruments (prefixQSN (strPolN n) A θ) hq hK (SubState.basis ())

/-! ## The averaged costs -/

open scoped Classical in
/-- **The classical costs on the tables with distinct `PK.seed`s**: `twPQSN` at the users' public
keys, honest cells and static covers at `θ` when the `PK.seed`s are distinct, `0` otherwise. -/
noncomputable def twMaskSN (A : MuAdversaryS n) (θ : TValsN n) : ℝ≥0∞ :=
  if PDistinct (tabOfN θ) then twPQSN (pkQN θ) (honQN θ) (starQN θ) A θ else 0

theorem twMaskSN_of_pDistinct (A : MuAdversaryS n) {θ : TValsN n} (h : PDistinct (tabOfN θ)) :
    twMaskSN A θ = twPQSN (pkQN θ) (honQN θ) (starQN θ) A θ := by
  classical
  unfold twMaskSN
  exact ite_eq_left h

theorem twMaskSN_of_not (A : MuAdversaryS n) {θ : TValsN n} (h : ¬PDistinct (tabOfN θ)) :
    twMaskSN A θ = 0 := by
  classical
  unfold twMaskSN
  exact ite_eq_right h

/-- **The averaged classical costs of the prefix**, from the slices' bounds: the prefix
invariant and the Enc bound on the tables with distinct `PK.seed`s, the averaged recorded
unselected mass. -/
theorem uavg_twMaskSN_le_of (A : MuAdversaryS n) {q K : ℕ} {cE εE τ : ℝ≥0∞}
    (hinv : ∀ θ, PDistinct (tabOfN θ) → PrefixInvQSN (pkQN θ) (honQN θ) A θ)
    (hK : ∀ θ, IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 1
        else 0) K)
    (henc : ∀ θ, PDistinct (tabOfN θ) → encPreSN A θ ≤ encCap cE εE q K (recUPreSN A θ))
    (hU : uavg (recUMaskSN A) ≤ τ) :
    uavg (twMaskSN A) ≤ twBoundQ cE εE q K τ 0 0 := by
  set c₀ : ℝ≥0∞ := ENNReal.ofReal (2 / Fintype.card PairOut) * K
  set a : TValsN n → ℝ≥0∞ := fun θ ↦
    (2 ^ 127 : ℝ≥0∞)⁻¹ * (encCap cE εE q K (recUMaskSN A θ) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ((0 : ℕ) : ℝ≥0∞)) + c₀
  set p : TValsN n → ℝ≥0∞ := fun θ ↦
    recUMaskSN A θ + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((0 : ℕ) : ℝ≥0∞)
  have hpt : ∀ θ, twMaskSN A θ ≤ (a θ ^ (2⁻¹ : ℝ) + p θ ^ (2⁻¹ : ℝ)) ^ 2 := fun θ ↦ by
    by_cases hP : PDistinct (tabOfN θ)
    · rw [twMaskSN_of_pDistinct A hP]
      have h1 : (2 ^ 127 : ℝ≥0∞)⁻¹ * encPreSN A θ + c₀ ≤ a θ := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le) le_rfl
        rw [Nat.cast_zero, mul_zero, add_zero, recUMaskSN_of_pDistinct A hP]
        exact henc θ hP
      have h2 : recUPreSN A θ ≤ p θ := by
        rw [← recUMaskSN_of_pDistinct A hP]
        exact le_add_of_nonneg_right zero_le
      exact (twPQSN_le (honQN θ) (starQN θ) A θ (hinv θ hP) (hK θ)).trans
        (pow_le_pow_left₀ zero_le (add_le_add (ENNReal.rpow_le_rpow h1 (by norm_num))
          (ENNReal.rpow_le_rpow h2 (by norm_num))) 2)
    · rw [twMaskSN_of_not A hP]
      exact zero_le
  refine (uavg_mono hpt).trans ((uavg_sq_rpow_add_le a p).trans ?_)
  have hua : uavg a ≤ aCap cE εE q K τ 0 := by
    have e : a = fun θ ↦ ((2 ^ 127 : ℝ≥0∞)⁻¹ * (cE * 4 * ((q + K : ℕ) : ℝ≥0∞))) *
        recUMaskSN A θ + ((2 ^ 127 : ℝ≥0∞)⁻¹ * (cE * ((q : ℝ≥0∞) +
          ((q + K : ℕ) : ℝ≥0∞) * K * εE) + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((0 : ℕ) : ℝ≥0∞)) + c₀) := by
      funext θ
      simp only [a, encCap]
      ring
    rw [e, uavg_add, uavg_const_mul]
    refine (add_le_add (mul_le_mul_of_nonneg_left hU zero_le) (uavg_const_le _)).trans_eq ?_
    simp only [aCap, encCap]
    ring
  have hup : uavg p ≤ pCap τ 0 := by
    rw [uavg_add]
    exact add_le_add hU (uavg_const_le _)
  unfold twBoundQ
  gcongr

/-- **The bound on the averaged classical costs** of `n` users with `q` hash calls and `total`
signing requests: `twBoundQ` at the Enc constants, `K = clsCapSN total`, `τ = tauUN q K`, no
re-grind weights. -/
noncomputable def clsBoundSN (total q : ℕ) : ℝ≥0∞ :=
  twBoundQ encC encEps q (clsCapSN total) (tauUN q (clsCapSN total)) 0 0

end Quantum.Qrom.Sphincs.Multi

end
