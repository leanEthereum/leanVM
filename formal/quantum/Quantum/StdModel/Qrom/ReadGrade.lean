module

public import Quantum.Xmss.Assembly.EventSqrt

@[expose] public section

/-!
# Challenge reads graded like sponge calls

A classical read of a challenge cell (a cell whose recorded value may enter the event) cannot be
made free; it is priced like a quantum call, by a square root. ReadCost's square-root form
(`potential_hwReadKraus_le_sqrt`) and its per-state terms (`read_readH_le`) give, for a read of
cell `z` of `h` with any memory update `u` on a state with no decompressed `⊥` at the cell:
if at most `F` values flip the event from an empty cell, the move with the cell's own value never
enters the event from outside, and a recorded state whose read moves the memory across the event
is already in it, then `√w' ≤ √w + √(η tr σ)` with `η = (2 √(F/N) + √((F + 2)/N))²`
(`tsum_potential_readH_le_sqrt`, `N = |X|`).
-/

open Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.StdModel.Qrom

open Quantum Quantum.Sponge

/-- **The price of a graded read**: `(2 √(F/N) + √((F + 2)/N))²`, `N = |X|`. -/
noncomputable def gradeEta (X : Type) [Fintype X] (F : ℕ) : ℝ :=
  (2 * √((F : ℝ) / Fintype.card X) + √(((F : ℝ) + 2) / Fintype.card X)) ^ 2

theorem gradeEta_nonneg (X : Type) [Fintype X] (F : ℕ) : 0 ≤ gradeEta X F :=
  sq_nonneg _

/-- The real inequality behind the graded read: `(s + e)² + β² t² + 2 e s ≤ (s + (2α + β) t)²`
for `e ≤ α t`. -/
theorem graded_real_le {s e α β t : ℝ} (hs : 0 ≤ s) (he : 0 ≤ e) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (ht : 0 ≤ t) (h : e ≤ α * t) :
    (s + e) ^ 2 + β ^ 2 * t ^ 2 + 2 * (e * s) ≤ (s + (2 * α + β) * t) ^ 2 := by
  have h1 : e * s ≤ α * t * s := mul_le_mul_of_nonneg_right h hs
  have h2 : e ^ 2 ≤ (α * t) ^ 2 := pow_le_pow_left₀ he h 2
  nlinarith [mul_nonneg hα hβ, mul_nonneg (mul_nonneg hα hβ) (sq_nonneg t),
    mul_nonneg (mul_nonneg hβ ht) hs]

section sharp

variable {n Y R : Type} [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y] [Nonempty Y]

omit [Fintype n] [DecidableEq n] in
/-- **A sharper change weight of one outcome**: the outcome `y` changes the event from the empty
cell with weight at most the indicator that recording `y` (with the rest moved by `y`) changes it,
plus `2/|Y|` (the compression's mass off the recorded value). -/
theorem dw_le (S : Set n) [DecidablePred (· ∈ S)] (e : n ≃ Option Y × R)
    (τ : Option Y → R → R) (y : Y) (r : R) :
    dw e τ S y r ≤ (if ind S (e.symm (some y, τ (some y) r)) = q0 e S r then 0 else 1) +
      2 / Fintype.card Y := by
  have hN : (1 : ℝ) ≤ Fintype.card Y := Nat.one_le_cast.mpr Fintype.card_pos
  set I : Option Y → ℝ := fun a ↦ if ind S (e.symm (a, τ (some y) r)) = q0 e S r then 0 else 1
  have hI0 : ∀ a, 0 ≤ I a := fun a ↦ by simp only [I]; split_ifs <;> norm_num
  have hI1 : ∀ a, I a ≤ 1 := fun a ↦ by simp only [I]; split_ifs <;> norm_num
  have hsum := sum_cr_sq (Y := Y) y
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (some y))] at hsum
  unfold dw
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (some y))]
  have hrest : ∑ a ∈ Finset.univ.erase (some y), cr a (some y) ^ 2 * I a ≤
      ∑ a ∈ Finset.univ.erase (some y), cr a (some y) ^ 2 :=
    Finset.sum_le_sum fun a _ ↦ mul_le_of_le_one_right (sq_nonneg _) (hI1 a)
  have hyy : cr (some y) (some y) = 1 - (Fintype.card Y : ℝ)⁻¹ := by simp [cr]
  have hsq : cr (some y) (some y) ^ 2 ≤ 1 := by
    rw [hyy]
    have h0 : 0 ≤ 1 - (Fintype.card Y : ℝ)⁻¹ := by
      rw [sub_nonneg]
      exact inv_le_one_of_one_le₀ hN
    nlinarith [inv_nonneg.mpr (zero_le_one.trans hN)]
  have hoff : 1 - cr (some y) (some y) ^ 2 ≤ 2 / Fintype.card Y := by
    rw [hyy, div_eq_mul_inv]
    nlinarith [sq_nonneg (Fintype.card Y : ℝ)⁻¹]
  have h1 : cr (some y) (some y) ^ 2 * I (some y) ≤ I (some y) :=
    mul_le_of_le_one_left (hI0 _) hsq
  change cr (some y) (some y) ^ 2 * I (some y) +
    ∑ a ∈ Finset.univ.erase (some y), cr a (some y) ^ 2 * I a ≤ I (some y) + _
  linarith

omit [Fintype n] [DecidableEq n] in
/-- **The sharper change weight of a rest**: at most the number of outcomes whose recording
changes the event, plus `2`. -/
theorem chw_le (S : Set n) [DecidablePred (· ∈ S)] (e : n ≃ Option Y × R)
    (τ : Option Y → R → R) (r : R) :
    chw e τ S r ≤ ((Finset.univ.filter fun y : Y ↦
      ind S (e.symm (some y, τ (some y) r)) ≠ q0 e S r).card : ℝ) + 2 := by
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  unfold chw
  refine (Finset.sum_le_sum fun y _ ↦ dw_le S e τ y r).trans_eq ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_div_cancel₀ _ hN.ne', Finset.card_filter, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  split_ifs <;> simp_all

end sharp

section read

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M] [Nonempty X] [Nonempty Z]

omit [DecidableEq M] [Nonempty X] [Nonempty Z] in
/-- A diagonal sum bounded termwise on the support of `σ`. -/
theorem sum_diag_le_of_support {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) (f g : Unit × HwReg X Z M → ℝ) (h : ∀ q, σ q q ≠ 0 → f q ≤ g q) :
    ∑ q, f q * (σ q q).re ≤ ∑ q, g q * (σ q q).re := by
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases hq : σ q q = 0
  · simp [hq]
  · exact mul_le_mul_of_nonneg_right (h q hq) (Complex.nonneg_iff.1 hσ.diag_nonneg).1

omit [DecidableEq M] [Nonempty X] [Nonempty Z] in
theorem trace_re_eq_sum (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    σ.trace.re = ∑ q, 1 * (σ q q).re := by
  simp [Matrix.trace, Complex.re_sum]

open scoped Classical in
/-- The number of values whose recording at cell `z` of `q`, with the memory update, changes the
event. -/
noncomputable def rdCnt (S : Set (HwReg X Z M)) (z : Z) (u : M → Option X → M)
    (q : Unit × HwReg X Z M) : ℕ :=
  (Finset.univ.filter fun v : X ↦ ¬ ((((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2.1,
    u q.2.2.2 (some v)) ∈ S) ↔ q.2 ∈ S)).card

omit [DecidableEq M] [Nonempty Z] in
/-- **The diagonal term of a read of `h`, sharply**: on an empty cell the number of values whose
recording (with the memory update) changes the event, plus `2`, over `|X|`; `2/|X|` plus the
classical move on a recorded cell; the classical move on a hardwired cell. -/
theorem readA_readH_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (u : M → Option X → M) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) :
    readA S (.readH z u) σ ≤ ∑ q, (if q.2.2.1.1 z = none then
        (if q.2.1.1 z = none then ((rdCnt S z u q : ℝ) + 2) / Fintype.card X else
          2 / Fintype.card X + if hCls S u (q.2.1.1 z) q then 1 else 0) else
        if hCls S u (q.2.2.1.1 z) q then 1 else 0) * (σ q q).re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hsym := splitH'_symm_tau (M := M) z u
  unfold readA costA
  refine Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right ?_ (hre q)
  by_cases ha : q.2.2.1.1 z = none
  · rw [ite_eq_left ha]
    have ha' : actH z (splitH' z q).2 := ha
    rcases h1 : q.2.1.1 z with _ | y
    · rw [ite_eq_left rfl]
      refine (fd_none_le (liftSet S) ha' h1).trans
        (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
      refine (chw_le (liftSet S) _ _ _).trans ?_
      have h0 : q0 (splitH' z) (liftSet S) (splitH' z q).2 = ind (liftSet S) q := by
        rw [q0, splitH'_symm_none z q h1]
      refine add_le_add (Nat.cast_le.mpr (Finset.card_le_card fun v hv ↦ ?_)) le_rfl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [hsym, h0, ind_ne_iff] at hv
      exact hv
    · rw [ite_eq_right (Option.some_ne_none y)]
      refine (fd_some_le (liftSet S) (τ := tauH z u) (φ := phiH z u) ha' h1).trans ?_
      rw [hsym]
      have hup : Function.update q.2.1.1 z (some y) = q.2.1.1 := by
        rw [← h1, Function.update_eq_self]
      rw [hup, add_comm]
      exact add_le_add le_rfl (ind_sub_ind_le _ q)
  · rw [ite_eq_right ha, fd_off (liftSet S) (show ¬ actH z (splitH' z q).2 from ha)]
    exact ind_sub_ind_le _ q

/-- **A read of a challenge cell costs like a sponge call.** For a read of cell `z` of `h` with the
memory update `u`, on a state with no decompressed `⊥` at the cell (`ReadNoBot`) and an event
up-closed in the read cell: if on the support of `σ` at most `F` values flip the event from an
empty cell (`hFlip`, `rdCnt`), the move with the cell's own value never enters the event from
outside (`hCls`), and a recorded state whose read moves the memory across the event is in it
(`hMove`), then `√w' ≤ √w + √(η tr σ)` with `η = gradeEta X F`. -/
theorem tsum_potential_readH_le_sqrt (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (u : M → Option X → M) (F : ℕ) (hup : UpCell S (.readH z u))
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : ReadNoBot (.readH z u) σ)
    (hflip : ∀ q : Unit × HwReg X Z M, σ q q ≠ 0 → q.2.2.1.1 z = none → q.2.1.1 z = none →
      (Finset.univ.filter (hFlip S z u q)).card ≤ F ∧ rdCnt S z u q ≤ F)
    (hclsR : ∀ q : Unit × HwReg X Z M, σ q q ≠ 0 → q.2.2.1.1 z = none →
      ¬ hCls S u (q.2.1.1 z) q)
    (hclsW : ∀ q : Unit × HwReg X Z M, σ q q ≠ 0 → q.2.2.1.1 z ≠ none →
      ¬ hCls S u (q.2.2.1.1 z) q)
    (hmove : ∀ q : Unit × HwReg X Z M, σ q q ≠ 0 → q.2.2.1.1 z = none → q.2.1.1 z ≠ none →
      hMove S z u q → q.2 ∈ S) :
    ∑' r, QuantumRuntime.potential (hwProjector S) (MatrixMap.conj (hwReadKraus (.readH z u) r) σ)
      ≤ (QuantumRuntime.potential (hwProjector S) σ ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (gradeEta X F * σ.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := potential_hwReadKraus_le_sqrt S (.readH z u) hup hσ hnb
  obtain ⟨hEr, -, hMr⟩ := read_readH_le S z u hσ
  set N : ℝ := (Fintype.card X : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  set a : ℝ := (F : ℝ) / N
  set b : ℝ := ((F : ℝ) + 2) / N
  have ha : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hN.le
  have hb : 0 ≤ b := div_nonneg (by positivity) hN.le
  set T : ℝ := σ.trace.re
  set W : ℝ := ∑ q, ind (liftSet S) q * (σ q q).re
  set E : ℝ := readE S (.readH z u) σ
  set A : ℝ := readA S (.readH z u) σ
  set m : ℝ := readM S (.readH z u) σ
  have hre : ∀ q : Unit × HwReg X Z M, 0 ≤ (σ q q).re :=
    fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hT : 0 ≤ T := by
    rw [show T = ∑ q, 1 * (σ q q).re from trace_re_eq_sum σ]
    exact Finset.sum_nonneg fun q _ ↦ by simpa using hre q
  have hW : 0 ≤ W := Finset.sum_nonneg fun q _ ↦ mul_nonneg (ind_nonneg _ q) (hre q)
  have hE0 : 0 ≤ E := costE_nonneg (liftSet S) hσ
  -- `E ≤ a T`
  have hE : E ≤ a * T := by
    refine hEr.trans ?_
    rw [show T = ∑ q, 1 * (σ q q).re from trace_re_eq_sum σ, Finset.mul_sum]
    simp only [← mul_assoc, mul_one]
    refine sum_diag_le_of_support hσ _ _ fun q hq ↦ ?_
    split_ifs with hc
    · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hflip q hq hc.1 hc.2).1) hN.le
    · exact ha
  -- `A ≤ b T`
  have hA : A ≤ b * T := by
    refine (readA_readH_le S z u hσ).trans ?_
    rw [show T = ∑ q, 1 * (σ q q).re from trace_re_eq_sum σ, Finset.mul_sum]
    simp only [← mul_assoc, mul_one]
    refine sum_diag_le_of_support hσ _ _ fun q hq ↦ ?_
    have h2b : 2 / N ≤ b :=
      div_le_div_of_nonneg_right (by linarith [(Nat.cast_nonneg F : (0 : ℝ) ≤ F)]) hN.le
    split_ifs with h1 h2 h3 h4
    · have hc := (Nat.cast_le (α := ℝ)).mpr (hflip q hq h1 h2).2
      exact div_le_div_of_nonneg_right (by linarith) hN.le
    · exact absurd h3 (hclsR q hq h1)
    · simpa using h2b
    · exact absurd h4 (hclsW q hq h1)
    · exact hb
  -- `m ≤ W`
  have hm : m ≤ W := by
    refine hMr.trans (sum_diag_le_of_support hσ _ _ fun q hq ↦ ?_)
    split_ifs with hc
    · exact (ind_eq_one_of_mem (hmove q hq hc.1 hc.2.1 hc.2.2)).ge
    · exact ind_nonneg _ q
  have hm0 : 0 ≤ m := costM_nonneg (liftSet S) hσ
  rw [potential_eq_sum] at h ⊢
  refine h.trans ?_
  -- Everything as `ofReal` of reals.
  have hX1 : (ENNReal.ofReal W ^ (2⁻¹ : ℝ) + ENNReal.ofReal E ^ (2⁻¹ : ℝ)) ^ 2 =
      ENNReal.ofReal ((√W + √E) ^ 2) := by
    rw [ENNReal.ofReal_rpow_inv_two, ENNReal.ofReal_rpow_inv_two,
      ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
      ENNReal.ofReal_pow (by positivity)]
  have hX3 : 2 * (ENNReal.ofReal E * ENNReal.ofReal m) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (2 * (√E * √W)) := by
    rw [← ENNReal.ofReal_mul hE0, ENNReal.ofReal_rpow_inv_two,
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    rw [Real.sqrt_mul hE0]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm) (Real.sqrt_nonneg _)
  have hη : √(gradeEta X F * T) = (2 * √a + √b) * √T := by
    rw [Real.sqrt_mul (gradeEta_nonneg X F), gradeEta,
      Real.sqrt_sq (by positivity)]
  have hRHS : (ENNReal.ofReal W ^ (2⁻¹ : ℝ) +
      ENNReal.ofReal (gradeEta X F * T) ^ (2⁻¹ : ℝ)) ^ 2 =
        ENNReal.ofReal ((√W + (2 * √a + √b) * √T) ^ 2) := by
    rw [ENNReal.ofReal_rpow_inv_two, ENNReal.ofReal_rpow_inv_two, hη,
      ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (by positivity),
      ENNReal.ofReal_pow (by positivity)]
  rw [hRHS, hX1]
  calc ENNReal.ofReal ((√W + √E) ^ 2) +
        (ENNReal.ofReal A + 2 * (ENNReal.ofReal E * ENNReal.ofReal m) ^ (2⁻¹ : ℝ))
      ≤ ENNReal.ofReal ((√W + √E) ^ 2) +
        (ENNReal.ofReal (b * T) + ENNReal.ofReal (2 * (√E * √W))) :=
        add_le_add le_rfl (add_le_add (ENNReal.ofReal_le_ofReal hA) hX3)
    _ = ENNReal.ofReal ((√W + √E) ^ 2 + (b * T + 2 * (√E * √W))) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((√W + (2 * √a + √b) * √T) ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have he : √E ≤ √a * √T := by
          rw [← Real.sqrt_mul ha]
          exact Real.sqrt_le_sqrt hE
        have key := graded_real_le (Real.sqrt_nonneg W) (Real.sqrt_nonneg E)
          (Real.sqrt_nonneg a) (Real.sqrt_nonneg b) (Real.sqrt_nonneg T) he
        rw [Real.sq_sqrt hb, Real.sq_sqrt hT] at key
        linarith

omit [Nonempty X] [Nonempty Z] in
/-- **A read that never enters the event on the support costs nothing**: if no Kraus entry of the
read leads from a register of `T` outside the event into it, a state supported on `T` keeps its
event weight from rising. -/
theorem tsum_potential_le_of_into [AddCommGroup X] [AddCommGroup Z] (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)]
    (c : HwRead X Z M) (T : Set (HwReg X Z M))
    (hT : ∀ r (q' q : Unit × HwReg X Z M), hwReadKraus c r q' q ≠ 0 → q.2 ∈ T → q'.2 ∈ S →
      q.2 ∈ S)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hsupp : QuerySupportedOn (fun m : Unit × HwReg X Z M ↦ m.2) T σ) :
    ∑' r, QuantumRuntime.potential (hwProjector S) (MatrixMap.conj (hwReadKraus c r) σ) ≤
      QuantumRuntime.potential (hwProjector S) σ := by
  obtain ⟨hQ, hQQ⟩ := one_kronecker_hwProjector_proj S
  rw [one_kronecker_hwProjector] at hQ hQQ
  set Pj := indProj (liftSet S) with hPj
  have hcomm : ∀ r, Pj * hwReadKraus c r * σ = Pj * hwReadKraus c r * Pj * σ := by
    intro r
    ext q' b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hPj, indProj, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hk : hwReadKraus c r q' a = 0
    · simp [hk]
    by_cases hs : σ a b = 0
    · simp [hs]
    have ha := (hsupp a b hs).1
    by_cases hq : q'.2 ∈ S
    · have h1 : ind (liftSet S) a = 1 := by
        simp [ind, mem_liftSet, hT r q' a hk ha hq]
      rw [h1]
      simp
    · have h0 : ind (liftSet S) q' = 0 := by
        simp [ind, mem_liftSet, hq]
      rw [h0]
      simp
  have hσh : σᴴ = σ := hσ.1
  have hadj : ∀ r, σ * (hwReadKraus c r)ᴴ * Pj = σ * Pj * (hwReadKraus c r)ᴴ * Pj := by
    intro r
    have h := congrArg conjTranspose (hcomm r)
    simp only [conjTranspose_mul, hσh, hQ] at h
    simpa only [Matrix.mul_assoc] using h
  set τ := Pj * σ * Pj with hτ
  have hτp : τ.PosSemidef := by
    have h := hσ.mul_mul_conjTranspose_same Pj
    rwa [hQ] at h
  -- each term is the trace of the event part of `K τ Kᴴ`
  have key : ∀ K : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ,
      Pj * K * σ = Pj * K * Pj * σ → σ * Kᴴ * Pj = σ * Pj * Kᴴ * Pj →
      (Kᴴ * Pj * K * σ).trace = (Pj * (K * τ * Kᴴ) * Pj).trace := by
    intro K hc ha
    have e1 : (Kᴴ * Pj * K * σ).trace = (Pj * K * σ * Kᴴ).trace := by
      rw [show Kᴴ * Pj * K * σ = Kᴴ * (Pj * K * σ) by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm]
    have e2 : Pj * K * σ * Kᴴ * Pj = Pj * (K * τ * Kᴴ) * Pj := by
      calc Pj * K * σ * Kᴴ * Pj = (Pj * K * σ) * Kᴴ * Pj := rfl
        _ = Pj * K * Pj * (σ * Kᴴ * Pj) := by rw [hc]; simp only [Matrix.mul_assoc]
        _ = Pj * K * Pj * (σ * Pj * Kᴴ * Pj) := by rw [ha]
        _ = Pj * (K * τ * Kᴴ) * Pj := by simp only [hτ, Matrix.mul_assoc]
    rw [e1, ← e2, Matrix.trace_mul_comm (Pj * K * σ * Kᴴ) Pj]
    simp only [← Matrix.mul_assoc]
    rw [hQQ]
  have hterm : ∀ r, ((hwReadKraus c r)ᴴ * Pj * hwReadKraus c r * σ).trace =
      (Pj * (hwReadKraus c r * τ * (hwReadKraus c r)ᴴ) * Pj).trace := fun r ↦
    key _ (hcomm r) (hadj r)
  -- the event part of a positive operator has at most its trace
  have hproj : ∀ A : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ, A.PosSemidef →
      (Pj * A * Pj).trace.re ≤ A.trace.re := by
    intro A hA
    have hdec : A.trace = (Pj * A * Pj).trace + ((1 - Pj) * A * (1 - Pj)).trace := by
      have h1 : ((1 - Pj) * A * (1 - Pj)).trace = A.trace - (Pj * A).trace - (A * Pj).trace +
          (Pj * A * Pj).trace := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
          Matrix.trace_sub]
        ring
      have h2 : (A * Pj).trace = (Pj * A).trace := Matrix.trace_mul_comm A Pj
      have h3 : (Pj * A * Pj).trace = (Pj * A).trace := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQQ]
      rw [h1, h2, h3]
      ring
    have hnn : 0 ≤ ((1 - Pj) * A * (1 - Pj)).trace.re := by
      have h := hA.mul_mul_conjTranspose_same (1 - Pj)
      rw [conjTranspose_sub, conjTranspose_one, hQ] at h
      exact h.trace_re_nonneg
    rw [hdec, Complex.add_re]
    linarith
  rw [tsum_potential_conj S _ hσ, ← hPj]
  have hpot : QuantumRuntime.potential (hwProjector S) σ = ENNReal.ofReal τ.trace.re := by
    rw [QuantumRuntime.potential, MatrixMap.amplifyLeft_conj, one_kronecker_hwProjector,
      MatrixMap.conj_apply, hQ]
  rw [hpot]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  simp only [hterm]
  calc ∑ r, (Pj * (hwReadKraus c r * τ * (hwReadKraus c r)ᴴ) * Pj).trace.re
      ≤ ∑ r, (hwReadKraus c r * τ * (hwReadKraus c r)ᴴ).trace.re :=
        Finset.sum_le_sum fun r _ ↦ hproj _ (hτp.mul_mul_conjTranspose_same _)
    _ = τ.trace.re := by
        have hc : ∀ r, (hwReadKraus c r * τ * (hwReadKraus c r)ᴴ).trace =
            ((hwReadKraus c r)ᴴ * hwReadKraus c r * τ).trace := fun r ↦ by
          rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
        rw [← Complex.re_sum]
        congr 1
        simp only [hc]
        rw [← Matrix.trace_sum, ← Finset.sum_mul, sum_hwReadKraus, Matrix.one_mul]

end read

/-! ## Programs with weighted calls, under an invariant -/

section gradedRun

open IPFunctor QuantumRuntime

universe u v u₁ v₁ w

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} (Q : Matrix R.D R.D ℂ) (κ : spec.Port → ℕ)
  (P : ∀ (i : spec.Port) (E : QReg),
    Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop)
  (η : ℝ≥0∞) (d : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)

/-- `k √x = √(k² x)`. -/
theorem natCast_mul_rpow_inv_two (k : ℕ) (x : ℝ≥0∞) :
    (k : ℝ≥0∞) * x ^ (2⁻¹ : ℝ) = ((k : ℝ≥0∞) ^ 2 * x) ^ (2⁻¹ : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), Quantum.Xmss.Assembly.pow_two_rpow_inv_two]

/-- The step of a call of weight `k`: `√(w' + C) ≤ k √(η t) + √(w + (δ + C))` from
`w' ≤ (√w + k √(η t))² + δ`. -/
theorem rpow_inv_two_add_le_of_le_sq_mul {a b δ C t : ℝ≥0∞} (k : ℕ)
    (h : a ≤ (b ^ (2⁻¹ : ℝ) + k * (η * t) ^ (2⁻¹ : ℝ)) ^ 2 + δ) :
    (a + C) ^ (2⁻¹ : ℝ) ≤ k * (η * t) ^ (2⁻¹ : ℝ) + (b + (δ + C)) ^ (2⁻¹ : ℝ) := by
  have e : (k : ℝ≥0∞) * (η * t) ^ (2⁻¹ : ℝ) = ((k * (η * t) ^ (2⁻¹ : ℝ)) ^ 2) ^ (2⁻¹ : ℝ) :=
    (Quantum.Xmss.Assembly.pow_two_rpow_inv_two _).symm
  rw [e] at h ⊢
  exact Quantum.Xmss.Assembly.rpow_inv_two_add_le_of_le_sq h

/-- **Weighted calls, by induction on the program.** A call of port `i` presented an operator
satisfying `P` raises the event weight of its input `σ` to at most
`(√w + κ i √(η tr σ))² + d σ`. A program within the charge `n` of `κ`, all calls satisfying `P`,
ends with `√w ≤ n √(η tr ρ) + √(w ρ + ∑ d)`. -/
theorem rpow_inv_two_tsum_potential_run_le_weighted
    (hη : ∀ i (E : QReg) (τ : Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ),
      P i E τ → τ.PosSemidef →
        ∑' r, potential Q ((R.step i).branch r (MatrixMap.traceRight (spec.In i × R.D) E τ)) ≤
          (potential Q (MatrixMap.traceRight (spec.In i × R.D) E τ) ^ (2⁻¹ : ℝ) + κ i *
            (η * ENNReal.ofReal (MatrixMap.traceRight (spec.In i × R.D) E τ).trace.re) ^
              (2⁻¹ : ℝ)) ^ 2 + d i (MatrixMap.traceRight (spec.In i × R.D) E τ))
    {A : QReg} (x : QuantumComp L spec Ω A) (n : ℕ)
    (hx : IFreeM.IsChargeBound x (portCharge κ) n)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (hP : R.ForallQueries I P x ρ) :
    (∑' p, potential Q ((R.run I x).branch p ρ)) ^ (2⁻¹ : ℝ) ≤
      n * (η * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (potential Q ρ + R.totalWeight I d x ρ) ^ (2⁻¹ : ℝ) := by
  classical
  induction x using QuantumComp.inductionOn generalizing n with
  | pure B y =>
    rw [run_pure, tsum_eq_single (⟨_, y⟩ : Σ u, Ω u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply]
        simp [potential],
      DSubInstrument.branch_ret_self, LinearMap.id_apply]
    exact le_add_left (ENNReal.rpow_le_rpow le_self_add (by norm_num))
  | primBind B o k ih =>
    have hρb := fun b ↦ ((I o).frame R.D).posSemidef_branch_apply b hρ
    have hL : ∀ p, potential Q ((R.run I (QuantumComp.primBind o k)).branch p ρ) =
        ∑' b, potential Q ((R.run I (k b)).branch p (((I o).frame R.D).branch b ρ)) :=
      fun p ↦ by
        rw [run_primBind, DSubInstrument.branch_bind_apply]
        exact potential_tsum Q ((((I o).frame R.D).isCPTNIFamily.comp_eval
          (fun b ↦ (R.run I (k b)).isCPTNIFamily) p).summable_apply ρ)
          fun b ↦ (R.run I (k b)).posSemidef_branch_apply p (hρb b)
    simp only [hL]
    rw [ENNReal.tsum_comm]
    rw [isChargeBound_portCharge_primBind_iff] at hx
    have hm : ∀ b, (n : ℝ≥0∞) * (η * ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re) ^
        (2⁻¹ : ℝ) = ∑' j : ℕ, (if j = 0 then (n : ℝ≥0∞) ^ 2 * (η *
          ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re) else 0) ^ (2⁻¹ : ℝ) := by
      intro b
      rw [tsum_eq_single 0 fun j hj ↦ by
        simp [hj, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]]
      simp only [↓reduceIte]
      exact natCast_mul_rpow_inv_two _ _
    refine (rpow_inv_two_tsum_le_of_le_add_tsum
      (L := fun b ↦ ∑' p, potential Q ((R.run I (k b)).branch p (((I o).frame R.D).branch b ρ)))
      (t := fun b ↦ potential Q (((I o).frame R.D).branch b ρ) +
        R.totalWeight I d (k b) (((I o).frame R.D).branch b ρ))
      (m := fun j b ↦ if j = 0 then (n : ℝ≥0∞) ^ 2 * (η *
        ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re) else 0)
      fun b ↦ ((ih b n (hx b) (hρb b) (hP b)).trans_eq (by rw [hm b, add_comm]))).trans ?_
    rw [add_comm]
    have h0 : ∑' j : ℕ, (∑' b, if j = 0 then (n : ℝ≥0∞) ^ 2 * (η *
        ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re) else 0) ^ (2⁻¹ : ℝ) ≤
        n * (η * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
      rw [tsum_eq_single 0 fun j hj ↦ by
        simp [hj, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]]
      simp only [↓reduceIte]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      calc ((n : ℝ≥0∞) ^ 2 * (η * ∑' b,
            ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re)) ^ (2⁻¹ : ℝ)
          ≤ ((n : ℝ≥0∞) ^ 2 * (η * ENNReal.ofReal ρ.trace.re)) ^ (2⁻¹ : ℝ) := by
            gcongr
            exact ((I o).frame R.D).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
        _ = n * (η * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
            exact (natCast_mul_rpow_inv_two _ _).symm
    gcongr
    rw [ENNReal.tsum_add, totalWeight_primBind]
    gcongr
    exact tsum_potential_frame_le Q (I o) hρ
  | queryBind B i E ℓ k ih =>
    have hρr := fun r ↦ (R.queryStep i E ℓ).posSemidef_branch_apply r hρ
    have hL : ∀ p, potential Q ((R.run I (QuantumComp.queryBind i E ℓ k)).branch p ρ) =
        ∑' r, potential Q ((R.run I (k r)).branch p ((R.queryStep i E ℓ).branch r ρ)) :=
      fun p ↦ by
        rw [run_queryBind, DSubInstrument.branch_bind_apply]
        exact potential_tsum Q (((R.queryStep i E ℓ).isCPTNIFamily.comp_eval
          (fun r ↦ (R.run I (k r)).isCPTNIFamily) p).summable_apply ρ)
          fun r ↦ (R.run I (k r)).posSemidef_branch_apply p (hρr r)
    simp only [hL]
    rw [ENNReal.tsum_comm]
    rw [isChargeBound_portCharge_queryBind_iff] at hx
    have hpot : ∑' r, potential Q ((R.queryStep i E ℓ).branch r ρ) =
        ∑' r, potential Q ((R.step i).branch r (callInput ℓ R.D ρ)) :=
      tsum_congr fun r ↦ potential_queryStep R Q i E ℓ r ρ
    rw [totalWeight_queryBind]
    have hτ := (SubInstrument.relabel (queryEquivIn ℓ R.D)).posSemidef_branch_apply () hρ
    set n' := n - κ i
    have hk := fun r ↦ ih r n' (hx.2 r) (hρr r) (hP.2 r)
    have hm : ∀ r, (n' : ℝ≥0∞) * (η * ENNReal.ofReal
        ((R.queryStep i E ℓ).branch r ρ).trace.re) ^ (2⁻¹ : ℝ) = ∑' j : ℕ, (if j = 0 then
          (n' : ℝ≥0∞) ^ 2 * (η * ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re)
          else 0) ^ (2⁻¹ : ℝ) := by
      intro r
      rw [tsum_eq_single 0 fun j hj ↦ by
        simp [hj, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]]
      simp only [↓reduceIte]
      exact natCast_mul_rpow_inv_two _ _
    refine (rpow_inv_two_tsum_le_of_le_add_tsum
      (L := fun r ↦ ∑' p, potential Q ((R.run I (k r)).branch p
        ((R.queryStep i E ℓ).branch r ρ)))
      (t := fun r ↦ potential Q ((R.queryStep i E ℓ).branch r ρ) +
        R.totalWeight I d (k r) ((R.queryStep i E ℓ).branch r ρ))
      (m := fun j r ↦ if j = 0 then (n' : ℝ≥0∞) ^ 2 *
        (η * ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re) else 0)
      fun r ↦ (hk r).trans_eq (by rw [hm r, add_comm])).trans ?_
    have hq0 := hη i E _ hP.1 hτ
    change ∑' r, potential Q ((R.step i).branch r (callInput ℓ R.D ρ)) ≤
      (potential Q (callInput ℓ R.D ρ) ^ (2⁻¹ : ℝ) +
        κ i * (η * ENNReal.ofReal (callInput ℓ R.D ρ).trace.re) ^ (2⁻¹ : ℝ)) ^ 2 +
          d i (callInput ℓ R.D ρ) at hq0
    rw [potential_callInput, trace_callInput, ← hpot] at hq0
    rw [ENNReal.tsum_add]
    refine (add_le_add (rpow_inv_two_add_le_of_le_sq_mul η (κ i) hq0) le_rfl).trans ?_
    have h0 : ∑' j : ℕ, (∑' r, if j = 0 then (n' : ℝ≥0∞) ^ 2 * (η *
        ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re) else 0) ^ (2⁻¹ : ℝ) ≤
        n' * (η * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
      rw [tsum_eq_single 0 fun j hj ↦ by
        simp [hj, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]]
      simp only [↓reduceIte]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      calc ((n' : ℝ≥0∞) ^ 2 * (η * ∑' r,
            ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re)) ^ (2⁻¹ : ℝ)
          ≤ ((n' : ℝ≥0∞) ^ 2 * (η * ENNReal.ofReal ρ.trace.re)) ^ (2⁻¹ : ℝ) := by
            gcongr
            exact (R.queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
        _ = n' * (η * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
            exact (natCast_mul_rpow_inv_two _ _).symm
    have hn : (n : ℝ≥0∞) = κ i + n' := by
      rw [← Nat.cast_add]
      exact congrArg _ (by omega)
    calc (κ i : ℝ≥0∞) * (η * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
          (potential Q ρ + (d i (callInput ℓ R.D ρ) + ∑' r, R.totalWeight I d (k r)
            ((R.queryStep i E ℓ).branch r ρ))) ^ (2⁻¹ : ℝ) +
          ∑' j : ℕ, (∑' r, if j = 0 then (n' : ℝ≥0∞) ^ 2 * (η *
            ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re) else 0) ^ (2⁻¹ : ℝ)
        ≤ κ i * (η * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
          (potential Q ρ + (d i (callInput ℓ R.D ρ) + ∑' r, R.totalWeight I d (k r)
            ((R.queryStep i E ℓ).branch r ρ))) ^ (2⁻¹ : ℝ) +
          n' * (η * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by gcongr
      _ = _ := by rw [hn]; ring

/-- **The weighted event bound under an invariant**: from a positive semidefinite `ρ`, a program
within the charge `n` of the weights `κ`, all calls satisfying `P`, ends with event weight
`√w ≤ n √(η tr ρ) + √(w ρ + ∑ d)`. -/
theorem rpow_inv_two_eventWeight_le_weighted
    (hη : ∀ i (E : QReg) (τ : Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ),
      P i E τ → τ.PosSemidef →
        ∑' r, potential Q ((R.step i).branch r (MatrixMap.traceRight (spec.In i × R.D) E τ)) ≤
          (potential Q (MatrixMap.traceRight (spec.In i × R.D) E τ) ^ (2⁻¹ : ℝ) + κ i *
            (η * ENNReal.ofReal (MatrixMap.traceRight (spec.In i × R.D) E τ).trace.re) ^
              (2⁻¹ : ℝ)) ^ 2 + d i (MatrixMap.traceRight (spec.In i × R.D) E τ))
    {A : QReg} (x : QuantumComp L spec Ω A) (n : ℕ)
    (hx : IFreeM.IsChargeBound x (portCharge κ) n)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (hP : R.ForallQueries I P x ρ) :
    R.eventWeight I Q x ρ ^ (2⁻¹ : ℝ) ≤
      n * (η * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (potential Q ρ + R.totalWeight I d x ρ) ^ (2⁻¹ : ℝ) := by
  rw [eventWeight_eq_tsum_potential]
  exact rpow_inv_two_tsum_potential_run_le_weighted R I Q κ P η d hη x n hx hρ hP

end gradedRun

end Quantum.StdModel.Qrom

end
