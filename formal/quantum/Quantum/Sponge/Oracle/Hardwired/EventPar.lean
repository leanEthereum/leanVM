module

public import Quantum.Sponge.Oracle.Parallel
public import Quantum.Sponge.Oracle.Hardwired.Mixed
public import Quantum.Par.Spec

@[expose] public section

/-!
# The event bound graded by rounds

The parallel runtime of the hardwired runtime answers a round of `w` calls of one sponge port by
the product of the `w` calls on its slots (`roundKraus_spongeHardwired`).

* **Rounds of `h`** (`rpow_inv_two_potential_hRound_le`): by the parallel transition lemma, a
  round of width `w` raises the square root of the weight of a union of one-cell events by at
  most `√(6 ε w tr σ)`.
* **Programs with rounds** (`rpow_inv_two_tsum_potential_run_le_rounds`): a quantum port raising
  the event amplitude by `√(α w tr σ)` for a round of width `w`, in a program of at most `d`
  rounds of total width `q`, contributes `√(α d q)` in total. Over the rounds this is
  Cauchy-Schwarz: a round of width `w` with `d - 1` rounds of total width `q - w` left satisfies
  `√w + √((d - 1)(q - w)) ≤ √(d q)` (`sqrt_round_le`).
* **The event bound** (`rpow_inv_two_eventWeight_spongeHardwiredRuntime_par_le`): for a union
  of one-cell events, a program of rounds of `h` and single calls, with `q` sponge calls in `d`
  rounds, ends with `√w ≤ √(6 ε d q) + √(∑ d)`, the classical costs as in the sequential bound.
  The same for the hardwired runtime extended by classical ports
  (`rpow_inv_two_eventWeight_extend_par_le`).
-/

open Matrix IPFunctor
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

namespace Quantum.Par

open Quantum QuantumRuntime Sponge

/-! ## Rounds as products of calls on slots -/

section slots

variable {S N : Type} [Fintype S] [DecidableEq S] [Fintype N] [DecidableEq N]

/-- Conjugating by a bijection reindexes. -/
theorem basisMatrix_mul_mul_basisMatrix_symm {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (e : n ≃ m) (X : Matrix n n ℂ) :
    basisMatrix e * X * basisMatrix e.symm = X.submatrix e.symm e.symm := by
  ext b a
  rw [mul_basisMatrix_apply, basisMatrix_equiv_mul_apply]
  rfl

/-- A round tensored with an identity and reindexed is the round of the reindexed calls. -/
theorem roundProd_kronecker_submatrix {n m O : Type*} [Fintype n] [Fintype m] [Fintype O]
    [DecidableEq n] [DecidableEq m] [DecidableEq O] (e : m ≃ n × O) :
    ∀ {w : ℕ} (V : Fin w → Matrix n n ℂ),
      (roundProd V ⊗ₖ (1 : Matrix O O ℂ)).submatrix e e =
        roundProd (fun j ↦ (V j ⊗ₖ (1 : Matrix O O ℂ)).submatrix e e)
  | 0, _ => by rw [roundProd_zero, roundProd_zero, one_kronecker_one, submatrix_one_equiv]
  | _ + 1, V => by
      rw [roundProd_succ, roundProd_succ, ← roundProd_kronecker_submatrix e (fun i ↦ V i.succ),
        submatrix_mul_equiv _ _ _ e, ← mul_kronecker_mul, Matrix.one_mul]

omit [Fintype S] [DecidableEq S] in
theorem rest_succ_iff {w : ℕ} (j : Fin w) (a a' : Fin (w + 1) → S) :
    ((fun i : {i // i ≠ j.succ} ↦ a' i) = fun i : {i // i ≠ j.succ} ↦ a i) ↔
      ((fun i : {i // i ≠ j} ↦ Fin.tail a' i) = fun i : {i // i ≠ j} ↦ Fin.tail a i) ∧
        a' 0 = a 0 := by
  constructor
  · intro h
    exact ⟨funext fun i ↦ congrFun h ⟨i.1.succ, fun e ↦ i.2 (Fin.succ_injective _ e)⟩,
      congrFun h ⟨0, (Fin.succ_ne_zero j).symm⟩⟩
  · rintro ⟨h1, h2⟩
    funext ⟨i, hi⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · exact h2
    · exact congrFun h1 ⟨k, fun e ↦ hi (by rw [e])⟩

omit [Fintype S] [DecidableEq S] in
theorem rest_zero_iff {w : ℕ} (a a' : Fin (w + 1) → S) :
    ((fun i : {i // i ≠ (0 : Fin (w + 1))} ↦ a' i) = fun i : {i // i ≠ 0} ↦ a i) ↔
      Fin.tail a' = Fin.tail a := by
  constructor
  · intro h
    exact funext fun i ↦ congrFun h ⟨i.succ, Fin.succ_ne_zero i⟩
  · intro h
    funext ⟨i, hi⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · exact absurd rfl hi
    · exact congrFun h k

variable (S N) in
/-- Putting the first slot back in front of the other slots. -/
def consSlotEquiv (w : ℕ) : ((Fin w → S) × N) × S ≃ (Fin (w + 1) → S) × N where
  toFun y := (Fin.cons y.2 y.1.1, y.1.2)
  invFun x := ((Fin.tail x.1, x.2), x.1 0)
  left_inv y := by simp
  right_inv x := by simp

variable (S N) in
/-- Moving the first slot behind the other slots. -/
def swapSlotEquiv (w : ℕ) : (S × N) × (Fin w → S) ≃ ((Fin w → S) × N) × S where
  toFun y := ((y.2, y.1.2), y.1.1)
  invFun y := ((y.2, y.1.2), y.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype S] [Fintype N] [DecidableEq N] in
/-- The calls of the later slots of a round, after the first slot is split off. -/
theorem slotLift_kronecker_tail {w : ℕ} (j : Fin w) (M : Matrix (S × N) (S × N) ℂ) :
    (slotLift j M ⊗ₖ (1 : Matrix S S ℂ)).submatrix (consSlotEquiv S N w).symm
      (consSlotEquiv S N w).symm = slotLift j.succ M := by
  ext ⟨a', s'⟩ ⟨a, s⟩
  change (slotLift j M ⊗ₖ (1 : Matrix S S ℂ)) ((Fin.tail a', s'), a' 0) ((Fin.tail a, s), a 0) = _
  rw [kroneckerMap_apply, slotLift_apply, slotLift_apply, Matrix.one_apply]
  by_cases h : (fun i : {i // i ≠ j.succ} ↦ a' i) = fun i : {i // i ≠ j.succ} ↦ a i
  · obtain ⟨h1, h2⟩ := (rest_succ_iff j a a').1 h
    simp only [h1, h2, h, ↓reduceIte, mul_one]
    rfl
  · simp only [h, ↓reduceIte]
    split_ifs with h1 h2 <;>
      first | exact absurd ((rest_succ_iff j a a').2 ⟨h1, h2⟩) h | simp

omit [Fintype S] [Fintype N] [DecidableEq N] in
/-- The call of the first slot of a round. -/
theorem slotLift_kronecker_zero {w : ℕ} (M : Matrix (S × N) (S × N) ℂ) :
    (M ⊗ₖ (1 : Matrix (Fin w → S) (Fin w → S) ℂ)).submatrix
      ((swapSlotEquiv S N w).trans (consSlotEquiv S N w)).symm
      ((swapSlotEquiv S N w).trans (consSlotEquiv S N w)).symm = slotLift 0 M := by
  ext ⟨a', s'⟩ ⟨a, s⟩
  change (M ⊗ₖ (1 : Matrix (Fin w → S) (Fin w → S) ℂ)) ((a' 0, s'), Fin.tail a')
    ((a 0, s), Fin.tail a) = _
  rw [kroneckerMap_apply, slotLift_apply, Matrix.one_apply]
  simp only [rest_zero_iff]
  by_cases h : Fin.tail a' = Fin.tail a <;> simp [h]

/-- **A round of one port, one slot at a time**: the first slot, then the round of the other
slots, between the relabellings of the round step. -/
theorem roundProd_succ_slotLift {w : ℕ} (U : Matrix (S × N) (S × N) ℂ) :
    basisMatrix (consSlotEquiv S N w) *
        (roundProd (fun j : Fin w ↦ slotLift j U) ⊗ₖ (1 : Matrix S S ℂ)) *
        basisMatrix (swapSlotEquiv S N w) *
        (U ⊗ₖ (1 : Matrix (Fin w → S) (Fin w → S) ℂ)) *
        basisMatrix ((swapSlotEquiv S N w).trans (consSlotEquiv S N w)).symm =
      roundProd (fun j : Fin (w + 1) ↦ slotLift j U) := by
  have hJ : basisMatrix (consSlotEquiv S N w).symm *
      basisMatrix ((swapSlotEquiv S N w).trans (consSlotEquiv S N w)) =
        basisMatrix (swapSlotEquiv S N w) := by
    rw [← basisMatrix_comp]
    congr 1
  have hT : roundProd (fun j : Fin w ↦ slotLift j.succ U) =
      basisMatrix (consSlotEquiv S N w) *
        (roundProd (fun j : Fin w ↦ slotLift j U) ⊗ₖ (1 : Matrix S S ℂ)) *
        basisMatrix (consSlotEquiv S N w).symm := by
    rw [basisMatrix_mul_mul_basisMatrix_symm, roundProd_kronecker_submatrix]
    congr 1
    funext j
    exact (slotLift_kronecker_tail j U).symm
  have hZ : slotLift (0 : Fin (w + 1)) U =
      basisMatrix ((swapSlotEquiv S N w).trans (consSlotEquiv S N w)) *
        (U ⊗ₖ (1 : Matrix (Fin w → S) (Fin w → S) ℂ)) *
        basisMatrix ((swapSlotEquiv S N w).trans (consSlotEquiv S N w)).symm := by
    rw [basisMatrix_mul_mul_basisMatrix_symm]
    exact (slotLift_kronecker_zero U).symm
  rw [roundProd_succ, hT, hZ, ← hJ]
  simp only [Matrix.mul_assoc]

end slots
/-! ## Cauchy-Schwarz over the rounds -/

section scalar

theorem sqrt_add_sqrt_mul_le {x q d : ℝ} (hx : 0 ≤ x) (hxq : x ≤ q) (hd : 1 ≤ d) :
    √x + √((d - 1) * (q - x)) ≤ √(d * q) := by
  have hq : 0 ≤ q - x := by linarith
  have hd1 : 0 ≤ d - 1 := by linarith
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt (mul_nonneg hd1 hq)
  have h3 : √x * √((d - 1) * (q - x)) ≤ ((d - 1) * x + (q - x)) / 2 := by
    rw [← Real.sqrt_mul hx, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg ((d - 1) * x - (q - x))]
  rw [Real.le_sqrt (by positivity) (by nlinarith)]
  nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg ((d - 1) * (q - x))]

/-- One round of width `x` and `d - e` rounds of total width `q - x`, against `d` rounds of
total width `q`. -/
theorem sqrt_round_le {x q d e : ℕ} (hxq : x ≤ q) (hed : e ≤ d) (hxe : x = 0 ∨ 1 ≤ e) :
    √(x : ℝ) + √(((d - e) * (q - x) : ℕ) : ℝ) ≤ √((d * q : ℕ) : ℝ) := by
  rcases hxe with rfl | he
  · rw [Nat.cast_zero, Real.sqrt_zero, zero_add, Nat.sub_zero]
    exact Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.mul_le_mul_right q (Nat.sub_le d e)))
  · refine le_trans (add_le_add le_rfl (Real.sqrt_le_sqrt (Nat.cast_le.mpr
      (Nat.mul_le_mul_right (q - x) (Nat.sub_le_sub_left he d))))) ?_
    have hd : 1 ≤ d := he.trans hed
    have h := sqrt_add_sqrt_mul_le (x := (x : ℝ)) (q := (q : ℝ)) (d := (d : ℝ))
      (Nat.cast_nonneg x) (Nat.cast_le.mpr hxq) (by exact_mod_cast hd)
    push_cast [Nat.cast_sub hd, Nat.cast_sub hxq]
    exact h

theorem rpow_inv_two_round_le (α T : ℝ≥0∞) {x y z : ℕ} (h : √(x : ℝ) + √(y : ℝ) ≤ √(z : ℝ)) :
    (α * x * T) ^ (2⁻¹ : ℝ) + (α * y * T) ^ (2⁻¹ : ℝ) ≤ (α * z * T) ^ (2⁻¹ : ℝ) := by
  have e : ∀ n : ℕ, α * (n : ℝ≥0∞) * T = α * T * n := fun n ↦ by ring
  rw [e x, e y, e z, ENNReal.mul_rpow_of_nonneg (α * T) (x : ℝ≥0∞) (by norm_num),
    ENNReal.mul_rpow_of_nonneg (α * T) (y : ℝ≥0∞) (by norm_num),
    ENNReal.mul_rpow_of_nonneg (α * T) (z : ℝ≥0∞) (by norm_num), ← mul_add]
  gcongr
  rw [← ENNReal.ofReal_natCast x, ← ENNReal.ofReal_natCast y, ← ENNReal.ofReal_natCast z,
    ENNReal.ofReal_rpow_inv_two, ENNReal.ofReal_rpow_inv_two, ENNReal.ofReal_rpow_inv_two,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h

theorem rpow_two_mul_rpow_inv_two (x y : ℝ≥0∞) :
    (x ^ (2 : ℝ) * y) ^ (2⁻¹ : ℝ) = x * y ^ (2⁻¹ : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.rpow_rpow_inv two_ne_zero]

/-- `ℓ²` Minkowski for three series. -/
theorem rpow_inv_two_tsum_le_of_le_add_two {K : Type*} {t a c b : K → ℝ≥0∞}
    (h : ∀ k, t k ^ (2⁻¹ : ℝ) ≤ a k ^ (2⁻¹ : ℝ) + c k ^ (2⁻¹ : ℝ) + b k ^ (2⁻¹ : ℝ)) :
    (∑' k, t k) ^ (2⁻¹ : ℝ) ≤
      (∑' k, a k) ^ (2⁻¹ : ℝ) + (∑' k, c k) ^ (2⁻¹ : ℝ) + (∑' k, b k) ^ (2⁻¹ : ℝ) := by
  have hac : ∀ k, ((a k ^ (2⁻¹ : ℝ) + c k ^ (2⁻¹ : ℝ)) ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) =
      a k ^ (2⁻¹ : ℝ) + c k ^ (2⁻¹ : ℝ) := fun k ↦ ENNReal.rpow_rpow_inv two_ne_zero _
  refine (Quantum.rpow_inv_two_tsum_le_of_le_add (a := fun k ↦
    (a k ^ (2⁻¹ : ℝ) + c k ^ (2⁻¹ : ℝ)) ^ (2 : ℝ)) (b := b)
    fun k ↦ (h k).trans_eq (by rw [hac])).trans ?_
  exact add_le_add (Quantum.rpow_inv_two_tsum_le_of_le_add fun k ↦ (hac k).le) le_rfl

/-- If `√a ≤ √b + s`, then `√(a + C) ≤ s + √(b + C)`. -/
theorem rpow_inv_two_add_le_of_le_two {a b C s : ℝ≥0∞}
    (h : a ^ (2⁻¹ : ℝ) ≤ b ^ (2⁻¹ : ℝ) + s) :
    (a + C) ^ (2⁻¹ : ℝ) ≤ s + (b + C) ^ (2⁻¹ : ℝ) := by
  have h' := rpow_inv_two_add_le_of_le (a := a) (b := b) (c := s ^ (2 : ℝ)) (C := C)
    (by rwa [ENNReal.rpow_rpow_inv two_ne_zero])
  rwa [ENNReal.rpow_rpow_inv two_ne_zero] at h'

end scalar

/-! ## The event bound for programs with rounds -/

section rounds

universe u v w u₁ v₁

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Xr : QReg → Type w} (Q : Matrix R.D R.D ℂ) (cls : spec.Port → Bool)
  (g : R.D → ℕ)

/-- One call of a port raising the grade by at most `γ`. -/
theorem querySupportedOn_queryStep_of_step (i : spec.Port) (γ : ℕ)
    (hR : ∀ r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + γ))
          ((R.step i).branch r σ))
    {A : QReg} {t : ℕ} (E : QReg) (ℓ : A ≃ spec.In i × E) (r : spec.Result i)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (h : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) :
    QuerySupportedOn (fun m : (spec.Out i × E) × R.D ↦ g m.2) (Set.Iic (t + γ))
      ((R.queryStep i E ℓ).branch r ρ) := by
  rw [QuantumRuntime.queryStep_branch_apply, DSubInstrument.branch_frame_apply]
  have h₁ := (h.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
    (q' := fun m : (spec.In i × R.D) × E ↦ g m.1.2) (S' := Set.Iic t) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  have h₂ := QuerySupportedOn.amplify_fst (q := fun m : spec.In i × R.D ↦ g m.2)
    (q' := fun m : spec.Out i × R.D ↦ g m.2) (fun σ hσ ↦ hR r t σ hσ) h₁
  refine (h₂.branch_relabel (QuantumRuntime.queryEquivOut _ R.D E)).imp fun m hm ↦ ?_
  obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivOut _ R.D E).surjective m
  rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

/-- **The event bound with rounds, by induction on the program.** A quantum port
(`cls i = false`) raises the event amplitude by at most `√(α cq i tr σ) + cr i √(β tr σ)` on
inputs of grade at most `G`; a classical port raises the weight by `d i σ`. Every port raises
the grade by at most `cg i`. From a state of grade at most `t`, with budgets `q'` for `cq`, `dr`
for `cd` (at least one for every quantum call with `cq i > 0`), `rr` for `cr` and `T` for `cg`,
`t + T ≤ G`, the summed potential of the leaves satisfies
`√w ≤ √(α dr q' tr ρ) + rr √(β tr ρ) + √(w ρ + ∑ d)`. -/
theorem rpow_inv_two_tsum_potential_run_le_rounds (cq cd cr cg : spec.Port → ℕ)
    (hg : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + cg i))
          ((R.step i).branch r σ))
    (α β : ℝ≥0∞) (G : ℕ) (hδ : ∀ i, cls i = false → cq i = 0 ∨ 1 ≤ cd i)
    (hq : ∀ i, cls i = false → ∀ σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ,
      σ.PosSemidef → QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic G) σ →
        (∑' r, potential Q ((R.step i).branch r σ)) ^ (2⁻¹ : ℝ) ≤
          potential Q σ ^ (2⁻¹ : ℝ) + (α * (cq i : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) +
            (cr i : ℝ≥0∞) * (β * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ))
    (d : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (hc : ∀ i, cls i = true → ∀ σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ,
      σ.PosSemidef → ∑' r, potential Q ((R.step i).branch r σ) ≤ potential Q σ + d i σ)
    {A : QReg} (x : QuantumComp L spec Xr A) (q' dr rr T t : ℕ)
    (hxq : IFreeM.IsChargeBound x (portCharge cq) q')
    (hxd : IFreeM.IsChargeBound x (portCharge cd) dr)
    (hxr : IFreeM.IsChargeBound x (portCharge cr) rr)
    (hxT : IFreeM.IsChargeBound x (portCharge cg) T) (htG : t + T ≤ G)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef)
    (hρg : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) :
    (∑' p, potential Q ((R.run I x).branch p ρ)) ^ (2⁻¹ : ℝ) ≤
      (α * ((dr * q' : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (rr : ℝ≥0∞) * (β * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (potential Q ρ + R.totalWeight I d x ρ) ^ (2⁻¹ : ℝ) := by
  classical
  induction x using QuantumComp.inductionOn generalizing q' dr rr T t with
  | pure B y =>
    rw [run_pure, tsum_eq_single (⟨_, y⟩ : Σ u, Xr u) fun p hp ↦ by
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
    rw [isChargeBound_portCharge_primBind_iff] at hxq hxd hxr hxT
    refine (rpow_inv_two_tsum_le_of_le_add_two
      (t := fun b ↦ ∑' p, potential Q ((R.run I (k b)).branch p (((I o).frame R.D).branch b ρ)))
      (a := fun b ↦ α * ((dr * q' : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re)
      (c := fun b ↦ (rr : ℝ≥0∞) ^ (2 : ℝ) * (β *
        ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re))
      (b := fun b ↦ potential Q (((I o).frame R.D).branch b ρ) +
        R.totalWeight I d (k b) (((I o).frame R.D).branch b ρ))
      fun b ↦ (ih b q' dr rr T t (hxq b) (hxd b) (hxr b) (hxT b) htG (hρb b)
        (hρg.amplify_snd _)).trans_eq (by rw [rpow_two_mul_rpow_inv_two])).trans ?_
    have htr := ((I o).frame R.D).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
    gcongr
    · rw [ENNReal.tsum_mul_left]
      gcongr
    · rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, rpow_two_mul_rpow_inv_two]
      gcongr
    · rw [ENNReal.tsum_add, totalWeight_primBind]
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
    rw [isChargeBound_portCharge_queryBind_iff] at hxq hxd hxr hxT
    have hσ := posSemidef_callInput ℓ hρ
    have hσg : QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t)
        (callInput ℓ R.D ρ) := hρg.callInput ℓ
    have hρrg := fun r ↦ querySupportedOn_queryStep_of_step R g i (cg i)
      (fun r t σ hσ ↦ hg i r t σ hσ) E ℓ r hρg
    have hpot : ∑' r, potential Q ((R.queryStep i E ℓ).branch r ρ) =
        ∑' r, potential Q ((R.step i).branch r (callInput ℓ R.D ρ)) :=
      tsum_congr fun r ↦ potential_queryStep R Q i E ℓ r ρ
    have htr : ∑' r, ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re ≤
        ENNReal.ofReal ρ.trace.re := (R.queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
    have hk := fun r ↦ ih r (q' - cq i) (dr - cd i) (rr - cr i) (T - cg i) (t + cg i)
      (hxq.2 r) (hxd.2 r) (hxr.2 r) (hxT.2 r) (by omega) (hρr r) (hρrg r)
    refine (rpow_inv_two_tsum_le_of_le_add_two
      (t := fun r ↦ ∑' p, potential Q ((R.run I (k r)).branch p
        ((R.queryStep i E ℓ).branch r ρ)))
      (a := fun r ↦ α * (((dr - cd i) * (q' - cq i) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re)
      (c := fun r ↦ ((rr - cr i : ℕ) : ℝ≥0∞) ^ (2 : ℝ) * (β *
        ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re))
      (b := fun r ↦ potential Q ((R.queryStep i E ℓ).branch r ρ) +
        R.totalWeight I d (k r) ((R.queryStep i E ℓ).branch r ρ))
      fun r ↦ (hk r).trans_eq (by rw [rpow_two_mul_rpow_inv_two])).trans ?_
    have ha : (∑' r, α * (((dr - cd i) * (q' - cq i) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re) ≤
          α * (((dr - cd i) * (q' - cq i) : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re := by
      rw [ENNReal.tsum_mul_left]
      gcongr
    have hb : (∑' r, ((rr - cr i : ℕ) : ℝ≥0∞) ^ (2 : ℝ) * (β *
        ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re)) ^ (2⁻¹ : ℝ) ≤
          ((rr - cr i : ℕ) : ℝ≥0∞) * (β * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, rpow_two_mul_rpow_inv_two]
      gcongr
    rw [totalWeight_queryBind, ENNReal.tsum_add]
    cases hci : cls i
    · -- A quantum call.
      have hq0 := hq i hci _ hσ (hσg.mono (Set.Iic_subset_Iic.mpr (by omega)))
      rw [potential_callInput, trace_callInput, ← hpot, add_assoc] at hq0
      have h2 := rpow_inv_two_add_le_of_le_two (C := ∑' r, R.totalWeight I d (k r)
        ((R.queryStep i E ℓ).branch r ρ)) hq0
      have hs := rpow_inv_two_round_le α (ENNReal.ofReal ρ.trace.re)
        (sqrt_round_le (x := cq i) (q := q') (d := dr) (e := cd i) hxq.1 hxd.1 (hδ i hci))
      have hr : ((rr - cr i : ℕ) : ℝ≥0∞) + cr i = rr := by
        rw [← Nat.cast_add, Nat.sub_add_cancel hxr.1]
      calc _ ≤ (α * (((dr - cd i) * (q' - cq i) : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re) ^
              (2⁻¹ : ℝ) + ((rr - cr i : ℕ) : ℝ≥0∞) * (β * ENNReal.ofReal ρ.trace.re) ^
                (2⁻¹ : ℝ) + ((α * (cq i : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
              (cr i : ℝ≥0∞) * (β * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
              (potential Q ρ + ∑' r, R.totalWeight I d (k r)
                ((R.queryStep i E ℓ).branch r ρ)) ^ (2⁻¹ : ℝ)) :=
            add_le_add (add_le_add (ENNReal.rpow_le_rpow ha (by norm_num)) hb) h2
        _ = ((α * (cq i : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
              (α * (((dr - cd i) * (q' - cq i) : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re) ^
                (2⁻¹ : ℝ)) + (((rr - cr i : ℕ) : ℝ≥0∞) + cr i) *
                  (β * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
              (potential Q ρ + ∑' r, R.totalWeight I d (k r)
                  ((R.queryStep i E ℓ).branch r ρ)) ^ (2⁻¹ : ℝ) := by ring
        _ ≤ _ := by
            rw [hr]
            gcongr
            exact le_add_self
    · -- A classical call.
      have hc0 := hc i hci _ hσ
      rw [potential_callInput, ← hpot] at hc0
      refine add_le_add (add_le_add (ENNReal.rpow_le_rpow (ha.trans ?_) (by norm_num))
        (hb.trans ?_)) (ENNReal.rpow_le_rpow ?_ (by norm_num))
      · gcongr <;> omega
      · gcongr
        omega
      · rw [← add_assoc]
        gcongr

end rounds

/-! ## The rounds of the hardwired runtime -/

section hardwired

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z]

variable (X Z) in
/-- The Kraus operators of the steps of the hardwired runtime. -/
noncomputable def hwKraus (W₀ : Hw X Z) (m₀ : M) :
    ∀ i : (hwSpec X Z M).Port, (hwSpec X Z M).Result i →
      Matrix ((hwSpec X Z M).Out i × HwReg X Z M) ((hwSpec X Z M).In i × HwReg X Z M) ℂ
  | .inl (.inl p), _ => (spongeHardwired X Z W₀ m₀).U p
  | .inl (.inr c), r => hwReadKraus c r
  | .inr c, r => hwProgKraus c r

theorem spongeHardwiredRuntime_step_branch (W₀ : Hw X Z) (m₀ : M)
    (i : (hwSpec X Z M).Port) (r : (hwSpec X Z M).Result i) :
    ((spongeHardwiredRuntime X Z W₀ m₀).step i).branch r =
      MatrixMap.conj (hwKraus X Z W₀ m₀ i r) := by
  rcases i with (p | c) | c
  · exact spongeHardwiredRuntime_step_sponge W₀ m₀ p r
  · exact spongeHardwiredRuntime_step_read W₀ m₀ c r
  · exact spongeHardwiredRuntime_step_prog W₀ m₀ c r

/-- **A round of one sponge port is the product of its calls on the slots.** -/
theorem roundKraus_spongeHardwired (W₀ : Hw X Z) (m₀ : M) (p : SpongePort) :
    ∀ {w : ℕ} (rs : RoundResult (hwSpec X Z M)
      (fun _ : Fin w ↦ (.inl (.inl p) : (hwSpec X Z M).Port))),
      (spongeHardwiredRuntime X Z W₀ m₀).roundKraus (hwKraus X Z W₀ m₀)
          (fun _ : Fin w ↦ (.inl (.inl p) : (hwSpec X Z M).Port)) rs =
        roundProd (fun j : Fin w ↦
          slotLift (S := spongeIn X Z p) (N := HwReg X Z M) j ((spongeHardwired X Z W₀ m₀).U p))
  | 0, rs => by
      simp only [QuantumRuntime.roundKraus]
      rw [roundProd_zero]
      refine (congrArg basisMatrix (funext fun y ↦ ?_)).trans basisMatrix_id
      exact Prod.ext (funext fun i ↦ i.elim0) rfl
  | w + 1, rs => by
      simp only [QuantumRuntime.roundKraus]
      rw [roundKraus_spongeHardwired W₀ m₀ p (Fin.tail rs)]
      exact roundProd_succ_slotLift _

/-- A round of unitary calls is unitary. -/
theorem roundProd_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n] :
    ∀ {w : ℕ} {V : Fin w → Matrix n n ℂ}, (∀ j, V j ∈ unitaryGroup n ℂ) →
      roundProd V ∈ unitaryGroup n ℂ
  | 0, _, _ => by rw [roundProd_zero]; exact one_mem _
  | _ + 1, _, hV => mul_mem (roundProd_mem_unitaryGroup fun j ↦ hV j.succ) (hV 0)

/-- The rounds of port `h` as a product of slot calls. -/
noncomputable abbrev hRound (w : ℕ) :
    Matrix ((Fin w → Z × X) × HwReg X Z M) ((Fin w → Z × X) × HwReg X Z M) ℂ :=
  roundProd (fun j : Fin w ↦ slotLift j (portMat (hwReadH X Z M) (compressReg X Z M)))

theorem hRound_mem_unitaryGroup (w : ℕ) (W₀ : Hw X Z) (m₀ : M) :
    hRound (X := X) (Z := Z) (M := M) w ∈ unitaryGroup _ ℂ :=
  roundProd_mem_unitaryGroup fun _ ↦ onFactor_mem_unitaryGroup _
    ((spongeHardwired X Z W₀ m₀).unitary SpongePort.h)

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M]
  [AddCommGroup X] [AddCommGroup Z] in
/-- A round of calls raising a grade by at most one raises it by at most its width. -/
theorem roundProd_grade_le {n : Type*} [Fintype n] [DecidableEq n] (g : n → ℕ) :
    ∀ {w : ℕ} (V : Fin w → Matrix n n ℂ), (∀ j x x', V j x' x ≠ 0 → g x' ≤ g x + 1) →
      ∀ x x', roundProd V x' x ≠ 0 → g x' ≤ g x + w
  | 0, _, _, x, x', h => by
      have he : x' = x := preserves_one (fun x : n ↦ x) x x' h
      rw [he]
      exact Nat.le_add_right _ _
  | w + 1, V, hV, x, x', h => by
      rw [roundProd_succ, Matrix.mul_apply] at h
      obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have h1 := roundProd_grade_le g (fun j ↦ V j.succ) (fun j ↦ hV j.succ) y x'
        (left_ne_zero_of_mul hy)
      have h2 := hV 0 x y (right_ne_zero_of_mul hy)
      omega

/-- A round of port `h` raises the grade by at most its width. -/
theorem dbGrade_le_of_hRound_ne_zero (W₀ : Hw X Z) (m₀ : M) {w : ℕ}
    (x x' : (Fin w → Z × X) × HwReg X Z M) (h : hRound (X := X) (Z := Z) (M := M) w x' x ≠ 0) :
    dbGrade x'.2.1 ≤ dbGrade x.2.1 + w :=
  roundProd_grade_le (fun x : (Fin w → Z × X) × HwReg X Z M ↦ dbGrade x.2.1) _
    (fun j x x' hx ↦ by
      rw [slotLift_apply] at hx
      split_ifs at hx
      · exact dbGrade_le_of_spongeHardwired_U_ne_zero W₀ m₀ .h (x.1 j) (x'.1 j) x.2 x'.2 hx
      · exact absurd rfl hx) x x' h

end hardwired

/-! ## The event bound of the parallel hardwired runtime -/

section par

universe u v w

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z]

variable (X Z M) in
/-- The rounds of the parallel hardwired runtime are rounds of port `h`. -/
abbrev hPort : Unit → (hwSpec X Z M).Port := fun _ ↦ .inl (.inl .h)

section charges

variable {sp : QuantumOracleSpec.{0, 0}} {Q : Type} (port : Q → sp.Port) (cls : sp.Port → Bool)

/-- The classical ports of the parallel signature: the classical single ports. -/
def parCls : (parSpec sp port).Port → Bool
  | .inl i => cls i
  | .inr _ => false

/-- The quantum calls of a command: one for a single quantum call, the width for a round. -/
def spongeWidth : (parSpec sp port).Port → ℕ :=
  widthCharge port fun i ↦ if cls i then 0 else 1

/-- The classical calls of a command. -/
def clsCount : (parSpec sp port).Port → ℕ :=
  widthCharge port fun i ↦ if cls i then 1 else 0

/-- Whether a command is a single quantum call or a round with a quantum call. -/
def spongeRounds : (parSpec sp port).Port → ℕ :=
  roundCharge port fun i ↦ if cls i then 0 else 1

variable {port cls}

theorem spongeWidth_round (hport : ∀ a, cls (port a) = false) (w : ℕ) (f : Fin w → Q) :
    spongeWidth port cls (.inr (.round w f)) = w := by
  simp [spongeWidth, widthCharge, hport]

theorem clsCount_round (hport : ∀ a, cls (port a) = false) (w : ℕ) (f : Fin w → Q) :
    clsCount port cls (.inr (.round w f)) = 0 := by
  simp [clsCount, widthCharge, hport]

theorem spongeWidth_add_clsCount_inl (i : sp.Port) :
    spongeWidth port cls (.inl i) + clsCount port cls (.inl i) = 1 := by
  simp only [spongeWidth, clsCount, widthCharge]
  cases cls i <;> rfl

theorem spongeWidth_eq_zero_or (i : (parSpec sp port).Port) :
    spongeWidth port cls i = 0 ∨ 1 ≤ spongeRounds port cls i := by
  unfold spongeRounds roundCharge
  by_cases h : widthCharge port (fun i ↦ if cls i then 0 else 1) i = 0
  · exact Or.inl h
  · right
    simp [h]

end charges

/-- Charges add up. -/
theorem isChargeBound_portCharge_add {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{0, 0}}
    {Xr : QReg → Type w} (c₁ c₂ : spec.Port → ℕ) {A : QReg} (x : QuantumComp L spec Xr A)
    {n₁ n₂ : ℕ} (h₁ : IFreeM.IsChargeBound x (portCharge c₁) n₁)
    (h₂ : IFreeM.IsChargeBound x (portCharge c₂) n₂) :
    IFreeM.IsChargeBound x (portCharge fun i ↦ c₁ i + c₂ i) (n₁ + n₂) := by
  induction x using QuantumComp.inductionOn generalizing n₁ n₂ with
  | pure B y => trivial
  | primBind B o k ih =>
    rw [isChargeBound_portCharge_primBind_iff] at h₁ h₂ ⊢
    exact fun b ↦ ih b (h₁ b) (h₂ b)
  | queryBind B i E ℓ k ih =>
    rw [isChargeBound_portCharge_queryBind_iff] at h₁ h₂ ⊢
    refine ⟨by omega, fun r ↦ ?_⟩
    have h := ih r (h₁.2 r) (h₂.2 r)
    rwa [show n₁ - c₁ i + (n₂ - c₂ i) = n₁ + n₂ - (c₁ i + c₂ i) by omega] at h

/-- The step of a round of the parallel hardwired runtime. -/
theorem par_step_round_branch (W₀ : Hw X Z) (m₀ : M) (w : ℕ) (f : Fin w → Unit)
    (rs : RoundResult (hwSpec X Z M) fun i ↦ hPort X Z M (f i)) :
    (((spongeHardwiredRuntime X Z W₀ m₀).par (hPort X Z M)).step (.inr (.round w f))).branch rs =
      MatrixMap.conj (hRound (X := X) (Z := Z) (M := M) w) := by
  have h := (spongeHardwiredRuntime X Z W₀ m₀).branch_roundStep_of_conj (hwKraus X Z W₀ m₀)
    (spongeHardwiredRuntime_step_branch W₀ m₀)
    (fun _ : Fin w ↦ (.inl (.inl .h) : (hwSpec X Z M).Port)) rs
  rw [roundKraus_spongeHardwired] at h
  exact h

/-- **One round of `h`.** On inputs of grade at most `n`, with the event a union of cell events
with fresh bound `ε` below `n + 1`, a round of width `w` raises the square root of the event
weight by at most `√(6 ε w tr σ)`. -/
theorem rpow_inv_two_potential_hRound_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (Sc : Z → Set (HwReg X Z M)) [∀ c, DecidablePred (· ∈ Sc c)] (hsub : ∀ c, Sc c ⊆ S)
    (hunion : ∀ s ∈ S, ∃ c, s ∈ Sc c)
    (hloc : ∀ c (s s' : HwReg X Z M), s'.1.1 c = s.1.1 c → s'.1.2 = s.1.2 → s'.2 = s.2 →
      (s' ∈ Sc c ↔ s ∈ Sc c))
    (hup : ∀ c W m, UpClosed (slice (Sc c) W m)) {n : ℕ} {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤)
    (hε : ∀ c W m, FreshBound (slice (Sc c) W m) (n + 1) ε) (W₀ : Hw X Z) (m₀ : M) (w : ℕ)
    {σ : Matrix ((Fin w → Z × X) × HwReg X Z M) ((Fin w → Z × X) × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef)
    (hσg : QuerySupportedOn (fun q : (Fin w → Z × X) × HwReg X Z M ↦ dbGrade q.2.1)
      (Set.Iic n) σ) :
    potential (hwProjector S) (MatrixMap.conj (hRound (X := X) (Z := Z) (M := M) w) σ) ^
        (2⁻¹ : ℝ) ≤
      potential (hwProjector S) σ ^ (2⁻¹ : ℝ) +
        (6 * ε * w * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) := by
  set U := hRound (X := X) (Z := Z) (M := M) w
  set Q := (1 : Matrix (Fin w → Z × X) (Fin w → Z × X) ℂ) ⊗ₖ hwProjector S
  have hQ : Q = labelProjector (fun x : (Fin w → Z × X) × HwReg X Z M ↦ decide (x.2 ∈ S))
      true := by
    simp only [Q, hwProjector, one_kronecker_labelProjector]
  have hpot : ∀ τ : Matrix ((Fin w → Z × X) × HwReg X Z M) ((Fin w → Z × X) × HwReg X Z M) ℂ,
      potential (hwProjector S) τ = ENNReal.ofReal (MatrixMap.conj Q τ).trace.re :=
    fun τ ↦ by rw [potential, MatrixMap.amplifyLeft_conj]
  rw [hpot, hpot, ← LinearMap.comp_apply, ← MatrixMap.conj_mul,
    show Q * U = U * Q + (Q * U - U * Q) by abel]
  refine (MatrixMap.ofReal_trace_conj_add_rpow_le hσ _ _).trans (add_le_add (le_of_eq ?_) ?_)
  · rw [MatrixMap.conj_mul, LinearMap.comp_apply,
      trace_conj_of_mem_unitaryGroup (hRound_mem_unitaryGroup w W₀ m₀)]
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    have hr0 : (0 : ℝ) ≤ w * (6 * ε.toReal) := by positivity
    have hn := l2_opNorm_commutator_hRound_le S Sc hsub hunion hloc hup hεtop hε W₀ m₀ w
    rw [← hQ] at hn
    have hcert := MatrixMap.posSemidef_scalar_sub_gram_of_norm_sq_le _
      ((pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hr0))
    refine (ofReal_trace_conj_le_of_certificate _ _ hr0 hcert hσ
      (hσg.conj_diagonal_eq_self fun q hq ↦ by simp [Set.mem_Iic.mp hq])).trans_eq ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_toReal hεtop, ENNReal.ofReal_natCast]
    norm_num
    ring

/-- Every program is within the zero charge. -/
theorem isChargeBound_zero_portCharge {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{0, 0}}
    {Xr : QReg → Type w} {A : QReg} (x : QuantumComp L spec Xr A) :
    IFreeM.IsChargeBound x (portCharge fun _ ↦ 0) 0 := by
  induction x using QuantumComp.inductionOn with
  | pure B y => trivial
  | primBind B o k ih => exact (isChargeBound_portCharge_primBind_iff _ o k 0).2 ih
  | queryBind B i E ℓ k ih =>
    exact (isChargeBound_portCharge_queryBind_iff _ i E ℓ k 0).2 ⟨le_rfl, ih⟩

/-- The charge of `Mixed` is the charge of `Par.Spec`. -/
theorem portCharge_eq_callCharge {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{0, 0}}
    (c : spec.Port → ℕ) : portCharge (L := L) c = callCharge c := by
  funext A cmd
  cases cmd <;> rfl

variable {L : LocalSig.{u, v}} {Xr : QReg → Type w} {A : QReg}

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The event has no weight at the start. -/
theorem potential_start_eq_zero (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (W₀ : Hw X Z)
    (m₀ : M) (hempty : ((Database.empty, Database.empty, Database.empty), W₀, m₀) ∉ S)
    (ρ : SubState A) :
    potential (hwProjector S)
      (ρ.matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
        W₀, m₀) : HwReg X Z M)).matrix) = 0 := by
  have hz : hwProjector S * (SubState.basis (((Database.empty, Database.empty, Database.empty),
      W₀, m₀) : HwReg X Z M)).matrix = 0 := by
    rw [hwProjector, labelProjector, SubState.matrix_basis]
    ext a b
    rw [diagonal_mul, Matrix.single_apply, Matrix.zero_apply]
    by_cases h : ((Database.empty, Database.empty, Database.empty), W₀, m₀) = a ∧
        ((Database.empty, Database.empty, Database.empty), W₀, m₀) = b
    · rcases h with ⟨rfl, rfl⟩
      simp [hempty]
    · simp [h]
  rw [potential, MatrixMap.amplifyLeft_conj, MatrixMap.conj_apply,
    ← mul_kronecker_mul, hz, kronecker_zero, Matrix.zero_mul, Matrix.trace_zero,
    Complex.zero_re, ENNReal.ofReal_zero]

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The databases are empty at the start. -/
theorem querySupportedOn_start (W₀ : Hw X Z) (m₀ : M) (ρ : SubState A) :
    QuerySupportedOn (fun m : A × HwReg X Z M ↦ dbGrade m.2.1) (Set.Iic 0)
      (ρ.matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
        W₀, m₀) : HwReg X Z M)).matrix) := by
  intro m m' hm
  rw [SubState.matrix_basis, kroneckerMap_apply] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
  · exact False.elim (h rfl)

/-- The end of the event bound with rounds: no weight at the start, trace at most one. -/
theorem rpow_inv_two_rounds_finish {T P W τ ε : ℝ≥0∞} {d q : ℕ} (hP : P = 0) (hτ : τ ≤ 1)
    (h : T ^ (2⁻¹ : ℝ) ≤ (6 * ε * ((d * q : ℕ) : ℝ≥0∞) * τ) ^ (2⁻¹ : ℝ) +
      ((0 : ℕ) : ℝ≥0∞) * (0 * τ) ^ (2⁻¹ : ℝ) + (P + W) ^ (2⁻¹ : ℝ)) :
    T ^ (2⁻¹ : ℝ) ≤ (6 * ε * d * q) ^ (2⁻¹ : ℝ) + W ^ (2⁻¹ : ℝ) := by
  refine h.trans ?_
  rw [hP, zero_add, Nat.cast_zero, zero_mul, add_zero, Nat.cast_mul, ← mul_assoc]
  refine add_le_add (ENNReal.rpow_le_rpow ?_ (by norm_num)) le_rfl
  calc 6 * ε * d * q * τ ≤ 6 * ε * d * q * 1 := by gcongr
    _ = 6 * ε * d * q := mul_one _

/-- **The event bound of the parallel hardwired runtime.** Let `S` be a union of cell events
`Sc c` (each depending on its cell `c` of `h`, on `k`, `k'` and on the hardwired register), with
upward closed slices, without the start, and with fresh bound `ε` below `q + K + 1` entries for
`S` and for every `Sc c`. A program of rounds of `h` and single calls, with at most `q` sponge
calls in total, `d` rounds and single sponge calls, and `K` classical calls, ends with
`√w ≤ √(6 ε d q) + √(∑ d)`, where `∑ d` sums the costs of the classical calls along the run. -/
theorem rpow_inv_two_eventWeight_spongeHardwiredRuntime_par_le (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (Sc : Z → Set (HwReg X Z M)) [∀ c, DecidablePred (· ∈ Sc c)]
    (hsub : ∀ c, Sc c ⊆ S) (hunion : ∀ s ∈ S, ∃ c, s ∈ Sc c)
    (hloc : ∀ c (s s' : HwReg X Z M), s'.1.1 c = s.1.1 c → s'.1.2 = s.1.2 → s'.2 = s.2 →
      (s' ∈ Sc c ↔ s ∈ Sc c))
    (hupc : ∀ c W m, UpClosed (slice (Sc c) W m)) (hup : ∀ W m, UpClosed (slice S W m))
    (W₀ : Hw X Z) (m₀ : M)
    (hempty : ((Database.empty, Database.empty, Database.empty), W₀, m₀) ∉ S) {q d K : ℕ}
    {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤) (hεc : ∀ c W m, FreshBound (slice (Sc c) W m) (q + K + 1) ε)
    (hε : ∀ W m, FreshBound (slice S W m) (q + K + 1) ε)
    (dR : HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (hdR : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector S)
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ potential (hwProjector S) σ + dR c σ)
    (hdP : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector S)
      (MatrixMap.conj (hwProgKraus c r) σ) ≤ potential (hwProjector S) σ + dP c σ)
    (I : L.Interp) (x : QuantumComp L (parSpec (hwSpec X Z M) (hPort X Z M)) Xr A)
    (hxq : IFreeM.IsChargeBound x (portCharge (spongeWidth (hPort X Z M) hwCls)) q)
    (hxd : IFreeM.IsChargeBound x (portCharge (spongeRounds (hPort X Z M) hwCls)) d)
    (hxK : IFreeM.IsChargeBound x (portCharge (clsCount (hPort X Z M) hwCls)) K)
    (ρ : SubState A) :
    ((spongeHardwiredRuntime X Z W₀ m₀).par (hPort X Z M)).eventWeight I (hwProjector S) x
        (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix) ^ (2⁻¹ : ℝ) ≤
      (6 * ε * d * q) ^ (2⁻¹ : ℝ) +
        ((spongeHardwiredRuntime X Z W₀ m₀).par (hPort X Z M)).totalWeight I
          (parWeight (hPort X Z M) (hwCost dR dP)) x
          (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix) ^ (2⁻¹ : ℝ) := by
  have hρ0 : (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix).PosSemidef :=
    (ρ.prod (spongeHardwiredRuntime X Z W₀ m₀).init).posSemidef
  have htr : ENNReal.ofReal
      (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix).trace.re ≤ 1 := by
    rw [← SubState.matrix_prod]
    exact ENNReal.ofReal_le_one.mpr (ρ.prod (spongeHardwiredRuntime X Z W₀ m₀).init).trace_re_le_one
  have h := rpow_inv_two_tsum_potential_run_le_rounds
    ((spongeHardwiredRuntime X Z W₀ m₀).par (hPort X Z M)) I (hwProjector S)
    (parCls (hPort X Z M) hwCls) (fun s : HwReg X Z M ↦ dbGrade s.1)
    (spongeWidth (hPort X Z M) hwCls) (spongeRounds (hPort X Z M) hwCls) (fun _ ↦ 0)
    (fun i ↦ spongeWidth (hPort X Z M) hwCls i + clsCount (hPort X Z M) hwCls i) ?_ (6 * ε) 0
    (q + K) (fun i _ ↦ spongeWidth_eq_zero_or i) ?_ (parWeight (hPort X Z M) (hwCost dR dP)) ?_ x
    q d 0 (q + K) 0 hxq hxd (isChargeBound_zero_portCharge x)
    (isChargeBound_portCharge_add _ _ x hxq hxK) (by omega) hρ0 (querySupportedOn_start W₀ m₀ ρ)
  · exact (le_of_eq (congrArg (· ^ (2⁻¹ : ℝ)) (eventWeight_eq_tsum_potential
      ((spongeHardwiredRuntime X Z W₀ m₀).par (hPort X Z M)) I (hwProjector S) x
      (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix)))).trans
      (rpow_inv_two_rounds_finish (potential_start_eq_zero S W₀ m₀ hempty ρ) htr h)
  · -- Grades: a single call raises the grade by one, a round by its width.
    intro i r t σ hσ
    rcases i with i | ⟨w, f⟩
    · have he := spongeWidth_add_clsCount_inl (port := hPort X Z M) (cls := hwCls) i
      exact (querySupportedOn_spongeHardwiredRuntime_step W₀ m₀ i r t σ hσ).mono
        (Set.Iic_subset_Iic.mpr (by omega))
    · have hb := LinearMap.congr_fun (par_step_round_branch W₀ m₀ w f r) σ
      refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
      have hw := spongeWidth_round (port := hPort X Z M) (cls := hwCls) (fun _ ↦ rfl) w f
      have hc := clsCount_round (port := hPort X Z M) (cls := hwCls) (fun _ ↦ rfl) w f
      exact QuerySupportedOn.conj hσ fun y' y hK hy ↦ by
        have := dbGrade_le_of_hRound_ne_zero W₀ m₀ y y' hK
        simp only [Set.mem_Iic] at hy ⊢
        omega
  · -- Quantum calls: single sponge calls and rounds of `h`.
    intro i hi σ hσ hσg
    rcases i with ((p | c) | c) | ⟨w, f⟩
    · have hs : ∑' r : Unit, potential (hwProjector S)
          (((spongeHardwiredRuntime X Z W₀ m₀).step (.inl (.inl p))).branch r σ) =
          potential (hwProjector S) (MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U p) σ) := by
        rw [tsum_fintype, Fintype.sum_unique, spongeHardwiredRuntime_step_sponge]
        rfl
      have h1 : (spongeWidth (hPort X Z M) hwCls (.inl (.inl (.inl p))) : ℝ≥0∞) = 1 := by
        simp [spongeWidth, widthCharge, hwCls]
      refine (congrArg (· ^ (2⁻¹ : ℝ)) hs).trans_le
        ((rpow_inv_two_potential_spongeHardwired_le S hup hεtop hε W₀ m₀ p hσ hσg).trans ?_)
      rw [h1, mul_one, Nat.cast_zero, zero_mul, add_zero]
      exact le_rfl
    · exact absurd hi (by simp [parCls, hwCls])
    · exact absurd hi (by simp [parCls, hwCls])
    · have hs : ∑' r : Fin w → Unit, potential (hwProjector S)
          ((((spongeHardwiredRuntime X Z W₀ m₀).par (hPort X Z M)).step
            (.inr (.round w f))).branch r σ) =
          potential (hwProjector S) (MatrixMap.conj (hRound (X := X) (Z := Z) (M := M) w) σ) := by
        rw [tsum_fintype, Fintype.sum_unique]
        exact congrArg _ (LinearMap.congr_fun (par_step_round_branch W₀ m₀ w f _) σ)
      refine (congrArg (· ^ (2⁻¹ : ℝ)) hs).trans_le
        ((rpow_inv_two_potential_hRound_le S Sc hsub hunion hloc hupc hεtop hεc W₀ m₀ w hσ
          hσg).trans ?_)
      rw [spongeWidth_round (port := hPort X Z M) (cls := hwCls) (fun _ ↦ rfl), Nat.cast_zero,
        zero_mul, add_zero]
      exact le_rfl
  · -- Classical calls: the read and program ports.
    intro i hi σ hσ
    rcases i with ((p | c) | c) | ⟨w, f⟩
    · exact absurd hi (by simp [parCls, hwCls])
    · have hs : ∑' r : c.Result, potential (hwProjector S)
          (((spongeHardwiredRuntime X Z W₀ m₀).step (.inl (.inr c))).branch r σ) =
          ∑' r : c.Result, potential (hwProjector S) (MatrixMap.conj (hwReadKraus c r) σ) :=
        tsum_congr fun r ↦ by rw [spongeHardwiredRuntime_step_read]; rfl
      exact hs.trans_le (hdR c σ hσ)
    · have hs : ∑' r : c.Result, potential (hwProjector S)
          (((spongeHardwiredRuntime X Z W₀ m₀).step (.inr c)).branch r σ) =
          ∑' r : c.Result, potential (hwProjector S) (MatrixMap.conj (hwProgKraus c r) σ) :=
        tsum_congr fun r ↦ by rw [spongeHardwiredRuntime_step_prog]; rfl
      exact hs.trans_le (hdP c σ hσ)
    · exact absurd hi (by simp [parCls])

/-- **The event bound of the parallel hardwired runtime**, squared:
`w ≤ (√(6 ε d q) + √(∑ d))²`. -/
theorem eventWeight_spongeHardwiredRuntime_par_le (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (Sc : Z → Set (HwReg X Z M)) [∀ c, DecidablePred (· ∈ Sc c)]
    (hsub : ∀ c, Sc c ⊆ S) (hunion : ∀ s ∈ S, ∃ c, s ∈ Sc c)
    (hloc : ∀ c (s s' : HwReg X Z M), s'.1.1 c = s.1.1 c → s'.1.2 = s.1.2 → s'.2 = s.2 →
      (s' ∈ Sc c ↔ s ∈ Sc c))
    (hupc : ∀ c W m, UpClosed (slice (Sc c) W m)) (hup : ∀ W m, UpClosed (slice S W m))
    (W₀ : Hw X Z) (m₀ : M)
    (hempty : ((Database.empty, Database.empty, Database.empty), W₀, m₀) ∉ S) {q d K : ℕ}
    {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤) (hεc : ∀ c W m, FreshBound (slice (Sc c) W m) (q + K + 1) ε)
    (hε : ∀ W m, FreshBound (slice S W m) (q + K + 1) ε)
    (dR : HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (hdR : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector S)
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ potential (hwProjector S) σ + dR c σ)
    (hdP : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector S)
      (MatrixMap.conj (hwProgKraus c r) σ) ≤ potential (hwProjector S) σ + dP c σ)
    (I : L.Interp) (x : QuantumComp L (parSpec (hwSpec X Z M) (hPort X Z M)) Xr A)
    (hxq : IFreeM.IsChargeBound x (portCharge (spongeWidth (hPort X Z M) hwCls)) q)
    (hxd : IFreeM.IsChargeBound x (portCharge (spongeRounds (hPort X Z M) hwCls)) d)
    (hxK : IFreeM.IsChargeBound x (portCharge (clsCount (hPort X Z M) hwCls)) K)
    (ρ : SubState A) :
    ((spongeHardwiredRuntime X Z W₀ m₀).par (hPort X Z M)).eventWeight I (hwProjector S) x
        (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix) ≤
      ((6 * ε * d * q) ^ (2⁻¹ : ℝ) +
        ((spongeHardwiredRuntime X Z W₀ m₀).par (hPort X Z M)).totalWeight I
          (parWeight (hPort X Z M) (hwCost dR dP)) x
          (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := ENNReal.rpow_le_rpow (rpow_inv_two_eventWeight_spongeHardwiredRuntime_par_le S Sc
    hsub hunion hloc hupc hup W₀ m₀ hempty hεtop hεc hε dR dP hdR hdP I x hxq hxd hxK ρ)
    (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

/-! ## The parallel hardwired runtime extended by classical ports -/

section ext

open Quantum.SubInstrument in
private theorem branch_relabel_bind_pure_of_ne' {S' T : Type*} [Fintype S'] [Fintype T]
    [DecidableEq S'] [DecidableEq T] {α : Type*} (e : S' ≃ T) {a b : α} (h : a ≠ b) :
    ((relabel e).bind fun _ ↦ SubInstrument.pure b).branch a = 0 := by
  rw [DSubInstrument.branch_bind_unit, SubInstrument.branch_pure_of_ne h, LinearMap.zero_comp]

open Quantum.SubInstrument in
/-- **A round of Kraus steps is a Kraus map**, with Kraus operators needed only at the ports of
the round. -/
theorem branch_roundStep_of_conj_on {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec)
    (K : ∀ p, spec.Result p → Matrix (spec.Out p × R.D) (spec.In p × R.D) ℂ) :
    ∀ {w : ℕ} (f : Fin w → spec.Port),
      (∀ i r, (R.step (f i)).branch r = MatrixMap.conj (K (f i) r)) →
      ∀ rs : RoundResult spec f, (R.roundStep f).branch rs = MatrixMap.conj (R.roundKraus K f rs)
  | 0, f, _, rs => by
    obtain rfl : rs = finZeroElim := funext fun i ↦ i.elim0
    rw [roundStep_zero, SubInstrument.map_eq_bind_pure, DSubInstrument.branch_bind_unit,
      SubInstrument.branch_pure_self, LinearMap.id_comp, branch_relabel]
    rfl
  | w + 1, f, hK, rs => by
    have hz : ∀ r rs', (r ≠ rs 0 ∨ rs' ≠ Fin.tail rs) →
        ((relabel (R.roundJoin f)).bind fun _ ↦
          SubInstrument.pure (Fin.cons (α := fun i ↦ spec.Result (f i)) r rs')).branch rs = 0 := by
      intro r rs' h
      refine branch_relabel_bind_pure_of_ne' _ fun he ↦ ?_
      rcases h with h | h
      · exact h ((Fin.cons_zero _ _).symm.trans (congrFun he 0).symm)
      · exact h ((Fin.tail_cons _ _).symm.trans (congrArg Fin.tail he).symm)
    refine LinearMap.ext fun ρ ↦ ?_
    rw [roundStep_succ, DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
      DSubInstrument.branch_bind_apply, tsum_eq_single (rs 0) fun r hr ↦ ?_]
    · rw [DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
        DSubInstrument.branch_bind_apply, tsum_eq_single (Fin.tail rs) fun rs' h ↦ ?_]
      · rw [Fin.cons_self_tail, DSubInstrument.branch_bind_unit, SubInstrument.branch_pure_self,
          LinearMap.id_comp, DSubInstrument.branch_frame_apply, DSubInstrument.branch_frame_apply,
          hK 0 (rs 0), branch_roundStep_of_conj_on R K (fun i ↦ f i.succ)
            (fun i r ↦ hK i.succ r), MatrixMap.amplify_conj, MatrixMap.amplify_conj,
          branch_relabel, branch_relabel, branch_relabel, roundKraus]
        simp only [MatrixMap.conj_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      · rw [hz _ _ (.inr h), LinearMap.zero_apply]
    · simp only [DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
        DSubInstrument.branch_bind_apply, fun rs' ↦ hz r rs' (.inl hr), LinearMap.zero_apply,
        tsum_zero]

variable {t : QuantumOracleSpec.{0, 0}}

variable (X Z M t) in
/-- The rounds of the extended runtime are rounds of port `h`. -/
abbrev ePort : Unit → ((hwSpec X Z M).sum t).Port := fun _ ↦ .inl (.inl (.inl .h))

variable (X Z M t) in
/-- The classical ports of the extended signature: those of `hwSpec` and the added ones. -/
def hwExtCls : ((hwSpec X Z M).sum t).Port → Bool
  | .inl i => hwCls i
  | .inr _ => true

/-- The classical costs on the ports of the extended runtime. -/
def hwExtCost {D : Type} [Fintype D]
    (dR : HwRead X Z M → Matrix (Unit × D) (Unit × D) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × D) (Unit × D) ℂ → ℝ≥0∞)
    (dT : ∀ j : t.Port, Matrix (t.In j × D) (t.In j × D) ℂ → ℝ≥0∞) :
    ∀ i, Matrix (((hwSpec X Z M).sum t).In i × D) (((hwSpec X Z M).sum t).In i × D) ℂ → ℝ≥0∞
  | .inl i => hwCost dR dP i
  | .inr j => dT j

variable (X Z) in
/-- Kraus operators of the hardwired ports of the extended runtime (`0` on the added ports). -/
noncomputable def hwExtKraus (W₀ : Hw X Z) (m₀ : M) :
    ∀ i : ((hwSpec X Z M).sum t).Port, ((hwSpec X Z M).sum t).Result i →
      Matrix (((hwSpec X Z M).sum t).Out i × HwReg X Z M)
        (((hwSpec X Z M).sum t).In i × HwReg X Z M) ℂ
  | .inl i, r => hwKraus X Z W₀ m₀ i r
  | .inr _, _ => 0

/-- A round of one sponge port of the extended runtime is the product of its calls on the
slots. -/
theorem roundKraus_extend (W₀ : Hw X Z) (m₀ : M)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j)) (p : SpongePort) :
    ∀ {w : ℕ} (rs : RoundResult ((hwSpec X Z M).sum t)
      (fun _ : Fin w ↦ (.inl (.inl (.inl p)) : ((hwSpec X Z M).sum t).Port))),
      ((spongeHardwiredRuntime X Z W₀ m₀).extend step').roundKraus (hwExtKraus X Z W₀ m₀)
          (fun _ : Fin w ↦ (.inl (.inl (.inl p)) : ((hwSpec X Z M).sum t).Port)) rs =
        roundProd (fun j : Fin w ↦
          slotLift (S := spongeIn X Z p) (N := HwReg X Z M) j ((spongeHardwired X Z W₀ m₀).U p))
  | 0, rs => by
      simp only [QuantumRuntime.roundKraus]
      rw [roundProd_zero]
      refine (congrArg basisMatrix (funext fun y ↦ ?_)).trans basisMatrix_id
      exact Prod.ext (funext fun i ↦ i.elim0) rfl
  | w + 1, rs => by
      simp only [QuantumRuntime.roundKraus]
      rw [roundKraus_extend W₀ m₀ step' p (Fin.tail rs)]
      exact roundProd_succ_slotLift _

/-- The step of a round of the extended parallel runtime. -/
theorem par_extend_step_round_branch (W₀ : Hw X Z) (m₀ : M)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j)) (w : ℕ) (f : Fin w → Unit)
    (rs : RoundResult ((hwSpec X Z M).sum t) fun i ↦ ePort X Z M t (f i)) :
    ((((spongeHardwiredRuntime X Z W₀ m₀).extend step').par (ePort X Z M t)).step
        (.inr (.round w f))).branch rs =
      MatrixMap.conj (hRound (X := X) (Z := Z) (M := M) w) := by
  have h := branch_roundStep_of_conj_on ((spongeHardwiredRuntime X Z W₀ m₀).extend step')
    (hwExtKraus X Z W₀ m₀)
    (fun _ : Fin w ↦ (.inl (.inl (.inl .h)) : ((hwSpec X Z M).sum t).Port))
    (fun _ r ↦ spongeHardwiredRuntime_step_branch W₀ m₀ (.inl (.inl .h)) r) rs
  rw [roundKraus_extend] at h
  exact h

/-- **The event bound of the parallel hardwired runtime extended by classical ports.** As
`rpow_inv_two_eventWeight_spongeHardwiredRuntime_par_le`, for the hardwired runtime (written with
its initial state `σ₀` and steps `s₀`) extended by ports `t`, which are classical calls raising
the grade by at most one (`hgT`) at costs `dT` (`hdT`); `K` counts them with the read and
program calls. -/
theorem rpow_inv_two_eventWeight_extend_par_le (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (Sc : Z → Set (HwReg X Z M)) [∀ c, DecidablePred (· ∈ Sc c)]
    (hsub : ∀ c, Sc c ⊆ S) (hunion : ∀ s ∈ S, ∃ c, s ∈ Sc c)
    (hloc : ∀ c (s s' : HwReg X Z M), s'.1.1 c = s.1.1 c → s'.1.2 = s.1.2 → s'.2 = s.2 →
      (s' ∈ Sc c ↔ s ∈ Sc c))
    (hupc : ∀ c W m, UpClosed (slice (Sc c) W m)) (hup : ∀ W m, UpClosed (slice S W m))
    (W₀ : Hw X Z) (m₀ : M)
    (hempty : ((Database.empty, Database.empty, Database.empty), W₀, m₀) ∉ S) {q d K : ℕ}
    {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤) (hεc : ∀ c W m, FreshBound (slice (Sc c) W m) (q + K + 1) ε)
    (hε : ∀ W m, FreshBound (slice S W m) (q + K + 1) ε)
    (dR : HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (hdR : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector S)
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ potential (hwProjector S) σ + dR c σ)
    (hdP : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector S)
      (MatrixMap.conj (hwProgKraus c r) σ) ≤ potential (hwProjector S) σ + dP c σ)
    (σ₀ : SubState (QReg.of (HwReg X Z M)))
    (s₀ : ∀ i, SubInstrument ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).Out i × QReg.of (HwReg X Z M)) ((hwSpec X Z M).Result i))
    (hσ₀ : σ₀ = (spongeHardwiredRuntime X Z W₀ m₀).init)
    (hs₀ : s₀ = (spongeHardwiredRuntime X Z W₀ m₀).step)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    (dT : ∀ j : t.Port,
      Matrix (t.In j × QReg.of (HwReg X Z M)) (t.In j × QReg.of (HwReg X Z M)) ℂ → ℝ≥0∞)
    (hgT : ∀ j r n (σ : Matrix (t.In j × QReg.of (HwReg X Z M))
        (t.In j × QReg.of (HwReg X Z M)) ℂ),
      QuerySupportedOn (fun q : t.In j × QReg.of (HwReg X Z M) ↦ dbGrade q.2.1) (Set.Iic n) σ →
      QuerySupportedOn (fun q : t.Out j × QReg.of (HwReg X Z M) ↦ dbGrade q.2.1)
        (Set.Iic (n + 1)) ((step' j).branch r σ))
    (hdT : ∀ j σ, σ.PosSemidef → ∑' r, potential (hwProjector S) ((step' j).branch r σ) ≤
      potential (hwProjector S) σ + dT j σ)
    (I : L.Interp) (x : QuantumComp L (parSpec ((hwSpec X Z M).sum t) (ePort X Z M t)) Xr A)
    (hxq : IFreeM.IsChargeBound x (portCharge (spongeWidth (ePort X Z M t) (hwExtCls X Z M t))) q)
    (hxd : IFreeM.IsChargeBound x
      (portCharge (spongeRounds (ePort X Z M t) (hwExtCls X Z M t))) d)
    (hxK : IFreeM.IsChargeBound x (portCharge (clsCount (ePort X Z M t) (hwExtCls X Z M t))) K)
    (ρ : SubState A) :
    (((QuantumRuntime.mk _ σ₀ s₀).extend step').par (ePort X Z M t)).eventWeight I
        (hwProjector S) x (ρ.matrix ⊗ₖ σ₀.matrix) ^ (2⁻¹ : ℝ) ≤
      (6 * ε * d * q) ^ (2⁻¹ : ℝ) +
        (((QuantumRuntime.mk _ σ₀ s₀).extend step').par (ePort X Z M t)).totalWeight I
          (parWeight (ePort X Z M t) (hwExtCost dR dP dT)) x
          (ρ.matrix ⊗ₖ σ₀.matrix) ^ (2⁻¹ : ℝ) := by
  subst hσ₀ hs₀
  have hρ0 : (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix).PosSemidef :=
    (ρ.prod (spongeHardwiredRuntime X Z W₀ m₀).init).posSemidef
  have htr : ENNReal.ofReal
      (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix).trace.re ≤ 1 := by
    rw [← SubState.matrix_prod]
    exact ENNReal.ofReal_le_one.mpr (ρ.prod (spongeHardwiredRuntime X Z W₀ m₀).init).trace_re_le_one
  have h := rpow_inv_two_tsum_potential_run_le_rounds
    (((spongeHardwiredRuntime X Z W₀ m₀).extend step').par (ePort X Z M t)) I (hwProjector S)
    (parCls (ePort X Z M t) (hwExtCls X Z M t)) (fun s : HwReg X Z M ↦ dbGrade s.1)
    (spongeWidth (ePort X Z M t) (hwExtCls X Z M t))
    (spongeRounds (ePort X Z M t) (hwExtCls X Z M t)) (fun _ ↦ 0)
    (fun i ↦ spongeWidth (ePort X Z M t) (hwExtCls X Z M t) i +
      clsCount (ePort X Z M t) (hwExtCls X Z M t) i) ?_ (6 * ε) 0
    (q + K) (fun i _ ↦ spongeWidth_eq_zero_or i) ?_
    (parWeight (ePort X Z M t) (hwExtCost dR dP dT)) ?_ x
    q d 0 (q + K) 0 hxq hxd (isChargeBound_zero_portCharge x)
    (isChargeBound_portCharge_add _ _ x hxq hxK) (by omega) hρ0 (querySupportedOn_start W₀ m₀ ρ)
  · exact (le_of_eq (congrArg (· ^ (2⁻¹ : ℝ)) (eventWeight_eq_tsum_potential
      (((spongeHardwiredRuntime X Z W₀ m₀).extend step').par (ePort X Z M t)) I (hwProjector S) x
      (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix)))).trans
      (rpow_inv_two_rounds_finish (potential_start_eq_zero S W₀ m₀ hempty ρ) htr h)
  · -- Grades: a single call raises the grade by one, a round by its width.
    intro i r n σ hσ
    rcases i with i | ⟨w, f⟩
    · have he := spongeWidth_add_clsCount_inl (port := ePort X Z M t) (cls := hwExtCls X Z M t) i
      rcases i with i | j
      · exact (querySupportedOn_spongeHardwiredRuntime_step W₀ m₀ i r n σ hσ).mono
          (Set.Iic_subset_Iic.mpr (by omega))
      · exact (hgT j r n σ hσ).mono (Set.Iic_subset_Iic.mpr (by omega))
    · have hb := LinearMap.congr_fun (par_extend_step_round_branch W₀ m₀ step' w f r) σ
      refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
      have hw := spongeWidth_round (port := ePort X Z M t) (cls := hwExtCls X Z M t)
        (fun _ ↦ rfl) w f
      have hc := clsCount_round (port := ePort X Z M t) (cls := hwExtCls X Z M t)
        (fun _ ↦ rfl) w f
      exact QuerySupportedOn.conj hσ fun y' y hK hy ↦ by
        have := dbGrade_le_of_hRound_ne_zero W₀ m₀ y y' hK
        simp only [Set.mem_Iic] at hy ⊢
        omega
  · -- Quantum calls: single sponge calls and rounds of `h`.
    intro i hi σ hσ hσg
    rcases i with (((p | c) | c) | j) | ⟨w, f⟩
    · have hs : ∑' r : Unit, potential (hwProjector S)
          (((spongeHardwiredRuntime X Z W₀ m₀).step (.inl (.inl p))).branch r σ) =
          potential (hwProjector S) (MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U p) σ) := by
        rw [tsum_fintype, Fintype.sum_unique, spongeHardwiredRuntime_step_sponge]
        rfl
      have h1 : (spongeWidth (ePort X Z M t) (hwExtCls X Z M t) (.inl (.inl (.inl (.inl p)))) :
          ℝ≥0∞) = 1 := by
        simp [spongeWidth, widthCharge, hwExtCls, hwCls]
      refine (congrArg (· ^ (2⁻¹ : ℝ)) hs).trans_le
        ((rpow_inv_two_potential_spongeHardwired_le S hup hεtop hε W₀ m₀ p hσ hσg).trans ?_)
      rw [h1, mul_one, Nat.cast_zero, zero_mul, add_zero]
      exact le_rfl
    · exact absurd hi (by simp [parCls, hwExtCls, hwCls])
    · exact absurd hi (by simp [parCls, hwExtCls, hwCls])
    · exact absurd hi (by simp [parCls, hwExtCls])
    · have hs : ∑' r : Fin w → Unit, potential (hwProjector S)
          (((((spongeHardwiredRuntime X Z W₀ m₀).extend step').par (ePort X Z M t)).step
            (.inr (.round w f))).branch r σ) =
          potential (hwProjector S) (MatrixMap.conj (hRound (X := X) (Z := Z) (M := M) w) σ) := by
        rw [tsum_fintype, Fintype.sum_unique]
        exact congrArg _ (LinearMap.congr_fun (par_extend_step_round_branch W₀ m₀ step' w f _) σ)
      refine (congrArg (· ^ (2⁻¹ : ℝ)) hs).trans_le
        ((rpow_inv_two_potential_hRound_le S Sc hsub hunion hloc hupc hεtop hεc W₀ m₀ w hσ
          hσg).trans ?_)
      rw [spongeWidth_round (port := ePort X Z M t) (cls := hwExtCls X Z M t) (fun _ ↦ rfl),
        Nat.cast_zero, zero_mul, add_zero]
      exact le_rfl
  · -- Classical calls: the read, program and added ports.
    intro i hi σ hσ
    rcases i with (((p | c) | c) | j) | ⟨w, f⟩
    · exact absurd hi (by simp [parCls, hwExtCls, hwCls])
    · have hs : ∑' r : c.Result, potential (hwProjector S)
          (((spongeHardwiredRuntime X Z W₀ m₀).step (.inl (.inr c))).branch r σ) =
          ∑' r : c.Result, potential (hwProjector S) (MatrixMap.conj (hwReadKraus c r) σ) :=
        tsum_congr fun r ↦ by rw [spongeHardwiredRuntime_step_read]; rfl
      exact hs.trans_le (hdR c σ hσ)
    · have hs : ∑' r : c.Result, potential (hwProjector S)
          (((spongeHardwiredRuntime X Z W₀ m₀).step (.inr c)).branch r σ) =
          ∑' r : c.Result, potential (hwProjector S) (MatrixMap.conj (hwProgKraus c r) σ) :=
        tsum_congr fun r ↦ by rw [spongeHardwiredRuntime_step_prog]; rfl
      exact hs.trans_le (hdP c σ hσ)
    · exact hdT j σ hσ
    · exact absurd hi (by simp [parCls])

end ext

end par

end Quantum.Par

end
