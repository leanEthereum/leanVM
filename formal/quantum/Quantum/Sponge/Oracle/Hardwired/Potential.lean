module

public import Quantum.Sponge.Oracle.Hardwired.Event

@[expose] public section

/-!
# Diagonal potentials on the hardwired register

A *diagonal potential* is a function `φ ≥ 0` of the basis states `(D, W, m)` of the hardwired
register, read as the operator `Φ = diag φ`. If changing one database cell raises `φ` by at most
one (`OneCellLipschitz`), every sponge port satisfies `Uᴴ (1 ⊗ Φ) U ≤ 1 ⊗ Φ + 1`
(`posSemidef_diagonalPotential_drop`): the port acts on the queried cell only, `Φ` lies between
`Ψ` and `Ψ + 1` for the minimum `Ψ` of `φ` over the contents of that cell, and `U` commutes
with `Ψ`.

Summed along a run (`diagonalPotential_drop`): if every classical port lowers the expected
potential by at least its drop weight, the drops of all classical calls add up to at most the
initial potential plus the number `q` of sponge calls. This is the potential of design §4 for the
selected grinding reads, `Φ = ∑_{(l,e) not yet selected} n_{l,e}(D)`.
-/

open IPFunctor Matrix
open scoped Kronecker ENNReal ComplexOrder

universe u v u₁ v₁ w

namespace Quantum.Sponge

open Quantum QuantumRuntime

/-! ## Sponge calls are weighted by their number -/

section count

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {X : QReg → Type w} (cls : spec.Port → Bool)

/-- The trace on the calls of the ports outside `cls`. -/
noncomputable def clsTrace : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞ :=
  fun i σ ↦ if cls i then 0 else ENNReal.ofReal σ.trace.re

/-- **Counting the calls outside `cls`.** A program making at most `q` calls of ports outside
`cls` has total trace at most `q tr ρ` on those calls. -/
theorem totalWeight_clsTrace_le {A : QReg} (x : QuantumComp L spec X A) (q : ℕ)
    (hx : IFreeM.IsChargeBound x (portCharge fun i ↦ if cls i then 0 else 1) q)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I (clsTrace R cls) x ρ ≤ q * ENNReal.ofReal ρ.trace.re := by
  classical
  induction x using QuantumComp.inductionOn generalizing q with
  | pure _ _ =>
    simp [totalWeight]
  | primBind B o k ih =>
    rw [isChargeBound_portCharge_primBind_iff] at hx
    rw [totalWeight_primBind]
    calc ∑' b, R.totalWeight I (clsTrace R cls) (k b) (((I o).frame R.D).branch b ρ)
        ≤ ∑' b, q * ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re :=
          ENNReal.tsum_le_tsum fun b ↦ ih b q (hx b)
            (((I o).frame R.D).posSemidef_branch_apply b hρ)
      _ ≤ q * ENNReal.ofReal ρ.trace.re := by
          rw [ENNReal.tsum_mul_left]
          gcongr
          exact ((I o).frame R.D).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
  | queryBind B i E ℓ k ih =>
    rw [isChargeBound_portCharge_queryBind_iff] at hx
    rw [totalWeight_queryBind]
    have htr : ∑' r, ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re ≤
        ENNReal.ofReal ρ.trace.re := (R.queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
    have hk : ∀ q', (∀ r, IFreeM.IsChargeBound (k r)
        (portCharge fun i ↦ if cls i then 0 else 1) q') →
        ∑' r, R.totalWeight I (clsTrace R cls) (k r) ((R.queryStep i E ℓ).branch r ρ) ≤
          q' * ENNReal.ofReal ρ.trace.re := fun q' hq' ↦
      (ENNReal.tsum_le_tsum fun r ↦ ih r q' (hq' r)
        ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ)).trans
        (by rw [ENNReal.tsum_mul_left]; gcongr)
    cases hci : cls i
    · simp only [hci, Bool.false_eq_true, ↓reduceIte] at hx
      have h1 : clsTrace R cls i (callInput ℓ R.D ρ) = ENNReal.ofReal ρ.trace.re := by
        simp [clsTrace, hci, trace_callInput]
      rw [h1]
      calc ENNReal.ofReal ρ.trace.re + _ ≤ ENNReal.ofReal ρ.trace.re +
            ((q - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re := by gcongr; exact hk _ hx.2
        _ = q * ENNReal.ofReal ρ.trace.re := by
            rw [← one_add_mul, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_cancel' hx.1]
    · simp only [hci, ↓reduceIte, Nat.sub_zero] at hx
      have h1 : clsTrace R cls i (callInput ℓ R.D ρ) = 0 := by simp [clsTrace, hci]
      rw [h1, zero_add]
      exact hk _ hx.2

end count

/-! ## One-cell Lipschitz potentials -/

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

/-- Changing one database cell raises `φ` by at most one. -/
structure OneCellLipschitz (φ : HwReg X Z M → ℝ) : Prop where
  /-- A cell of `D.h`. -/
  h : ∀ (D : DbReg X Z) b z v, φ ((Function.update D.1 z v, D.2.1, D.2.2), b) ≤ φ (D, b) + 1
  /-- A cell of `D.k`. -/
  k : ∀ (D : DbReg X Z) b x v, φ ((D.1, Function.update D.2.1 x v, D.2.2), b) ≤ φ (D, b) + 1
  /-- A cell of `D.k'`. -/
  k' : ∀ (D : DbReg X Z) b x v, φ ((D.1, D.2.1, Function.update D.2.2 x v), b) ≤ φ (D, b) + 1

/-- The databases with the cell queried by `a` at port `i` emptied. -/
def eraseCell : (i : SpongePort) → spongeIn X Z i → DbReg X Z → DbReg X Z
  | .h, a, D => (Function.update D.1 (a : Z × X).1 none, D.2.1, D.2.2)
  | .k, a, D => (D.1, Function.update D.2.1 (a : X × Z).1 none, D.2.2)
  | .k', a, D => (D.1, D.2.1, Function.update D.2.2 (a : X × Z).1 none)

omit [Fintype M] [DecidableEq M] in
/-- Two databases with the same erasure differ at most in the queried cell. -/
theorem le_add_one_of_eraseCell_eq {φ : HwReg X Z M → ℝ} (hφ : OneCellLipschitz φ)
    (i : SpongePort) (a : spongeIn X Z i) {D D' : DbReg X Z} (b : Hw X Z × M)
    (h : eraseCell i a D' = eraseCell i a D) : φ (D, b) ≤ φ (D', b) + 1 := by
  cases i
  · have hD : D = (Function.update D'.1 (a : Z × X).1 (D.1 (a : Z × X).1), D'.2.1, D'.2.2) := by
      simp only [eraseCell, Prod.mk.injEq] at h
      obtain ⟨h₁, h₂, h₃⟩ := h
      refine Prod.ext (funext fun z ↦ ?_) (Prod.ext h₂.symm h₃.symm)
      by_cases hz : z = (a : Z × X).1
      · subst hz
        simp
      · simpa [Function.update_of_ne hz] using (congrFun h₁ z).symm
    rw [hD]
    exact hφ.h D' b _ _
  · have hD : D = (D'.1, Function.update D'.2.1 (a : X × Z).1 (D.2.1 (a : X × Z).1), D'.2.2) := by
      simp only [eraseCell, Prod.mk.injEq] at h
      obtain ⟨h₁, h₂, h₃⟩ := h
      refine Prod.ext h₁.symm (Prod.ext (funext fun x ↦ ?_) h₃.symm)
      by_cases hx : x = (a : X × Z).1
      · subst hx
        simp
      · simpa [Function.update_of_ne hx] using (congrFun h₂ x).symm
    rw [hD]
    exact hφ.k D' b _ _
  · have hD : D = (D'.1, D'.2.1, Function.update D'.2.2 (a : X × Z).1 (D.2.2 (a : X × Z).1)) := by
      simp only [eraseCell, Prod.mk.injEq] at h
      obtain ⟨h₁, h₂, h₃⟩ := h
      refine Prod.ext h₁.symm (Prod.ext h₂.symm (funext fun x ↦ ?_))
      by_cases hx : x = (a : X × Z).1
      · subst hx
        simp
      · simpa [Function.update_of_ne hx] using (congrFun h₃ x).symm
    rw [hD]
    exact hφ.k' D' b _ _

/-- The minimum of `φ` over the contents of the cell queried by `a` at port `i`. -/
noncomputable def cellMin (φ : HwReg X Z M → ℝ) (i : SpongePort) (a : spongeIn X Z i)
    (s : HwReg X Z M) : ℝ :=
  (Finset.univ.filter fun D : DbReg X Z ↦ eraseCell i a D = eraseCell i a s.1).inf'
    ⟨s.1, by simp⟩ fun D ↦ φ (D, s.2)

omit [Fintype M] [DecidableEq M] in
theorem cellMin_le (φ : HwReg X Z M → ℝ) (i : SpongePort) (a : spongeIn X Z i)
    (s : HwReg X Z M) : cellMin φ i a s ≤ φ s :=
  Finset.inf'_le _ (by simp)

omit [Fintype M] [DecidableEq M] in
theorem le_cellMin_add_one {φ : HwReg X Z M → ℝ} (hφ : OneCellLipschitz φ) (i : SpongePort)
    (a : spongeIn X Z i) (s : HwReg X Z M) : φ s ≤ cellMin φ i a s + 1 := by
  obtain ⟨D, hD, he⟩ := Finset.exists_mem_eq_inf'
    (s := Finset.univ.filter fun D : DbReg X Z ↦ eraseCell i a D = eraseCell i a s.1)
    ⟨s.1, by simp⟩ fun D ↦ φ (D, s.2)
  rw [cellMin, he]
  exact le_add_one_of_eraseCell_eq hφ i a s.2 (Finset.mem_filter.mp hD).2

omit [Fintype M] [DecidableEq M] in
/-- `cellMin` depends only on the classical data, the erased databases and the queried cell. -/
theorem cellMin_congr (φ : HwReg X Z M → ℝ) (i : SpongePort) {a a' : spongeIn X Z i}
    {s s' : HwReg X Z M} (ha : eraseCell i a' = eraseCell i a) (hb : s'.2 = s.2)
    (hD : eraseCell i a s'.1 = eraseCell i a s.1) : cellMin φ i a' s' = cellMin φ i a s := by
  simp only [cellMin, ha, hD, hb]

/-! ## Nonzero entries of the sponge ports -/

section entries

variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The compressed oracle keeps the query input. -/
theorem fst_eq_of_compressedOracle_apply_ne_zero {m m' : A × Y} {D D' : Database A Y}
    (h : compressedOracle A Y (m, D) (m', D') ≠ 0) : m.1 = m'.1 := by
  rw [compressedOracle_eq_controlled, controlled_mul_standardOracle_mul_controlled_apply] at h
  obtain ⟨D₁, -, hD₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at hD₁ with hm
  · rw [hm, oracleEquiv_apply]
  · exact absurd rfl hD₁

end entries

variable [AddCommGroup X] [AddCommGroup Z]

omit [Fintype M] [DecidableEq M] in
/-- A nonzero entry of a compressed port keeps the erased databases and the queried cell. -/
theorem eraseCell_of_spongeCompressed_U_ne_zero (i : SpongePort) (a a' : spongeIn X Z i)
    (D D' : DbReg X Z) (h : (spongeCompressed X Z).U i (a', D') (a, D) ≠ 0) :
    eraseCell i a' = eraseCell i a ∧ eraseCell i a D' = eraseCell i a D := by
  obtain ⟨dh, dk, dk'⟩ := D
  obtain ⟨dh₂, dk₂, dk₂'⟩ := D'
  cases i
  · change onFactor (splitH (Z × X)) (compressedOracle Z X) (a', (dh₂, dk₂, dk₂'))
      (a, (dh, dk, dk')) ≠ 0 at h
    rw [onFactor_apply] at h
    split_ifs at h with hr
    swap
    · exact absurd rfl h
    have hs := eq_update_of_compressedOracle_apply_ne_zero h
    have hx := fst_eq_of_compressedOracle_apply_ne_zero h
    simp only [splitH, Equiv.prodAssoc_symm_apply, Prod.mk.injEq] at hr hs hx
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨funext fun D ↦ by simp [eraseCell, hx], ?_⟩
    simp only [eraseCell, Prod.mk.injEq, and_true]
    rw [hs, Function.update_idem]
  · change onFactor (splitK (X × Z)) (compressedOracle X Z) (a', (dh₂, dk₂, dk₂'))
      (a, (dh, dk, dk')) ≠ 0 at h
    rw [onFactor_apply] at h
    split_ifs at h with hr
    swap
    · exact absurd rfl h
    have hs := eq_update_of_compressedOracle_apply_ne_zero h
    have hx := fst_eq_of_compressedOracle_apply_ne_zero h
    simp only [splitK, Equiv.coe_fn_mk, Prod.mk.injEq] at hr hs hx
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨funext fun D ↦ by simp [eraseCell, hx], ?_⟩
    simp only [eraseCell, Prod.mk.injEq, true_and, and_true]
    rw [hs, Function.update_idem]
  · change onFactor (splitK' (X × Z)) (compressedOracle X Z) (a', (dh₂, dk₂, dk₂'))
      (a, (dh, dk, dk')) ≠ 0 at h
    rw [onFactor_apply] at h
    split_ifs at h with hr
    swap
    · exact absurd rfl h
    have hs := eq_update_of_compressedOracle_apply_ne_zero h
    have hx := fst_eq_of_compressedOracle_apply_ne_zero h
    simp only [splitK', Equiv.coe_fn_mk, Prod.mk.injEq] at hr hs hx
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨funext fun D ↦ by simp [eraseCell, hx], ?_⟩
    simp only [eraseCell, Prod.mk.injEq, true_and]
    rw [hs, Function.update_idem]

omit [Fintype M] [DecidableEq M] in
/-- A nonzero entry of the hardwired shift keeps the query input. -/
theorem eraseCell_of_hwShift_ne_zero (W : Hw X Z) (i : SpongePort) (a a' : spongeIn X Z i)
    (h : hwShift W i a' a ≠ 0) : eraseCell i a' = eraseCell i a := by
  cases i <;>
  · simp only [hwShift, labelProjector, diagonal_mul, oracleUnitary_apply] at h
    have h' := right_ne_zero_of_mul h
    split_ifs at h' with ha
    · funext D
      simp [eraseCell, ha]
    · exact absurd rfl h'

/-- A nonzero entry of a sponge port of the hardwired runtime keeps the classical data, the
erased databases and the queried cell. -/
theorem eraseCell_of_spongeHardwired_U_ne_zero (W₀ : Hw X Z) (m₀ : M) (i : SpongePort)
    (a a' : spongeIn X Z i) (s s' : HwReg X Z M)
    (h : (spongeHardwired X Z W₀ m₀).U i (a', s') (a, s) ≠ 0) :
    s'.2 = s.2 ∧ eraseCell i a' = eraseCell i a ∧ eraseCell i a s'.1 = eraseCell i a s.1 := by
  rw [spongeHardwired_U] at h
  have key := eraseCell_of_spongeCompressed_U_ne_zero i a a' s.1 s'.1
  generalize (spongeCompressed X Z).U i = O at h key
  obtain ⟨D', b'⟩ := s'
  obtain ⟨D, b⟩ := s
  simp only [liftBlocks, submatrix_apply, hwSplit, Equiv.prodAssoc_symm_apply,
    blockDiagonal_apply] at h
  split_ifs at h with hb
  · refine ⟨hb, ?_⟩
    rw [Matrix.add_apply, labelProjector, diagonal_mul, kroneckerMap_apply, Matrix.one_apply] at h
    by_cases hO : O (a', D') (a, D) = 0
    · rw [hO, mul_zero, zero_add] at h
      have h' := right_ne_zero_of_mul h
      split_ifs at h' with hD
      · have hD' : D' = D := hD
        subst hD'
        exact ⟨eraseCell_of_hwShift_ne_zero b'.1 i a a' (left_ne_zero_of_mul h), rfl⟩
      · exact absurd rfl h'
    · exact key hO
  · exact absurd rfl h

/-! ## The operator inequality -/

/-- The diagonal potential `diag φ` of a function of the basis states. -/
noncomputable def diagPot {n : Type*} [DecidableEq n] (φ : n → ℝ) : Matrix n n ℂ :=
  diagonal fun s ↦ (φ s : ℂ)

theorem posSemidef_diagPot {n : Type*} [Fintype n] [DecidableEq n] {φ : n → ℝ}
    (hφ : ∀ s, 0 ≤ φ s) : (diagPot φ).PosSemidef :=
  posSemidef_diagonal_iff.mpr fun s ↦ Complex.zero_le_real.mpr (hφ s)

/-- **A sponge port raises a one-cell Lipschitz diagonal potential by at most one**:
`Uᴴ (1 ⊗ Φ) U ≤ 1 ⊗ Φ + 1`. -/
theorem posSemidef_diagonalPotential_drop {φ : HwReg X Z M → ℝ} (hφ : OneCellLipschitz φ)
    (W₀ : Hw X Z) (m₀ : M) (i : SpongePort) :
    let U := (spongeHardwired X Z W₀ m₀).U i
    ((1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ diagPot φ + 1 -
      Uᴴ * ((1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ diagPot φ) * U).PosSemidef := by
  intro U
  set Φ := (1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ diagPot φ
  set Ψ := diagPot fun q : spongeIn X Z i × HwReg X Z M ↦ cellMin φ i q.1 q.2
  have hΦ : Φ = diagPot fun q : spongeIn X Z i × HwReg X Z M ↦ φ q.2 := by
    simp only [Φ, diagPot, ← diagonal_one, diagonal_kronecker_diagonal, one_mul]
  have hUΨ : U * Ψ = Ψ * U := by
    ext ⟨a', s'⟩ ⟨a, s⟩
    simp only [Ψ, diagPot, mul_diagonal, diagonal_mul]
    by_cases hU : U (a', s') (a, s) = 0
    · simp [hU]
    · obtain ⟨hb, ha, hD⟩ := eraseCell_of_spongeHardwired_U_ne_zero W₀ m₀ i a a' s s' hU
      rw [cellMin_congr φ i ha hb hD, mul_comm]
  have hUU : Uᴴ * U = 1 := (spongeHardwired X Z W₀ m₀).conjTranspose_mul_self i
  have hconj : Uᴴ * (Ψ + 1) * U = Ψ + 1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, Matrix.mul_assoc, ← hUΨ,
      ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have h₁ : (Φ - Ψ).PosSemidef := by
    simp only [hΦ, Ψ, diagPot]
    rw [diagonal_sub]
    exact posSemidef_diagonal_iff.mpr fun q ↦ by
      rw [← Complex.ofReal_sub]
      exact Complex.zero_le_real.mpr (sub_nonneg.mpr (cellMin_le φ i q.1 q.2))
  have h₂ : (Ψ + 1 - Φ).PosSemidef := by
    simp only [hΦ, Ψ, diagPot]
    rw [← diagonal_one, diagonal_add, diagonal_sub]
    exact posSemidef_diagonal_iff.mpr fun q ↦ by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_sub]
      exact Complex.zero_le_real.mpr (sub_nonneg.mpr (le_cellMin_add_one hφ i q.1 q.2))
  have heq : Φ + 1 - Uᴴ * Φ * U = (Φ - Ψ) + Uᴴ * (Ψ + 1 - Φ) * U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hconj]
    abel
  rw [heq]
  exact h₁.add (h₂.conjTranspose_mul_mul_same U)

/-! ## The telescoped drops -/

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **The diagonal potential bounds the classical drops.** Let `φ ≥ 0` be one-cell Lipschitz, with
potential `Φ = diag φ`, and let every read and program port lower the potential by at least its
drop weight: `dR c σ + ∑ᵣ tr (Φ K_r σ K_rᴴ) ≤ tr (Φ σ)`. Then for a program making at most `q`
sponge calls, the drops of all classical calls add up to at most `tr (Φ ρ) + q tr ρ`. -/
theorem diagonalPotential_drop [Nonempty X] [Nonempty Z] {φ : HwReg X Z M → ℝ}
    (hφ0 : ∀ s, 0 ≤ φ s) (hφ : OneCellLipschitz φ) (W₀ : Hw X Z) (m₀ : M)
    (dR : HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (hdR : ∀ c σ, σ.PosSemidef → dR c σ + ∑' r, potential (diagPot fun s ↦ √(φ s))
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ potential (diagPot fun s ↦ √(φ s)) σ)
    (hdP : ∀ c σ, σ.PosSemidef → dP c σ + ∑' r, potential (diagPot fun s ↦ √(φ s))
      (MatrixMap.conj (hwProgKraus c r) σ) ≤ potential (diagPot fun s ↦ √(φ s)) σ)
    (I : L.Interp) (x : QuantumComp L (hwSpec X Z M) W A) {q : ℕ}
    (hxq : IFreeM.IsChargeBound x (portCharge fun i ↦ if hwCls i then 0 else 1) q)
    {ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ} (hρ : ρ.PosSemidef) :
    (spongeHardwiredRuntime X Z W₀ m₀).totalWeight I (hwCost dR dP) x ρ ≤
      potential (diagPot fun s ↦ √(φ s)) ρ + q * ENNReal.ofReal ρ.trace.re := by
  set R := spongeHardwiredRuntime X Z W₀ m₀
  set K : Matrix (HwReg X Z M) (HwReg X Z M) ℂ := diagPot fun s ↦ √(φ s)
  have hKK : Kᴴ * K = diagPot φ := by
    simp only [K, diagPot, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext s
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hφ0 s)]
  have hdrop : ∀ N, ∑ j ∈ Finset.range N, R.queryWeight I (hwCost dR dP) x ρ j ≤
      potential K ρ + q * ENNReal.ofReal ρ.trace.re := fun N ↦ by
    refine (R.sum_range_queryWeight_le_potential I x N (fun _ ↦ K) (fun _ ↦ hwCost dR dP)
      (fun _ ↦ clsTrace R hwCls) (fun n _ i σ hσ ↦ ?_) hρ).trans ?_
    · rcases i with (p | c) | c
      · have hd := drop_of_posSemidef (fun _ : Unit ↦ (spongeHardwired X Z W₀ m₀).U p) K K 1 hσ
          (by
            rw [Fintype.sum_unique, hKK]
            exact posSemidef_diagonalPotential_drop hφ W₀ m₀ p)
        have hb : ∀ r : Unit, (R.step (.inl (.inl p))).branch r σ =
            MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U p) σ := fun r ↦
          LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge W₀ m₀ p r) σ
        refine (le_of_eq ?_).trans ((le_add_self.trans hd).trans_eq ?_)
        · exact (zero_add _).trans (tsum_congr fun r ↦ congrArg (potential K) (hb r))
        · simp only [clsTrace, hwCls, Bool.false_eq_true, ↓reduceIte]
          exact congrArg (fun N ↦ potential K σ + ENNReal.ofReal N.trace.re) (Matrix.one_mul σ)
      · have hb : ∀ r : c.Result, (R.step (.inl (.inr c))).branch r σ =
            MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
          LinearMap.congr_fun (spongeHardwiredRuntime_step_read W₀ m₀ c r) σ
        refine (le_of_eq ?_).trans ((hdR c σ hσ).trans (le_of_eq (add_zero _).symm))
        exact congrArg (dR c σ + ·) (tsum_congr fun r ↦ congrArg (potential K) (hb r))
      · have hb : ∀ r : c.Result, (R.step (.inr c)).branch r σ =
            MatrixMap.conj (hwProgKraus c r) σ := fun r ↦
          LinearMap.congr_fun (spongeHardwiredRuntime_step_prog W₀ m₀ c r) σ
        refine (le_of_eq ?_).trans ((hdP c σ hσ).trans (le_of_eq (add_zero _).symm))
        exact congrArg (dP c σ + ·) (tsum_congr fun r ↦ congrArg (potential K) (hb r))
    · exact add_le_add le_rfl
        ((ENNReal.sum_le_tsum _).trans (totalWeight_clsTrace_le R I hwCls x q hxq hρ))
  exact ENNReal.tsum_le_of_sum_range_le hdrop

end Quantum.Sponge

end
