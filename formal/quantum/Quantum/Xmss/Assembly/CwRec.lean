module

public import Quantum.Xmss.Assembly.RestMass
public import Quantum.Xmss.Assembly.TrialSource
public import Quantum.Xmss.Assembly.EventSqrt

@[expose] public section

/-!
# The codeword-recorded mass of the randomizer trials

RestMass reduces Security's `restMass` to `CwRecView A τ`. Here the codeword-recorded mass of the
challenge prefix (`cwRecT`) is moved, trial by trial, onto the reveals of the randomizer bases.

* **Moded programs with a final-mode predicate** (`ModedP`, `totalWeight_le_modedP`,
  `totalWeight_le_modedP_inv`, the latter with the step condition on an invariant only).
* **The search modes** (`CwMode`, `cwBlk`, `cwRevLab`, `modedP_prefixR`): a reveal of a label's
  randomizer base starts its search; trial `j` reads `k` at its block `cwBlk`, then `k'` at
  `π (x, a)`, then `h` at `π (x, a).2 + c` with the trial's update.
* **One trial's reads with outcome-dependent weights**, over abstract types and a generic
  recorded-cell predicate (`HitPred`, `cwHit`, `sum_pot_cw_le`: TrialSource's `re_trace_gramQ_le`
  at the `k'`-cell, then at the `k`-cell; `cB_out_le`: at most `4` on a recorded or hardwired
  block with the key unselected, plus the fresh part `cwFresh`).
* **The potentials** (`cwKp`): after the `k`-read the codeword-recorded `h`-cell through each
  `k'`-outcome, after the `k'`-read that cell, and in a search four times each later trial already
  started (`cwTD`: block recorded or hardwired, key unselected). A weight scaled down along a Kraus
  family (`sum_dW_conj_le_scale`) covers the `h`-read, which can only select the key.
* **The reduction** (`cw_step`, `cwRecT_le_charge`): the codeword-recorded mass is at most the
  fresh parts of the `k`-reads plus, at each reveal, four times the trials already started
  (`cwRevW`). The fresh parts are counted (`cwFresh_le_count`) on the database grade and the
  hardwired `k'`-cells, at most `6q + clsCap` each: `cwFreshEps` per read, `clsCap` reads
  (`totalWeight_cwFreshW_le`).
* **`CwRecView` from the reveals** (`cwRecView_of_revView`): `CwRevView A R` (the reveals' charges
  summed over the hidden values) gives `CwRecView A (R + cwFreshEps (6q + clsCap) · clsCap)`.
  `CwRevView` is the remaining lemma: at a first reveal of a label the trial blocks carry the
  undisclosed base (Disclose's view lemma), at a repeated one the key is unselected only after a
  failed search.
-/

universe u v w w'

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid

/-! ## Potentials of projectors after a Kraus operator, over any register -/

section potGen

variable {D : Type} [Fintype D] [DecidableEq D]

omit [Fintype D] in
theorem cw_kron_setProj_eq (S : Set D) :
    (1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S =
      diagonal fun t : Unit × D ↦ (((Set.indicator S 1 t.2 : ℝ)) : ℂ) := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  simp only [kroneckerMap_apply, setProj, diagonal_apply, Matrix.one_apply, Set.indicator,
    Pi.one_apply]
  by_cases hd : d = d'
  · subst hd
    by_cases hS : d ∈ S <;> simp [hS]
  · simp [hd]

omit [DecidableEq D] in
theorem cw_potential_eq_kron (K : Matrix D D ℂ) (ρ : Matrix (Unit × D) (Unit × D) ℂ) :
    potential K ρ = ENNReal.ofReal
      ((((1 : Matrix Unit Unit ℂ) ⊗ₖ K)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ K) * ρ).trace.re) := by
  rw [potential_eq, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    Matrix.one_mul]

theorem cw_potential_setProj_mul_eq (S : Set D) (N : Matrix D D ℂ)
    (ρ : Matrix (Unit × D) (Unit × D) ℂ) :
    potential (setProj S * N) ρ = ENNReal.ofReal
      ((((1 : Matrix Unit Unit ℂ) ⊗ₖ N)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ N) * ρ).trace.re) := by
  have h1 : (1 : Matrix Unit Unit ℂ) ⊗ₖ (setProj S * N) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ N) := by
    rw [← mul_kronecker_mul, Matrix.one_mul]
  have hP : ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S)ᴴ = (1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S := by
    rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_setProj]
  have hPP : ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S) =
      (1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S := by
    rw [← mul_kronecker_mul, Matrix.one_mul, setProj_mul_self]
  have key : ((1 : Matrix Unit Unit ℂ) ⊗ₖ (setProj S * N))ᴴ *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ (setProj S * N)) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ N)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ N) := by
    rw [h1, conjTranspose_mul, hP, Matrix.mul_assoc, ← Matrix.mul_assoc (1 ⊗ₖ setProj S), hPP,
      Matrix.mul_assoc]
  rw [cw_potential_eq_kron, key]

theorem cw_re_trace_conj_diag_nonneg {f : Unit × D → ℝ} (hf : ∀ t, 0 ≤ f t)
    (N : Matrix (Unit × D) (Unit × D) ℂ) {ρ : Matrix (Unit × D) (Unit × D) ℂ}
    (hρ : ρ.PosSemidef) :
    0 ≤ (Nᴴ * diagonal (fun t ↦ ((f t : ℝ) : ℂ)) * N * ρ).trace.re := by
  have hP : (diagonal fun t ↦ ((f t : ℝ) : ℂ)).PosSemidef :=
    PosSemidef.diagonal fun t ↦ Complex.zero_le_real.mpr (hf t)
  exact (hP.conjTranspose_mul_mul_same N).trace_mul_re_nonneg hρ

/-- The diagonal weight after a Kraus operator, as the trace of its weighted Gram operator. -/
theorem cw_dW_conj (K : Matrix (Unit × D) (Unit × D) ℂ) (f : Unit × D → ℝ)
    (σ : Matrix (Unit × D) (Unit × D) ℂ) :
    ∑ t, f t * ((MatrixMap.conj K σ) t t).re =
      (Kᴴ * diagonal (fun t ↦ ((f t : ℝ) : ℂ)) * K * σ).trace.re := by
  have h := sum_dW_conj (fun _ : Unit ↦ K) f σ
  simp only [Fintype.sum_unique] at h
  exact h

end potGen

/-! ## A trial's `k`-read with the codeword-recorded weight of its `h`-cell, over abstract types -/

section cell

open Quantum.Sponge

variable {X₁ Z₁ M : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [Fintype M] [DecidableEq M]

/-- A recorded-cell predicate: for the rate `xi` and the `h`-cell `z`, a property of the `h`
database, the hardwired cells and the memory. -/
abbrev HitPred (X₁ Z₁ M : Type) : Type := X₁ → Z₁ → Database Z₁ X₁ → Hw X₁ Z₁ × M → Prop

/-- The register states whose `h`-cell `z` satisfies the recorded-cell predicate for `xi`. -/
def cwHit (Hp : HitPred X₁ Z₁ M) (xi : X₁) (z : Z₁) : Set (HwReg X₁ Z₁ M) :=
  {s | Hp xi z s.1.1 s.2}

open scoped Classical in
/-- The indicator of a recorded-cell predicate. -/
noncomputable def cwInd (Hp : HitPred X₁ Z₁ M) (xi : X₁) (z : Z₁)
    (dh : Database Z₁ X₁) (wm : Hw X₁ Z₁ × M) : ℝ :=
  if Hp xi z dh wm then 1 else 0

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
theorem cwInd_nonneg (Hp : HitPred X₁ Z₁ M) (xi : X₁) (z : Z₁)
    (dh : Database Z₁ X₁) (wm : Hw X₁ Z₁ × M) : 0 ≤ cwInd Hp xi z dh wm := by
  unfold cwInd
  split_ifs <;> norm_num

open scoped Classical in
omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
/-- The indicator vanishes off a memory condition `U` that the predicate implies. -/
theorem cwInd_le_U {Hp : HitPred X₁ Z₁ M} {U : M → Prop}
    (hU : ∀ xi z dh wm, Hp xi z dh wm → U wm.2) (xi : X₁) (z : Z₁)
    (dh : Database Z₁ X₁) (wm : Hw X₁ Z₁ × M) :
    cwInd Hp xi z dh wm ≤ if U wm.2 then 1 else 0 := by
  unfold cwInd
  by_cases h : Hp xi z dh wm
  · rw [ite_eq_left h, ite_eq_left (hU _ _ _ _ h)]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
/-- The indicator grows with the conditions. -/
theorem cwInd_mono {Hp Hp' : HitPred X₁ Z₁ M}
    (hH : ∀ xi z dh wm, Hp xi z dh wm → Hp' xi z dh wm) (xi : X₁) (z : Z₁)
    (dh : Database Z₁ X₁) (wm : Hw X₁ Z₁ × M) :
    cwInd Hp xi z dh wm ≤ cwInd Hp' xi z dh wm := by
  classical
  unfold cwInd
  by_cases h : Hp xi z dh wm
  · rw [ite_eq_left h, ite_eq_left (hH _ _ _ _ h)]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
theorem indicator_cwHit (Hp : HitPred X₁ Z₁ M) (xi : X₁) (z : Z₁) (s : HwReg X₁ Z₁ M) :
    (Set.indicator (cwHit Hp xi z) 1 s : ℝ) = cwInd Hp xi z s.1.1 s.2 := by
  classical
  unfold cwInd
  by_cases h : Hp xi z s.1.1 s.2
  · rw [Set.indicator_of_mem (show s ∈ cwHit Hp xi z from h), ite_eq_left h, Pi.one_apply]
  · rw [Set.indicator_of_notMem (show s ∉ cwHit Hp xi z from h), ite_eq_right h]

/-- The weight of a `k'`-read's rests: the codeword-recorded indicator of the `h`-cell
`z0 + c` for the outcome `c`. -/
noncomputable def cwQIn [AddCommGroup Z₁] (Hp : HitPred X₁ Z₁ M) (y xi : X₁)
    (z0 : Z₁) (o : Option Z₁) (r : RestK X₁ Z₁ M y) : ℝ :=
  cwInd Hp xi (z0 + o.getD 0) r.2.1 r.2.2.2

/-- **The bound after the `k'`-read at `y`**, a function of the `h` and `k'` databases, the
hardwired cells and the memory: the codeword-recorded indicator of the `h`-cell `z0 + c` for a
hardwired value `c`, twice it for a recorded one, `2/|Z|` times their sum on an empty cell. -/
noncomputable def cwBetaIn [AddCommGroup Z₁] (Hp : HitPred X₁ Z₁ M) (y xi : X₁)
    (z0 : Z₁) (dh : Database Z₁ X₁) (dk' : Database X₁ Z₁) (wm : Hw X₁ Z₁ × M) : ℝ :=
  match wm.1.2.2 y, dk' y with
  | some c, _ => cwInd Hp xi (z0 + c) dh wm
  | none, some c => 2 * cwInd Hp xi (z0 + c) dh wm
  | none, none => 2 / Fintype.card Z₁ * ∑ c, cwInd Hp xi (z0 + c) dh wm

variable [AddCommGroup Z₁]

omit [Fintype X₁] [DecidableEq X₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
theorem cwBetaIn_nonneg (Hp : HitPred X₁ Z₁ M) (y xi : X₁) (z0 : Z₁)
    (dh : Database Z₁ X₁) (dk' : Database X₁ Z₁) (wm : Hw X₁ Z₁ × M) :
    0 ≤ cwBetaIn Hp y xi z0 dh dk' wm := by
  unfold cwBetaIn
  split
  · exact cwInd_nonneg Hp _ _ dh wm
  · exact mul_nonneg zero_le_two (cwInd_nonneg Hp _ _ dh wm)
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun c _ ↦ cwInd_nonneg Hp _ _ dh wm)

open scoped Classical in
omit [Fintype X₁] [DecidableEq X₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
/-- The bound after the `k'`-read is at most `2`, and vanishes off `U`. -/
theorem cwBetaIn_le_U [Nonempty Z₁] {Hp : HitPred X₁ Z₁ M} {U : M → Prop}
    (hU : ∀ xi z dh wm, Hp xi z dh wm → U wm.2) (y xi : X₁) (z0 : Z₁)
    (dh : Database Z₁ X₁) (dk' : Database X₁ Z₁) (wm : Hw X₁ Z₁ × M) :
    cwBetaIn Hp y xi z0 dh dk' wm ≤ 2 * if U wm.2 then 1 else 0 := by
  have hu := fun c ↦ cwInd_le_U hU xi (z0 + c) dh wm
  have hn : (0 : ℝ) ≤ if U wm.2 then 1 else 0 := by split_ifs <;> norm_num
  unfold cwBetaIn
  split
  · refine (hu _).trans ?_
    linarith
  · exact mul_le_mul_of_nonneg_left (hu _) zero_le_two
  · have hN : (0 : ℝ) < Fintype.card Z₁ := by exact_mod_cast Fintype.card_pos
    calc 2 / (Fintype.card Z₁ : ℝ) * ∑ c, cwInd Hp xi (z0 + c) dh wm
        ≤ 2 / (Fintype.card Z₁ : ℝ) * ∑ _c : Z₁, (if U wm.2 then (1 : ℝ) else 0) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ ↦ hu c) (by positivity)
      _ = 2 * if U wm.2 then 1 else 0 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp

omit [Fintype X₁] [DecidableEq X₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
/-- The bound grows with the conditions. -/
theorem cwBetaIn_mono {Hp Hp' : HitPred X₁ Z₁ M}
    (hH : ∀ xi z dh wm, Hp xi z dh wm → Hp' xi z dh wm) (y xi : X₁) (z0 : Z₁)
    (dh : Database Z₁ X₁) (dk' : Database X₁ Z₁) (wm : Hw X₁ Z₁ × M) :
    cwBetaIn Hp y xi z0 dh dk' wm ≤ cwBetaIn Hp' y xi z0 dh dk' wm := by
  have hm := fun c ↦ cwInd_mono hH xi (z0 + c) dh wm
  unfold cwBetaIn
  split
  · exact hm _
  · exact mul_le_mul_of_nonneg_left (hm _) zero_le_two
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ ↦ hm c) (by positivity)

omit [Fintype M] in
theorem kron_setProj_cwHit (Hp : HitPred X₁ Z₁ M) (y xi : X₁) (z0 : Z₁)
    (o : Option Z₁) :
    (1 : Matrix Unit Unit ℂ) ⊗ₖ setProj (cwHit Hp xi (z0 + o.getD 0)) =
      wDiag (splitK' y) (cwQIn Hp y xi z0) o := by
  rw [cw_kron_setProj_eq, wDiag]
  congr 1

omit [Fintype X₁] [Fintype M] [DecidableEq Z₁] [DecidableEq M] in
theorem cB_in_eq (Hp : HitPred X₁ Z₁ M) (y xi : X₁) (z0 : Z₁)
    (t : Unit × HwReg X₁ Z₁ M) :
    cB (splitK' y) (actK' y) (tauK y fun m _ ↦ m) (idxK' y) (phiK' y fun m _ ↦ m)
      (cwQIn Hp y xi z0) t = cwBetaIn Hp y xi z0 t.2.1.1 t.2.1.2.2 t.2.2 := by
  obtain ⟨⟨⟩, ⟨dh, dk, dk'⟩, W, m⟩ := t
  rcases hW : W.2.2 y with _ | c <;> rcases hd : dk' y with _ | c'
  all_goals simp [cB, cwBetaIn, cwQIn, splitK', actK', tauK, idxK', phiK', hW, hd]

/-- The weight of a `k`-read's rests for the trial of block `x`: the bound after the `k'`-read at
`π (x, a)` for the outcome `a`. -/
noncomputable def cwQOut (Hp : HitPred X₁ Z₁ M) (π : Equiv.Perm (X₁ × Z₁))
    (x : X₁) (o : Option Z₁) (r : RestK X₁ Z₁ M x) : ℝ :=
  cwBetaIn Hp (π (x, o.getD 0)).1 (π (x, o.getD 0)).1 (π (x, o.getD 0)).2 r.2.1 r.2.2.1 r.2.2.2

/-- The inner read: the codeword-recorded potentials after a `k'`-read at `y`. -/
theorem sum_pot_in_le [Nonempty Z₁] (Hp : HitPred X₁ Z₁ M) (y xi : X₁) (z0 : Z₁)
    {τ : Matrix (Unit × HwReg X₁ Z₁ M) (Unit × HwReg X₁ Z₁ M) ℂ} (hτ : τ.PosSemidef)
    (hnb : CellNoBot (splitK' y) (actK' y) τ) :
    ∑ r : Option Z₁ × M, potential (setProj (cwHit Hp xi (z0 + r.1.getD 0)) *
        readKrausK' y (fun m _ ↦ m) r) τ ≤
      ENNReal.ofReal (∑ s, cwBetaIn Hp y xi z0 s.2.1.1 s.2.1.2.2 s.2.2 * (τ s s).re) := by
  have hA : ∀ r : Option Z₁ × M,
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK' y (fun m _ ↦ m) r)ᴴ *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj (cwHit Hp xi (z0 + r.1.getD 0))) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK' y (fun m _ ↦ m) r) =
      (hwReadKraus (.readK' y fun m _ ↦ m) r)ᴴ * wDiag (splitK' y) (cwQIn Hp y xi z0) r.1 *
        hwReadKraus (.readK' y fun m _ ↦ m) r := fun r ↦ by
    rw [kron_setProj_cwHit Hp y xi z0 r.1]
    rfl
  simp only [cw_potential_setProj_mul_eq, hA]
  have hnn : ∀ r : Option Z₁ × M, 0 ≤ ((hwReadKraus (.readK' y fun m _ ↦ m) r)ᴴ *
      wDiag (splitK' y) (cwQIn Hp y xi z0) r.1 * hwReadKraus (.readK' y fun m _ ↦ m) r *
        τ).trace.re := fun r ↦
    cw_re_trace_conj_diag_nonneg (fun t ↦ cwInd_nonneg Hp _ _ _ _) _ hτ
  rw [← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hnn r]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul]
  refine (re_trace_gramQ_le (cellRead_readK' y fun m _ ↦ m) (clsOff_readK' y fun m _ ↦ m)
    (cwQIn Hp y xi z0) (fun o r ↦ cwInd_nonneg Hp _ _ _ _) hτ hnb).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun s _ ↦ by rw [cB_in_eq]

/-- **The trial's `k`-read and `k'`-read**: the codeword-recorded potentials after both reads
are at most the diagonal bound `cB` of the `k`-read with the weights `cwQOut`. -/
theorem sum_pot_cw_le [Nonempty Z₁] (Hp : HitPred X₁ Z₁ M)
    (π : Equiv.Perm (X₁ × Z₁)) (x : X₁)
    {σ : Matrix (Unit × HwReg X₁ Z₁ M) (Unit × HwReg X₁ Z₁ M) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitK x) (actK x) σ)
    (hnb' : ∀ r : Option Z₁ × M, CellNoBot (splitK' (π (x, r.1.getD 0)).1)
      (actK' (π (x, r.1.getD 0)).1) (MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ)) :
    ∑ r : Option Z₁ × M, ∑ r' : Option Z₁ × M,
        potential (setProj (cwHit Hp (π (x, r.1.getD 0)).1
          ((π (x, r.1.getD 0)).2 + r'.1.getD 0)) * readKrausK' (π (x, r.1.getD 0)).1
            (fun m _ ↦ m) r') (MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) ≤
      ENNReal.ofReal (∑ s, cB (splitK x) (actK x) (tauK x fun m _ ↦ m) (idxK x)
        (phiK x fun m _ ↦ m) (cwQOut Hp π x) s * (σ s s).re) := by
  have hσr := fun r : Option Z₁ × M ↦ posSemidef_conj (hwReadKraus (.readK x fun m _ ↦ m) r) hσ
  have hnn : ∀ r : Option Z₁ × M, 0 ≤ ∑ s, cwBetaIn Hp (π (x, r.1.getD 0)).1
      (π (x, r.1.getD 0)).1 (π (x, r.1.getD 0)).2 s.2.1.1 s.2.1.2.2 s.2.2 *
        ((MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) s s).re := fun r ↦
    Finset.sum_nonneg fun s _ ↦ mul_nonneg (cwBetaIn_nonneg Hp _ _ _ _ _ _)
      (Complex.nonneg_iff.1 (hσr r).diag_nonneg).1
  have hdiag : ∀ r : Option Z₁ × M, ∑ s, cwBetaIn Hp (π (x, r.1.getD 0)).1
      (π (x, r.1.getD 0)).1 (π (x, r.1.getD 0)).2 s.2.1.1 s.2.1.2.2 s.2.2 *
        ((MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) s s).re =
      ((hwReadKraus (.readK x fun m _ ↦ m) r)ᴴ * wDiag (splitK x) (cwQOut Hp π x) r.1 *
        hwReadKraus (.readK x fun m _ ↦ m) r * σ).trace.re := fun r ↦
    cw_dW_conj _ (fun s ↦ cwBetaIn Hp (π (x, r.1.getD 0)).1 (π (x, r.1.getD 0)).1
      (π (x, r.1.getD 0)).2 s.2.1.1 s.2.1.2.2 s.2.2) σ
  calc _ ≤ ∑ r : Option Z₁ × M, ENNReal.ofReal (∑ s, cwBetaIn Hp (π (x, r.1.getD 0)).1
          (π (x, r.1.getD 0)).1 (π (x, r.1.getD 0)).2 s.2.1.1 s.2.1.2.2 s.2.2 *
            ((MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) s s).re) :=
        Finset.sum_le_sum fun r _ ↦ sum_pot_in_le Hp _ _ _ (hσr r) (hnb' r)
    _ = ENNReal.ofReal (((∑ r : Option Z₁ × M, (hwReadKraus (.readK x fun m _ ↦ m) r)ᴴ *
          wDiag (splitK x) (cwQOut Hp π x) r.1 * hwReadKraus (.readK x fun m _ ↦ m) r) *
            σ).trace.re) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hnn r, Finset.sum_mul, Matrix.trace_sum,
          Complex.re_sum]
        exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun r _ ↦ hdiag r)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (re_trace_gramQ_le (cellRead_readK x fun m _ ↦ m)
        (clsOff_readK x fun m _ ↦ m) (cwQOut Hp π x)
        (fun o r ↦ cwBetaIn_nonneg Hp _ _ _ _ _ _) hσ hnb)

open scoped Classical in
/-- The trial's `k`-cell `x` is recorded or hardwired, the memory in `U`. -/
noncomputable def cwRecHw (U : M → Prop) (x : X₁) (s : Unit × HwReg X₁ Z₁ M) : ℝ :=
  if (s.2.1.2.1 x ≠ none ∨ s.2.2.1.2.1 x ≠ none) ∧ U s.2.2.2 then 1 else 0

open scoped Classical in
/-- **The fresh `k`-cell part**: on a cell `x` neither recorded nor hardwired, `2/|Z|` times the
bounds after the `k'`-reads of all outcomes. -/
noncomputable def cwFresh (Hp : HitPred X₁ Z₁ M) (π : Equiv.Perm (X₁ × Z₁)) (x : X₁)
    (s : Unit × HwReg X₁ Z₁ M) : ℝ :=
  if s.2.1.2.1 x = none ∧ s.2.2.1.2.1 x = none then
    2 / Fintype.card Z₁ * ∑ a, cwBetaIn Hp (π (x, a)).1 (π (x, a)).1 (π (x, a)).2 s.2.1.1 s.2.1.2.2
      s.2.2
  else 0

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M]
  [AddCommGroup Z₁] in
theorem cwRecHw_nonneg (U : M → Prop) (x : X₁) (s : Unit × HwReg X₁ Z₁ M) :
    0 ≤ cwRecHw (Z₁ := Z₁) U x s := by
  unfold cwRecHw
  split_ifs <;> norm_num

omit [Fintype X₁] [DecidableEq X₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
theorem cwFresh_nonneg (Hp : HitPred X₁ Z₁ M) (π : Equiv.Perm (X₁ × Z₁)) (x : X₁)
    (s : Unit × HwReg X₁ Z₁ M) : 0 ≤ cwFresh Hp π x s := by
  unfold cwFresh
  split_ifs
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ ↦ cwBetaIn_nonneg Hp _ _ _ _ _ _)
  · exact le_rfl

omit [Fintype X₁] [DecidableEq X₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
/-- The fresh part grows with the predicate. -/
theorem cwFresh_mono {Hp Hp' : HitPred X₁ Z₁ M}
    (hH : ∀ xi z dh wm, Hp xi z dh wm → Hp' xi z dh wm) (π : Equiv.Perm (X₁ × Z₁)) (x : X₁)
    (s : Unit × HwReg X₁ Z₁ M) : cwFresh Hp π x s ≤ cwFresh Hp' π x s := by
  unfold cwFresh
  split_ifs
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ ↦ cwBetaIn_mono hH _ _ _ _ _ _)
      (by positivity)
  · exact le_rfl

omit [Fintype X₁] [Fintype M] [DecidableEq M] [DecidableEq Z₁] in
/-- **The diagonal bound of a trial's `k`-read, pointwise**: at most `4` on a recorded or
hardwired `k`-cell with the memory in `U`, plus the fresh part. -/
theorem cB_out_le [Nonempty Z₁] {Hp : HitPred X₁ Z₁ M} {U : M → Prop}
    (hU : ∀ xi z dh wm, Hp xi z dh wm → U wm.2) (π : Equiv.Perm (X₁ × Z₁)) (x : X₁)
    (s : Unit × HwReg X₁ Z₁ M) :
    cB (splitK x) (actK x) (tauK x fun m _ ↦ m) (idxK x) (phiK x fun m _ ↦ m) (cwQOut Hp π x) s ≤
      4 * cwRecHw U x s + cwFresh Hp π x s := by
  classical
  obtain ⟨⟨⟩, ⟨dh, dk, dk'⟩, W, m⟩ := s
  have hb := fun a : Z₁ ↦ cwBetaIn_le_U hU (π (x, a)).1 (π (x, a)).1 (π (x, a)).2 dh dk' (W, m)
  have hn : (0 : ℝ) ≤ if U m then 1 else 0 := by split_ifs <;> norm_num
  rcases hW : W.2.1 x with _ | a <;> rcases hd : dk x with _ | a'
  · simp [cB, splitK, actK, tauK, cwQOut, cwRecHw, cwFresh, hW, hd]
  · have h4 : cwRecHw U x ((), ((dh, dk, dk'), W, m)) = if U m then 1 else 0 := by
      simp [cwRecHw, hd]
    have h0 : cwFresh Hp π x ((), ((dh, dk, dk'), W, m)) = 0 := by simp [cwFresh, hd]
    rw [h4, h0]
    simp only [cB, splitK, actK, tauK, cwQOut, Equiv.coe_fn_mk, hW, hd, ↓reduceIte,
      Option.elim_some, Option.getD_some]
    have := hb a'
    linarith
  · have h4 : cwRecHw U x ((), ((dh, dk, dk'), W, m)) = if U m then 1 else 0 := by
      simp [cwRecHw, hW]
    have h0 : cwFresh Hp π x ((), ((dh, dk, dk'), W, m)) = 0 := by simp [cwFresh, hW]
    rw [h4, h0]
    simp only [cB, splitK, actK, idxK, phiK, cwQOut, Equiv.coe_fn_mk, hW, reduceCtorEq,
      ↓reduceIte, Option.getD_some]
    have := hb a
    linarith
  · have h4 : cwRecHw U x ((), ((dh, dk, dk'), W, m)) = if U m then 1 else 0 := by
      simp [cwRecHw, hW]
    have h0 : cwFresh Hp π x ((), ((dh, dk, dk'), W, m)) = 0 := by simp [cwFresh, hW]
    rw [h4, h0]
    simp only [cB, splitK, actK, idxK, phiK, cwQOut, Equiv.coe_fn_mk, hW, reduceCtorEq,
      ↓reduceIte, Option.getD_some]
    have := hb a
    linarith

end cell

/-! ## Weights after a Kraus family that scales a weight -/

section scale

variable {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι]

/-- **A weight scaled down along a Kraus family**: if every nonzero entry `K r s' a` gives
`f' s' = c r f a` with `c r ≤ 1`, and `f` is constant along the nonzero entries of each row,
the weights `f'` after the family add up to at most the weight `f` before. -/
theorem sum_dW_conj_le_scale (K : ι → Matrix n n ℂ) (hK : ∑ r, (K r)ᴴ * K r = 1) (f f' : n → ℝ)
    (hf : ∀ a, 0 ≤ f a) (c : ι → ℝ) (hc1 : ∀ r, c r ≤ 1)
    (h1 : ∀ r s' a, K r s' a ≠ 0 → f' s' = c r * f a)
    (h2 : ∀ r s' a b, K r s' a ≠ 0 → K r s' b ≠ 0 → f a = f b)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    ∑ r, dW f' (MatrixMap.conj (K r) σ) ≤ dW f σ := by
  set N : Matrix n n ℂ := diagonal fun a ↦ ((√(f a) : ℝ) : ℂ)
  have hN : Nᴴ = N := by
    simp only [N, diagonal_conjTranspose]
    congr 1
    funext a
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  set τ := N * σ * N
  have hτ : τ.PosSemidef := by
    have := hσ.mul_mul_conjTranspose_same N
    rwa [hN] at this
  have hτe : ∀ a b, τ a b = ((√(f a) : ℝ) : ℂ) * σ a b * ((√(f b) : ℝ) : ℂ) := fun a b ↦ by
    simp only [τ, N, mul_diagonal, diagonal_mul]
  have hentry : ∀ r s', (f' s' : ℂ) * (MatrixMap.conj (K r) σ) s' s' =
      (c r : ℂ) * (MatrixMap.conj (K r) τ) s' s' := fun r s' ↦ by
    simp only [MatrixMap.conj_apply, Matrix.mul_apply, conjTranspose_apply, hτe,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
    by_cases ha : K r s' a = 0
    · simp [ha]
    by_cases hb : K r s' b = 0
    · simp [hb]
    have e1 := h1 r s' a ha
    have e2 := h2 r s' a b ha hb
    have e3 : ((√(f a) : ℝ) : ℂ) * ((√(f b) : ℝ) : ℂ) = (f a : ℂ) := by
      rw [← e2, ← Complex.ofReal_mul, Real.mul_self_sqrt (hf a)]
    rw [e1]
    push_cast
    linear_combination (c r : ℂ) * K r s' a * σ a b * star (K r s' b) * e3.symm
  have hdW : ∀ r, dW f' (MatrixMap.conj (K r) σ) = c r * ((MatrixMap.conj (K r) τ).trace.re) :=
    fun r ↦ by
      unfold dW
      rw [Matrix.trace, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ ↦ ?_
      have := congrArg Complex.re (hentry r s')
      rwa [Complex.re_ofReal_mul, Complex.re_ofReal_mul] at this
  have hnn : ∀ r, 0 ≤ (MatrixMap.conj (K r) τ).trace.re := fun r ↦
    (Complex.nonneg_iff.1 (posSemidef_conj (K r) hτ).trace_nonneg).1
  have htr : ∑ r, (MatrixMap.conj (K r) τ).trace.re = τ.trace.re := by
    rw [← Complex.re_sum, ← Matrix.trace_sum]
    simp only [MatrixMap.conj_apply]
    rw [show ∑ r, K r * τ * (K r)ᴴ = ∑ r, K r * (τ * (K r)ᴴ) from
      Finset.sum_congr rfl fun r _ ↦ Matrix.mul_assoc _ _ _]
    simp only [Matrix.trace_sum, Matrix.trace_mul_comm (K _)]
    rw [← Matrix.trace_sum, show ∑ r, τ * (K r)ᴴ * K r = τ * ∑ r, (K r)ᴴ * K r by
      rw [Matrix.mul_sum]; simp only [Matrix.mul_assoc], hK, Matrix.mul_one]
  have hτd : τ.trace.re = dW f σ := by
    unfold dW
    rw [Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [τ, N, Matrix.diag_apply, mul_diagonal, diagonal_mul]
    rw [mul_comm, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (hf a),
      Complex.re_ofReal_mul]
  calc ∑ r, dW f' (MatrixMap.conj (K r) σ) = ∑ r, c r * (MatrixMap.conj (K r) τ).trace.re :=
        Finset.sum_congr rfl fun r _ ↦ hdW r
    _ ≤ ∑ r, (MatrixMap.conj (K r) τ).trace.re :=
        Finset.sum_le_sum fun r _ ↦ mul_le_of_le_one_left (hnn r) (hc1 r)
    _ = dW f σ := htr.trans hτd

end scale


/-! ## Moded programs with a final-mode predicate -/

section modedP

variable {spec : QuantumOracleSpec.{0, 0}} {L : LocalSig.{u, v}} {Ω : QReg → Type w}
  {Mode : Type} (ok : Mode → spec.Port → Prop) (nx : Mode → (i : spec.Port) → spec.Result i → Mode)

/-- **A moded program with a final-mode predicate**: from the mode `μ`, every call is allowed by
the current mode, which moves by the call's result; every leaf `a` is reached in a mode `μ'` with
`fin a μ'`. -/
def ModedP (fin : (Σ u, Ω u) → Mode → Prop) :
    Mode → {A : QReg} → IFreeM (QuantumComp.toIPFunctor L spec) Ω A → Prop
  | μ, _, .pure a => fin ⟨_, a⟩ μ
  | μ, _, .liftBind c next =>
      modeCmdOk ok c μ ∧ ∀ b, ModedP fin (modeCmdNx nx c μ b) (next b)

variable {ok nx}

theorem modedP_bind {Y : QReg → Type w'} {fin : (Σ u, Ω u) → Mode → Prop}
    {fin' : (Σ u, Y u) → Mode → Prop} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L spec) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor L spec) Y u) {μ : Mode}
    (hx : ModedP ok nx fin μ x) (hg : ∀ u a μ', fin ⟨u, a⟩ μ' → ModedP ok nx fin' μ' (g u a)) :
    ModedP ok nx fin' μ (x.bind g) := by
  induction x using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hg _ a μ hx
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem modedP₂_bind {A B B' : QReg} {α β : Type} {F : α → Mode → Prop} {F' : β → Mode → Prop}
    (x : QuantumComp₂ L spec A B α) (g : α → QuantumComp₂ L spec B B' β) {μ : Mode}
    (hx : ModedP ok nx (fun p μ ↦ F p.2.2 μ) μ x)
    (hg : ∀ a μ', F a μ' → ModedP ok nx (fun p μ ↦ F' p.2.2 μ) μ' (g a)) :
    ModedP ok nx (fun p μ ↦ F' p.2.2 μ) μ (x.bind g) := by
  refine modedP_bind x _ hx fun u p μ' h ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a μ' h

theorem modedP_map {A B' : QReg} {γ δ : Type} {x : QuantumComp₂ L spec A B' γ} (g : γ → δ)
    {F : δ → Mode → Prop} {μ : Mode} (hx : ModedP ok nx (fun p μ ↦ F (g p.2.2) μ) μ x) :
    ModedP ok nx (fun p μ ↦ F p.2.2 μ) μ (x.map g) := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact modedP₂_bind (F := fun a μ ↦ F (g a) μ) _ _ hx fun _ _ h ↦ h

theorem modedP_act {A B : QReg} {α : Type} {F : α → Mode → Prop} (p : SubInstrument A B α)
    (μ : Mode) (h : ∀ a, F a μ) :
    ModedP (L := LocalSig.instruments) ok nx (fun q μ ↦ F q.2.2 μ) μ (QComp.act (spec := spec) p) :=
  ⟨trivial, fun b ↦ h b.down⟩

variable (R : QuantumRuntime spec) (I : L.Interp)

/-- **Moving the weight along a moded program** (TrialSource's `totalWeight_le_moded` with a
final-mode predicate). -/
theorem totalWeight_le_modedP {Zp J : Type*} [Fintype Zp] [Fintype J]
    (Kp : Mode → J → Matrix Zp R.D ℂ)
    (w c : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (h : ∀ μ i σ, σ.PosSemidef → ok μ i →
      w i σ + ∑' r, ∑ j, potential (Kp (nx μ i r) j) ((R.step i).branch r σ) ≤
        ∑ j, potential (Kp μ j) σ + c i σ)
    {fin : (Σ u, Ω u) → Mode → Prop} {A : QReg} (x : QuantumComp L spec Ω A) :
    ∀ μ, ModedP ok nx fin μ x → ∀ {ρ : Matrix (A × R.D) (A × R.D) ℂ}, ρ.PosSemidef →
      R.totalWeight I w x ρ ≤ ∑ j, potential (Kp μ j) ρ + R.totalWeight I c x ρ := by
  classical
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    intro μ _ ρ _
    rw [totalWeight_pure]
    exact zero_le
  | primBind _ o k ih =>
    intro μ hx ρ hρ
    have hb := fun b ↦ ((I o).frame R.D).posSemidef_branch_apply b hρ
    rw [totalWeight_primBind, totalWeight_primBind]
    calc ∑' b, R.totalWeight I w (k b) (((I o).frame R.D).branch b ρ)
        ≤ ∑' b, (∑ j, potential (Kp μ j) (((I o).frame R.D).branch b ρ) +
            R.totalWeight I c (k b) (((I o).frame R.D).branch b ρ)) :=
          ENNReal.tsum_le_tsum fun b ↦ ih b μ (hx.2 (ULift.up b)) (hb b)
      _ = ∑ j, ∑' b, potential (Kp μ j) (((I o).frame R.D).branch b ρ) +
            ∑' b, R.totalWeight I c (k b) (((I o).frame R.D).branch b ρ) := by
          rw [ENNReal.tsum_add, Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
      _ ≤ _ := by
          gcongr with j
          exact tsum_potential_frame_le (Kp μ j) (I o) hρ
  | queryBind _ i E ℓ k ih =>
    intro μ hx ρ hρ
    have hσ := posSemidef_callInput ℓ hρ
    have hb := fun r ↦ (R.queryStep i E ℓ).posSemidef_branch_apply r hρ
    rw [totalWeight_queryBind, totalWeight_queryBind]
    have hk : ∀ r, R.totalWeight I w (k r) ((R.queryStep i E ℓ).branch r ρ) ≤
        ∑ j, potential (Kp (nx μ i r) j) ((R.step i).branch r (callInput ℓ R.D ρ)) +
          R.totalWeight I c (k r) ((R.queryStep i E ℓ).branch r ρ) := fun r ↦ by
      simp only [← potential_queryStep]
      exact ih r _ (hx.2 (ULift.up r)) (hb r)
    calc w i (callInput ℓ R.D ρ) + ∑' r, R.totalWeight I w (k r) ((R.queryStep i E ℓ).branch r ρ)
        ≤ w i (callInput ℓ R.D ρ) + ∑' r, (∑ j, potential (Kp (nx μ i r) j)
            ((R.step i).branch r (callInput ℓ R.D ρ)) +
            R.totalWeight I c (k r) ((R.queryStep i E ℓ).branch r ρ)) := by
          gcongr with r
          exact hk r
      _ = (w i (callInput ℓ R.D ρ) + ∑' r, ∑ j, potential (Kp (nx μ i r) j)
            ((R.step i).branch r (callInput ℓ R.D ρ))) +
            ∑' r, R.totalWeight I c (k r) ((R.queryStep i E ℓ).branch r ρ) := by
          rw [ENNReal.tsum_add, add_assoc]
      _ ≤ (∑ j, potential (Kp μ j) (callInput ℓ R.D ρ) + c i (callInput ℓ R.D ρ)) +
            ∑' r, R.totalWeight I c (k r) ((R.queryStep i E ℓ).branch r ρ) := by
          exact add_le_add (h μ i _ hσ hx.1) le_rfl
      _ = _ := by
          simp only [potential_callInput]
          rw [add_assoc]

/-- **`totalWeight_le_modedP` on an invariant**: the step condition only for inputs satisfying
`Inv`, when every call of the run is presented an operator satisfying `P`, which gives `Inv`. -/
theorem totalWeight_le_modedP_inv {Zp J : Type*} [Fintype Zp] [Fintype J]
    (Kp : Mode → J → Matrix Zp R.D ℂ)
    (P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop)
    (Inv : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → Prop)
    (hP : ∀ i E σ, P i E σ → Inv i (MatrixMap.traceRight (spec.In i × R.D) E σ))
    (w c : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (h : ∀ μ i σ, σ.PosSemidef → Inv i σ → ok μ i →
      w i σ + ∑' r, ∑ j, potential (Kp (nx μ i r) j) ((R.step i).branch r σ) ≤
        ∑ j, potential (Kp μ j) σ + c i σ)
    {fin : (Σ u, Ω u) → Mode → Prop} {A : QReg} (x : QuantumComp L spec Ω A) (μ : Mode)
    (hx : ModedP ok nx fin μ x) {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef)
    (hq : R.ForallQueries I P x ρ) :
    R.totalWeight I w x ρ ≤ ∑ j, potential (Kp μ j) ρ + R.totalWeight I c x ρ := by
  classical
  have hw : R.totalWeight I w x ρ =
      R.totalWeight I (fun i σ ↦ if Inv i σ then w i σ else 0) x ρ :=
    totalWeight_congr_of_forallQueries R I (fun i E σ hσ ↦ by rw [ite_eq_left (hP i E σ hσ)]) x ρ hq
  have hc : R.totalWeight I c x ρ =
      R.totalWeight I (fun i σ ↦ if Inv i σ then c i σ else ⊤) x ρ :=
    totalWeight_congr_of_forallQueries R I (fun i E σ hσ ↦ by rw [ite_eq_left (hP i E σ hσ)]) x ρ hq
  rw [hw, hc]
  refine totalWeight_le_modedP R I Kp _ _ (fun μ i σ hσ hok ↦ ?_) x μ hx hρ
  by_cases hi : Inv i σ
  · simp only [ite_eq_left hi]
    exact h μ i σ hσ hi hok
  · simp only [ite_eq_right hi, zero_add, add_top]
    exact le_top

end modedP

/-! ## The modes of the randomizer searches -/

section modes

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- The modes of the randomizer searches: free; in the search of label `lab` from the base
`base`, before trial `j`; after that trial's `k`-read with outcome `a`; after its `k'`-read, with
the rate `xi` after `π` and the `h`-cell `z` next. -/
inductive CwMode
  | free
  | grd (lab : RLabel) (base : Randomizer) (j : ℕ)
  | afK (lab : RLabel) (base : Randomizer) (j : ℕ) (a : Z)
  | afK' (lab : RLabel) (base : Randomizer) (j : ℕ) (xi : X) (z : Z)

/-- A mode between trials. -/
def CwMode.Idle : CwMode → Prop
  | .free => True
  | .grd .. => True
  | _ => False

/-- The block of trial `j` of the search of label `lab` from base `base`. -/
noncomputable def cwBlk (P : PublicParameter) (lab : RLabel) (base : Randomizer) (j : ℕ) : X :=
  (blocks (thInput P (hashDomainFields (.message lab.layer lab.key))
    (lab.msg ++ littleEndianBytes 16 (base + BitVec.ofNat digestBits j)))).getD 0 0

/-- The label of a reveal of a single randomizer base (decided classically: the decidable
instance by enumeration of the labels is not to be evaluated). -/
noncomputable def cwRevLab (T : Finset HPos) : Option RLabel :=
  @dite _ (∃ lab : RLabel, T = {.inr lab}) (Classical.propDecidable _) (fun h ↦ some h.choose)
    fun _ ↦ none

theorem cwRevLab_eq_some {T : Finset HPos} {lab : RLabel} (h : T = {.inr lab}) :
    cwRevLab T = some lab := by
  unfold cwRevLab
  split_ifs with h'
  · exact congrArg some
      (Sum.inr_injective (Finset.singleton_injective (h'.choose_spec.symm.trans h)))
  · exact absurd ⟨lab, h⟩ h'

theorem cwRevLab_spec {T : Finset HPos} {lab : RLabel} (h : cwRevLab T = some lab) :
    T = {.inr lab} := by
  unfold cwRevLab at h
  split_ifs at h with h'
  obtain rfl := Option.some.inj h
  exact h'.choose_spec

/-- The mode after a reveal labelled `o`: the search of the label from the base `bse lab`, free
otherwise. -/
def cwOptNx (o : Option RLabel) (bse : RLabel → Randomizer) : CwMode :=
  match o with
  | some lab => .grd lab (bse lab) 0
  | none => .free

theorem cwOptNx_idle (o : Option RLabel) (bse : RLabel → Randomizer) : (cwOptNx o bse).Idle := by
  cases o
  · exact trivial
  · exact trivial

/-- The mode after a reveal of `T`: the search of its label for a single randomizer base. -/
noncomputable def cwRevNx (T : Finset HPos) (bse : RLabel → Randomizer) : CwMode :=
  cwOptNx (cwRevLab T) bse

theorem cwRevNx_idle (T : Finset HPos) (bse : RLabel → Randomizer) : (cwRevNx T bse).Idle :=
  cwOptNx_idle _ bse

theorem cwRevNx_lab (lab : RLabel) (bse : RLabel → Randomizer) :
    cwRevNx {.inr lab} bse = .grd lab (bse lab) 0 := by
  unfold cwRevNx
  rw [cwRevLab_eq_some (T := {.inr lab}) (lab := lab) rfl]
  rfl

theorem cwOptNx_congr {o : Option RLabel} {bse bse' : RLabel → Randomizer}
    (h : ∀ lab, o = some lab → bse lab = bse' lab) : cwOptNx o bse = cwOptNx o bse' := by
  cases o with
  | none => rfl
  | some lab => exact congrArg (fun b ↦ CwMode.grd lab b 0) (h lab rfl)

theorem cwRevNx_congr {T : Finset HPos} {bse bse' : RLabel → Randomizer}
    (h : ∀ lab, cwRevLab T = some lab → bse lab = bse' lab) : cwRevNx T bse = cwRevNx T bse' :=
  cwOptNx_congr h

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter)

/-- The reads a mode allows: in a search before trial `j`, the `k`-read at the trial's block
keeping the memory; after it with outcome `a`, the `k'`-read at `π (x, a)` keeping the memory;
then the `h`-read at `z` with the trial's update `hu lab x xi`. -/
noncomputable def cwRdOk {M' : Type} (hu : RLabel → X → X → M' → Option X → M') :
    CwMode → HwRead X Z M' → Prop
  | .grd lab base j, .readK x u =>
      j < randomizerAttemptLimit ∧ x = cwBlk P lab base j ∧ u = fun m _ ↦ m
  | .afK lab base j a, .readK' y u => y = (π (cwBlk P lab base j, a)).1 ∧ u = fun m _ ↦ m
  | .afK' lab base j xi z, .readH z' u => z' = z ∧ u = hu lab (cwBlk P lab base j) xi
  | _, _ => False

/-- The mode after a read. -/
noncomputable def cwRdNx {M' : Type} : CwMode → (c : HwRead X Z M') → c.Result → CwMode
  | .grd lab base j, .readK _ _, r => .afK lab base j (r.1.getD 0)
  | .afK lab base j a, .readK' _ _, r => .afK' lab base j (π (cwBlk P lab base j, a)).1
      ((π (cwBlk P lab base j, a)).2 + r.1.getD 0)
  | .afK' lab base j _ _, .readH _ _, _ => .grd lab base (j + 1)
  | _, _, _ => .free

/-- The calls the modes allow, on runtime 1's ports. -/
noncomputable def cwOkR {M : Type} (hu : RLabel → X → X → M → Option X → M) :
    CwMode → (hwReadSpec X Z M).Port → Prop
  | μ, .inl _ => μ.Idle
  | μ, .inr c => cwRdOk π P hu μ c

/-- The mode after a call of runtime 1. -/
noncomputable def cwNxR {M : Type} : CwMode → (i : (hwReadSpec X Z M).Port) → (hwReadSpec X Z M).Result i →
    CwMode
  | _, .inl _, _ => .free
  | μ, .inr c, r => cwRdNx π P μ c r

/-- The calls the modes allow, on the template's ports. -/
noncomputable def cwOkT {M : Type} (hu : RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M) :
    CwMode → (XSpec M).Port → Prop
  | μ, .inl (.inl (.inr c)) => cwRdOk π P hu μ c.1
  | μ, _ => μ.Idle

/-- The mode after a call of the template: a reveal of a single randomizer base starts its
search. -/
noncomputable def cwNxT {M : Type} : CwMode → (i : (XSpec M).Port) → (XSpec M).Result i → CwMode
  | μ, .inl (.inl (.inr c)), r => cwRdNx π P μ c.1 r
  | _, .inr T, r => cwRevNx T fun lab ↦ extendBase r.1 lab
  | _, _, _ => .free

/-- The calls the modes allow, on runtime 2's ports with record ports. -/
noncomputable def cwOkZ {M : Type} (hu : RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M) :
    CwMode → (recHwSpec X Z HPos M).Port → Prop
  | μ, .inl (.inl (.inr c)) => cwRdOk π P hu μ c
  | μ, _ => μ.Idle

/-- The mode after a call of runtime 2 with record ports, at the hidden values `v`. -/
noncomputable def cwNxZ {M : Type} (v : HPos → Digest) :
    CwMode → (i : (recHwSpec X Z HPos M).Port) → (recHwSpec X Z HPos M).Result i → CwMode
  | μ, .inl (.inl (.inr c)), r => cwRdNx π P μ c r
  | _, .inr T, _ => cwRevNx T fun lab ↦ v (.inr lab)
  | _, _, _ => .free

/-- The update of a trial's `h`-read on the template's memory. -/
def cwLiftHu {M : Type} (hu : RLabel → X → X → M → Option X → M) :
    RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M :=
  fun lab b xi m o ↦ (m.1, hu lab b xi m.2 o)

variable {M : Type} [Fintype M] [DecidableEq M]

/-! ### Runtime 1's searches -/

variable {π P}

omit [Fintype M] [DecidableEq M] in
theorem modedP_readCall {hu : RLabel → X → X → M → Option X → M} {μ : CwMode}
    {c : HwRead X Z M} (h : cwRdOk π P hu μ c) (B : QReg) :
    ModedP (L := LocalSig.instruments) (cwOkR π P hu) (cwNxR π P)
      (fun p μ' ↦ μ' = cwRdNx π P μ c p.2.2) μ (readCall c B) :=
  ⟨h, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩

variable (π P) in
/-- A stateful program of runtime 1 that is moded from every state. -/
def CSMod (hu : RLabel → X → X → M → Option X → M) {B : QReg} {σ α : Type} (μ : CwMode)
    (F : α → CwMode → Prop) (x : StateT σ (QComp (hwReadSpec X Z M) B B) α) : Prop :=
  ∀ s, ModedP (L := LocalSig.instruments) (cwOkR π P hu) (cwNxR π P)
    (fun p μ' ↦ F p.2.2.1 μ') μ (x.run s)

section smod

variable {hu : RLabel → X → X → M → Option X → M} {B : QReg} {σ α β : Type}

omit [Fintype M] [DecidableEq M] in
theorem cSMod_bind {x : StateT σ (QComp (hwReadSpec X Z M) B B) α}
    {k : α → StateT σ (QComp (hwReadSpec X Z M) B B) β} {μ : CwMode} {F : α → CwMode → Prop}
    {G : β → CwMode → Prop} (hx : CSMod π P hu μ F x)
    (hk : ∀ a μ', F a μ' → CSMod π P hu μ' G (k a)) : CSMod π P hu μ G (x >>= k) := by
  intro s
  rw [StateT.run_bind]
  exact modedP₂_bind (F := fun (q : α × σ) μ ↦ F q.1 μ) (F' := fun (q : β × σ) μ ↦ G q.1 μ) _ _
    (hx s)
    fun p μ' h ↦ hk p.1 μ' h p.2

omit [Fintype M] [DecidableEq M] in
theorem cSMod_pure (a : α) {F : α → CwMode → Prop} {μ : CwMode} (h : F a μ) :
    CSMod π P hu μ F (pure a : StateT σ (QComp (hwReadSpec X Z M) B B) α) := by
  intro s
  rw [StateT.run_pure]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem cSMod_map {x : StateT σ (QComp (hwReadSpec X Z M) B B) α} (g : α → β) {μ : CwMode}
    {F : β → CwMode → Prop} (hx : CSMod π P hu μ (fun a ↦ F (g a)) x) :
    CSMod π P hu μ F (g <$> x) := by
  intro s
  rw [StateT.run_map]
  exact modedP_map (F := fun q : β × σ ↦ F q.1) (fun p : α × σ ↦ (g p.1, p.2)) (hx s)

omit [Fintype M] [DecidableEq M] in
theorem cSMod_rdK {lab : RLabel} {base : Randomizer} {j : ℕ} {x : X}
    (hj : j < randomizerAttemptLimit) (hx : x = cwBlk P lab base j) :
    CSMod π P hu (.grd lab base j) (fun a (μ : CwMode) ↦ μ = .afK lab base j a) (rdK (M := M) B x) :=
  fun s ↦ modedP₂_bind (F := fun r : Option Z × M ↦ fun (μ : CwMode) ↦ μ = .afK lab base j (r.1.getD 0))
    (F' := fun q : Z × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦ μ = .afK lab base j q.1)
    (readCall (.readK x keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k x (r.1.getD 0)]))
    (modedP_readCall (μ := .grd lab base j) (c := .readK x keepMem) ⟨hj, hx, rfl⟩ B)
    fun _ _ h ↦ h

omit [Fintype M] [DecidableEq M] in
theorem cSMod_rdK' {lab : RLabel} {base : Randomizer} {j : ℕ} {a : Z} {y : X}
    (hy : y = (π (cwBlk P lab base j, a)).1) :
    CSMod π P hu (.afK lab base j a) (fun c (μ : CwMode) ↦ μ = .afK' lab base j (π (cwBlk P lab base j, a)).1
      ((π (cwBlk P lab base j, a)).2 + c)) (rdK' (M := M) B y) :=
  fun s ↦ modedP₂_bind (F := fun r : Option Z × M ↦ fun (μ : CwMode) ↦ μ = .afK' lab base j
      (π (cwBlk P lab base j, a)).1 ((π (cwBlk P lab base j, a)).2 + r.1.getD 0))
    (F' := fun q : Z × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦ μ = .afK' lab base j
      (π (cwBlk P lab base j, a)).1 ((π (cwBlk P lab base j, a)).2 + q.1))
    (readCall (.readK' y keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k' y (r.1.getD 0)]))
    (modedP_readCall (μ := .afK lab base j a) (c := .readK' y keepMem) ⟨hy, rfl⟩ B)
    fun _ _ h ↦ h

omit [Fintype M] [DecidableEq M] in
theorem cSMod_rdHU {lab : RLabel} {base : Randomizer} {j : ℕ} {xi : X} {z z' : Z}
    {u : M → Option X → M} (hz : z' = z) (hu' : u = hu lab (cwBlk P lab base j) xi) :
    CSMod π P hu (.afK' lab base j xi z) (fun _ (μ : CwMode) ↦ μ = .grd lab base (j + 1)) (rdHU M B z' u) :=
  fun s ↦ modedP₂_bind (F := fun _ : Option X × M ↦ fun (μ : CwMode) ↦ μ = .grd lab base (j + 1))
    (F' := fun _ : X × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦ μ = .grd lab base (j + 1))
    (readCall (.readH z' u) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.h z' (r.1.getD 0)]))
    (modedP_readCall (μ := .afK' lab base j xi z) (c := .readH z' u) ⟨hz, hu'⟩ B)
    fun _ _ h ↦ h

end smod

/-- The updates of the trials' `h`-reads of runtime 1, by label. -/
def cwHu1 (upd : TrialUpd M) : RLabel → X → X → M → Option X → M :=
  fun lab b xi ↦ upd lab.layer lab.key b xi

omit [Fintype M] [DecidableEq M] in
/-- **A trial's round of reads.** -/
theorem cSMod_rdRoundU (upd : TrialUpd M) {B : QReg} {lab : RLabel} {base : Randomizer} {j : ℕ}
    (hj : j < randomizerAttemptLimit) {b : X} (hb : b = cwBlk P lab base j) :
    CSMod π P (cwHu1 upd) (.grd lab base j) (fun _ (μ : CwMode) ↦ μ = .grd lab base (j + 1))
      (rdRoundU M (upd lab.layer lab.key) π B (0, 0) b) := by
  unfold rdRoundU
  refine cSMod_bind (cSMod_rdK hj (by simp [hb])) fun a μ ha ↦ ?_
  subst ha
  refine cSMod_bind (cSMod_rdK' (a := a) (by simp [hb])) fun c μ hc ↦ ?_
  subst hc
  refine cSMod_bind (cSMod_rdHU (by simp [hb]) (by simp [cwHu1, hb])) fun w μ hw ↦ ?_
  exact cSMod_pure _ hw

omit [Fintype M] [DecidableEq M] in
/-- **A trial's hash** of a one-block input whose block is the trial's. -/
theorem modedP_hashTrial (upd : TrialUpd M) {B : QReg} {lab : RLabel} {base : Randomizer}
    {j : ℕ} (hj : j < randomizerAttemptLimit) (input : HashInput)
    (hb : blocks input = [cwBlk P lab base j]) :
    ModedP (L := LocalSig.instruments) (cwOkR π P (cwHu1 upd)) (cwNxR π P)
      (fun _ (μ : CwMode) ↦ μ = .grd lab base (j + 1)) (.grd lab base j)
      (hashTrial M (upd lab.layer lab.key) π B input) := by
  have hfold : CSMod π P (cwHu1 upd) (B := B) (.grd lab base j)
      (fun _ (μ : CwMode) ↦ μ = .grd lab base (j + 1))
      ((blocks input).foldlM (rdRoundU M (upd lab.layer lab.key) π B) (0, 0)) := by
    rw [hb]
    exact cSMod_bind (cSMod_rdRoundU upd hj rfl) fun s' μ h ↦ cSMod_pure s' h
  exact modedP_map (F := fun _ (μ : CwMode) ↦ μ = .grd lab base (j + 1)) Prod.fst
    (cSMod_map (F := fun _ (μ : CwMode) ↦ μ = .grd lab base (j + 1)) (out256 : X → HashOutput)
      (cSMod_map (F := fun _ (μ : CwMode) ↦ μ = .grd lab base (j + 1)) (fun s : X × Z ↦ s.1) hfold) [])

omit [Fintype M] [DecidableEq M] in
/-- **The randomizer search** of a label from its base, from its trial `trial`, ends between
trials. -/
theorem modedP_grindR (upd : TrialUpd M) (pub : Pub) {B : QReg} (lab : RLabel)
    (base : Randomizer) :
    ∀ n trial, trial + n ≤ randomizerAttemptLimit →
      ModedP (L := LocalSig.instruments) (cwOkR pub.perm pub.param (cwHu1 upd))
      (cwNxR pub.perm pub.param) (fun _ (μ : CwMode) ↦ μ.Idle) (.grd lab base trial)
      (grindR M upd pub B lab.layer lab.key lab.msg base n trial)
  | 0, _, _ => trivial
  | n + 1, trial, hn => by
    rw [grindR]
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (length_blocks_trial pub.param
      (hashDomainFields (.message lab.layer lab.key)) (RLabel.length_msg_le lab) base trial)
    have hbk : cwBlk pub.param lab base trial = b := by simp [cwBlk, hb]
    refine modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ = .grd lab base (trial + 1))
      (F' := fun _ (μ : CwMode) ↦ μ.Idle) _ _
      (modedP_hashTrial upd (by omega) _ (hb.trans (by rw [hbk]))) fun out μ hμ ↦ ?_
    subst hμ
    show ModedP _ _ _ _ (match Codeword.decode (truncateHash out) with
      | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
      | none => grindR M upd pub B lab.layer lab.key lab.msg base n (trial + 1))
    split
    · trivial
    · exact modedP_grindR upd pub lab base n (trial + 1) (by omega)

/-! ### Lifting the modes to the template and to runtime 2 -/

omit [Fintype M] [DecidableEq M] in
theorem cwRdOk_liftRead {hu : RLabel → X → X → M → Option X → M} {μ : CwMode}
    {c : HwRead X Z M} (h : cwRdOk π P hu μ c) :
    cwRdOk π P (cwLiftHu hu) μ (liftRead (S := HPos) c) := by
  rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z⟩ <;>
    rcases c with ⟨z', u⟩ | ⟨x', u⟩ | ⟨y, u⟩
  all_goals first
    | exact h
    | exact ⟨h.1, by rw [h.2]; try rfl⟩
    | exact ⟨h.1, h.2.1, by rw [h.2.2]⟩

omit [Fintype M] [DecidableEq M] in
/-- **Lifting runtime 1's moded programs to templates.** -/
theorem modedP_readLift {hu : RLabel → X → X → M → Option X → M} {Ω : QReg → Type} {A : QReg}
    {fin : (Σ u, Ω u) → CwMode → Prop}
    (y : QuantumComp LocalSig.instruments (hwReadSpec X Z M) Ω A) {μ : CwMode}
    (hy : ModedP (cwOkR π P hu) (cwNxR π P) fin μ y) :
    ModedP (cwOkT π P (cwLiftHu hu)) (cwNxT π P) fin μ (readLift goodAll y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨cwRdOk_liftRead hy.1, fun b ↦ ?_⟩
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;>
        rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z'⟩ <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

omit [Fintype M] [DecidableEq M] in
/-- A sponge program of runtime 1 is moded between trials. -/
theorem modedP_liftOrdinary {hu : RLabel → X → X → M → Option X → M} {Ω : QReg → Type}
    {A : QReg} (y : QuantumComp LocalSig.instruments (spongeSpec X Z) Ω A) :
    ∀ μ : CwMode, μ.Idle → ModedP (cwOkR π P hu) (cwNxR π P) (fun _ (μ : CwMode) ↦ μ.Idle) μ
      (y.liftOrdinary (t := hwReadCmdSpec X Z M)) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => exact fun _ h ↦ h
  | liftBind _ c next ih =>
    intro μ hμ
    show ModedP _ _ _ _ (IFreeM.mapLens QuantumComp.ordinaryLens (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ μ hμ⟩
    · exact ⟨hμ, fun b ↦ ih _ .free trivial⟩

omit [Fintype M] [DecidableEq M] in
theorem cwNxZ_rec_eq (v : HPos → Digest) (μ : CwMode) (T : Finset HPos)
    (m : Finset HPos × M) :
    cwNxZ (M := M) π P v μ (.inr T) m = cwNxT π P μ (.inr T) (restrictTo T v, m) :=
  cwRevNx_congr fun lab hl ↦ (extendBase_restrictTo
    (by rw [cwRevLab_spec hl]; exact Finset.mem_singleton_self _) v).symm

omit [Fintype M] [DecidableEq M] in
/-- **Realizing keeps the modes.** -/
theorem modedP_realizeT {hu : RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M}
    (v : HPos → Digest) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → CwMode → Prop} (y : QuantumComp L (XSpec M) Ω A)
    {μ : CwMode} (hy : ModedP (cwOkT π P hu) (cwNxT π P) fin μ y) :
    ModedP (cwOkZ π P hu) (cwNxZ π P v) fin μ (realizeT v y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (tmplLens v) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · cases p <;> exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨hy.1, fun b ↦ ?_⟩
      have h := ih _ (hy.2 (ULift.up (restrictTo T v, b.down)))
      exact (congrArg (fun μ' ↦ ModedP (cwOkZ π P hu) (cwNxZ π P v) fin μ' _)
        (cwNxZ_rec_eq (π := π) (P := P) v μ T b.down)).mpr h

/-! ### The challenge prefix is moded -/

section trialPrefix

variable (π P) in
/-- A template moded between trials: from every mode between trials, it ends between trials. -/
def CIdle (hu : RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M)
    {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments (XSpec M) Ω A) : Prop :=
  ∀ μ : CwMode, μ.Idle → ModedP (cwOkT π P hu) (cwNxT π P) (fun _ (μ : CwMode) ↦ μ.Idle) μ y

variable {hu : RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M}

omit [Fintype M] [DecidableEq M] in
theorem cIdle_bind {A B B' : QReg} {α β : Type} (x : QComp (XSpec M) A B α)
    (g : α → QComp (XSpec M) B B' β) (hx : CIdle π P hu x) (hg : ∀ a, CIdle π P hu (g a)) :
    CIdle π P hu (x.bind g) :=
  fun μ hμ ↦ modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Idle) (F' := fun _ (μ : CwMode) ↦ μ.Idle) x g (hx μ hμ)
    fun a μ' h ↦ hg a μ' h

omit [Fintype M] [DecidableEq M] in
theorem cIdle_pure {A : QReg} {α : Type} (a : α) :
    CIdle π P hu (QuantumComp₂.pure (L := LocalSig.instruments) (spec := XSpec M) (A := A) a) :=
  fun _ h ↦ h

omit [Fintype M] [DecidableEq M] in
theorem cIdle_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    CIdle π P hu (QComp.act (spec := XSpec M) p) :=
  fun _ hμ ↦ ⟨trivial, fun _ ↦ hμ⟩

omit [Fintype M] [DecidableEq M] in
theorem cwNxT_rec_idle (μ : CwMode) (T : Finset HPos)
    (r : (XSpec M).Result (.inr T)) : (cwNxT π P μ (.inr T) r).Idle :=
  cwRevNx_idle T _

omit [Fintype M] [DecidableEq M] in
theorem cIdle_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B B' α)
    (hk : ∀ r, CIdle π P hu (k r)) : CIdle π P hu (revealThen goodAll T k) :=
  fun μ hμ ↦ ⟨hμ, fun b ↦ cIdle_bind _ _ (cIdle_act _) (fun _ ↦ hk b.down) _
    (cwNxT_rec_idle (π := π) (P := P) μ T b.down)⟩

omit [Fintype M] [DecidableEq M] in
/-- The reveal of a label's randomizer base starts its search. -/
theorem cIdle_revealLab {B B' : QReg} {α : Type} (lab : RLabel)
    (k : RevealVals XD {.inr lab} × (Finset HPos × M) → QComp (XSpec M) B B' α)
    (hk : ∀ r, ModedP (cwOkT π P hu) (cwNxT π P) (fun _ (μ : CwMode) ↦ μ.Idle)
      (.grd lab (extendBase r.1 lab) 0) (k r)) :
    CIdle π P hu (revealThen goodAll {.inr lab} k) := by
  intro μ hμ
  refine ⟨hμ, fun b ↦ ?_⟩
  have he : cwNxT (M := M) π P μ (.inr {.inr lab}) b.down =
      .grd lab (extendBase b.down.1 lab) 0 :=
    cwRevNx_lab lab _
  rw [show modeCmdNx (cwNxT (M := M) π P) (QuantumComp.Cmd.query (L := LocalSig.instruments)
    (.inr {.inr lab}) B _) μ b = cwNxT (M := M) π P μ (.inr {.inr lab}) b.down from rfl, he]
  exact modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ = .grd lab (extendBase b.down.1 lab) 0)
    (F' := fun _ (μ : CwMode) ↦ μ.Idle) _ _ ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ h ▸ hk b.down

omit [Fintype M] [DecidableEq M] in
theorem cIdle_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (XSpec M) B B' α) (hk : CIdle π P hu k) : CIdle π P hu (progThen p hp k) :=
  fun _ hμ ↦ ⟨hμ, fun _ ↦ cIdle_bind _ _ (cIdle_act _) (fun _ ↦ hk) _ trivial⟩

omit [Fintype M] [DecidableEq M] in
theorem cIdle_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    CIdle π P hu (progPorts M B ps) := by
  induction ps with
  | nil => exact cIdle_pure _
  | cons p ps ih => exact cIdle_progThen p trivial _ ih

omit [Fintype M] [DecidableEq M] in
theorem cIdle_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    CIdle π P hu (progSlots M pub B ss) := by
  induction ss with
  | nil => exact cIdle_pure _
  | cons s ss ih => exact cIdle_bind _ _ (cIdle_progPorts B _) fun _ ↦ ih

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
theorem cIdle_signLayerT (pub : Pub) (B : QReg) (lab : RLabel) :
    CIdle pub.perm pub.param (cwLiftHu (cwHu1 upd)) (signLayerT M upd pub B lab) := by
  refine cIdle_revealLab lab _ fun r₀ ↦ ?_
  refine modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Idle) (F' := fun _ (μ : CwMode) ↦ μ.Idle) _ _
    (modedP_readLift _ (modedP_grindR upd pub lab _ _ _ (by omega))) fun g μ hμ ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · exact hμ
  · exact cIdle_revealThen _ _ (fun r ↦ cIdle_bind _ _ (cIdle_progSlots pub B _)
      fun _ ↦ cIdle_pure _) μ hμ

omit [Fintype M] [DecidableEq M] in
theorem cIdle_signT (pub : Pub) (B : QReg) (r : SigningRequest) :
    CIdle pub.perm pub.param (cwLiftHu (cwHu1 upd)) (signT M upd pub B r) := by
  refine cIdle_bind _ _ (cIdle_signLayerT upd pub B _) fun b ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · exact cIdle_pure _
  · refine cIdle_bind _ _ (cIdle_signLayerT upd pub B _) fun t ↦ ?_
    rcases t with _ | ⟨top, _⟩ <;> exact cIdle_pure _

omit [Fintype M] [DecidableEq M] in
theorem cIdle_challengeT (pub : Pub) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    ∀ μ : CwMode, μ.Idle → ModedP (cwOkT pub.perm pub.param (cwLiftHu (cwHu1 upd)))
      (cwNxT pub.perm pub.param) (fun _ (μ : CwMode) ↦ μ.Idle) μ (challengeT M upd pub A c) := by
  intro μ hμ
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact modedP_readLift _ (modedP_liftOrdinary _ μ hμ)
  · exact modedP_readLift _ (modedP_liftOrdinary _ μ hμ)
  · exact modedP_bind _ _ (cIdle_bind _ _ (cIdle_act _) (fun _ ↦ cIdle_signT upd pub _ r) μ hμ)
      fun _ _ μ' h ↦ h

omit [Fintype M] [DecidableEq M] in
theorem modedP_cast {spec : QuantumOracleSpec.{0, 0}} {ok : CwMode → spec.Port → Prop}
    {nx : CwMode → (i : spec.Port) → spec.Result i → CwMode} {Ω : QReg → Type w}
    {fin : (Σ u, Ω u) → CwMode → Prop} {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) (μ : CwMode) :
    ModedP ok nx fin μ (e ▸ y) ↔ ModedP ok nx fin μ y := by
  subst e
  rfl

omit [Fintype M] [DecidableEq M] in
/-- Substituting trees moded between trials. -/
theorem modedP_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (XSpec M)))
    (hσ : ∀ A c, ∀ μ : CwMode, μ.Idle → ModedP (cwOkT π P hu) (cwNxT π P)
      (fun _ (μ : CwMode) ↦ μ.Idle) μ (σ A c)) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ∀ μ : CwMode, μ.Idle → ModedP (cwOkT π P hu) (cwNxT π P) (fun _ (μ : CwMode) ↦ μ.Idle) μ
      (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact fun _ h ↦ h
  | liftBind s c next ih =>
    intro μ hμ
    rw [IFreeM.substitute_liftBind]
    exact modedP_bind _ _ (hσ s c μ hμ) fun u ans μ' h ↦ (modedP_cast ans.2 _ _).mpr
      (ih ans.1 μ' h)

omit [Fintype M] [DecidableEq M] in
/-- **The challenge prefix is moded**: its reads are the searches' trials. -/
theorem cIdle_prefixT (pub : Pub) (A : Adversary (X × Z)) :
    CIdle pub.perm pub.param (cwLiftHu (cwHu1 upd)) (prefixT M upd pub A) :=
  cIdle_revealThen _ _ fun _ ↦ cIdle_bind _ _
    (modedP_substitute _ (cIdle_challengeT upd pub) _) fun _ ↦ cIdle_pure _

omit [Fintype M] [DecidableEq M] in
/-- **The realized challenge prefix is moded**, from the free mode. -/
theorem modedP_prefixR (pub : Pub) (A : Adversary (X × Z)) (v : HPos → Digest) :
    ModedP (cwOkZ pub.perm pub.param (cwLiftHu (cwHu1 upd))) (cwNxZ pub.perm pub.param v)
      (fun _ (μ : CwMode) ↦ μ.Idle) .free (realizeT v (prefixT M upd pub A)) :=
  modedP_realizeT v _ (cIdle_prefixT upd pub A .free trivial)

end trialPrefix

end modes

/-! ## Potentials of projectors along Kraus families -/

section potKraus

variable {D : Type} [Fintype D] [DecidableEq D]

/-- The potential of a projector on basis states is the weighted diagonal of its indicator. -/
theorem cw_potential_setProj_eq_dW (S : Set D) (τ : Matrix (Unit × D) (Unit × D) ℂ) :
    potential (setProj S) τ = ENNReal.ofReal (dW (fun t ↦ (S.indicator 1 t.2 : ℝ)) τ) := by
  rw [potential_eq, conjTranspose_setProj, setProj_mul_self, cw_kron_setProj_eq, dW_eq_trace]

/-- **A projector's potential along a Kraus family that scales it**. -/
theorem cw_sum_pot_setProj_le {ι : Type} [Fintype ι]
    (K : ι → Matrix (Unit × D) (Unit × D) ℂ) (hK : ∑ r, (K r)ᴴ * K r = 1) (S S' : Set D)
    (c : ι → ℝ) (hc1 : ∀ r, c r ≤ 1)
    (h1 : ∀ r s' a, K r s' a ≠ 0 → (S'.indicator 1 s'.2 : ℝ) = c r * S.indicator 1 a.2)
    (h2 : ∀ r s' a b, K r s' a ≠ 0 → K r s' b ≠ 0 →
      (S.indicator 1 a.2 : ℝ) = S.indicator 1 b.2)
    {σ : Matrix (Unit × D) (Unit × D) ℂ} (hσ : σ.PosSemidef) :
    ∑ r, potential (setProj S') (MatrixMap.conj (K r) σ) ≤ potential (setProj S) σ := by
  simp only [cw_potential_setProj_eq_dW]
  have hf : ∀ t : Unit × D, (0 : ℝ) ≤ S.indicator 1 t.2 :=
    fun t ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hf' : ∀ t : Unit × D, (0 : ℝ) ≤ S'.indicator 1 t.2 :=
    fun t ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  rw [← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ dW_nonneg hf' (posSemidef_conj (K r) hσ)]
  exact ENNReal.ofReal_le_ofReal (sum_dW_conj_le_scale K hK _ _ hf c hc1 h1 h2 hσ)

/-- A projector kept by a Kraus family. -/
theorem cw_sum_pot_setProj_keep {ι : Type} [Fintype ι]
    (K : ι → Matrix (Unit × D) (Unit × D) ℂ) (hK : ∑ r, (K r)ᴴ * K r = 1) (S : Set D)
    (h : ∀ r s' a, K r s' a ≠ 0 → (s'.2 ∈ S ↔ a.2 ∈ S))
    {σ : Matrix (Unit × D) (Unit × D) ℂ} (hσ : σ.PosSemidef) :
    ∑ r, potential (setProj S) (MatrixMap.conj (K r) σ) ≤ potential (setProj S) σ := by
  have hind : ∀ r s' a, K r s' a ≠ 0 → (S.indicator 1 s'.2 : ℝ) = S.indicator 1 a.2 :=
    fun r s' a hK ↦ by
      by_cases ha : a.2 ∈ S
      · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ((h r s' a hK).2 ha), Pi.one_apply,
          Pi.one_apply]
      · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem (mt (h r s' a hK).1 ha)]
  exact cw_sum_pot_setProj_le K hK S S (fun _ ↦ 1) (fun _ ↦ le_rfl)
    (fun r s' a hK ↦ by rw [one_mul]; exact hind r s' a hK)
    (fun r s' a b ha hb ↦ (hind r s' a ha).symm.trans (hind r s' b hb)) hσ

end potKraus

/-! ## Entries of the read and record operators -/

section entries

variable {X₁ Z₁ M : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [DecidableEq M]

theorem cw_clsKraus_ne_zero {T B : Type} [DecidableEq B] {p : B → Prop} [DecidablePred p] {φ : B → B}
    {R : B → Matrix T T ℂ} {s s' : T × B} (h : clsKraus p φ R s' s ≠ 0) :
    p s.2 ∧ s'.2 = φ s.2 ∧ R s.2 s'.1 s.1 ≠ 0 := by
  rw [clsKraus_apply] at h
  split_ifs at h with hc
  · exact ⟨hc.1, hc.2, h⟩
  · exact absurd rfl h

/-- A nonzero entry of a read of the cell `x` of `k`: the other cells, the other databases and the
hardwired cells kept, the memory updated by the outcome. -/
theorem cw_readKrausK_ne_zero (x : X₁) (upd : M → Option Z₁ → M) (r : Option Z₁ × M)
    {s' s : HwReg X₁ Z₁ M} (h : readKrausK x upd r s' s ≠ 0) :
    s'.1.1 = s.1.1 ∧ s'.1.2.2 = s.1.2.2 ∧ (∀ b, b ≠ x → s'.1.2.1 b = s.1.2.1 b) ∧
      s'.2.1 = s.2.1 ∧ s.2.2 = r.2 ∧ s'.2.2 = upd r.2 r.1 := by
  obtain ⟨hp, hφ, hR⟩ := cw_clsKraus_ne_zero h
  rw [kroneckerMap_apply, kroneckerMap_apply] at hR
  have h₁ := left_ne_zero_of_mul hR
  have h₂ := right_ne_zero_of_mul hR
  have h₃ := left_ne_zero_of_mul h₂
  have h₄ := right_ne_zero_of_mul h₂
  refine ⟨?_, ?_, cellRead_apply_ne_zero h₃, by rw [hφ], hp, ?_⟩
  · by_contra hne
    exact h₁ (Matrix.one_apply_ne hne)
  · by_contra hne
    exact h₄ (Matrix.one_apply_ne hne)
  · rw [hφ]

/-- A nonzero entry of a read of the cell `x` of `k'`. -/
theorem cw_readKrausK'_ne_zero (x : X₁) (upd : M → Option Z₁ → M) (r : Option Z₁ × M)
    {s' s : HwReg X₁ Z₁ M} (h : readKrausK' x upd r s' s ≠ 0) :
    s'.1.1 = s.1.1 ∧ s'.1.2.1 = s.1.2.1 ∧ s'.2.1 = s.2.1 ∧ s.2.2 = r.2 ∧
      s'.2.2 = upd r.2 r.1 := by
  obtain ⟨hp, hφ, hR⟩ := cw_clsKraus_ne_zero h
  rw [kroneckerMap_apply, kroneckerMap_apply] at hR
  have h₁ := left_ne_zero_of_mul hR
  have h₂ := right_ne_zero_of_mul hR
  have h₃ := left_ne_zero_of_mul h₂
  refine ⟨?_, ?_, by rw [hφ], hp, ?_⟩
  · by_contra hne
    exact h₁ (Matrix.one_apply_ne hne)
  · by_contra hne
    exact h₃ (Matrix.one_apply_ne hne)
  · rw [hφ]

/-- A nonzero entry of a read of the cell `z` of `h`. -/
theorem cw_readKrausH_ne_zero (z : Z₁) (upd : M → Option X₁ → M) (r : Option X₁ × M)
    {s' s : HwReg X₁ Z₁ M} (h : readKrausH z upd r s' s ≠ 0) :
    s'.1.2 = s.1.2 ∧ s'.2.1 = s.2.1 ∧ s.2.2 = r.2 ∧ s'.2.2 = upd r.2 r.1 := by
  obtain ⟨hp, hφ, hR⟩ := cw_clsKraus_ne_zero h
  rw [kroneckerMap_apply] at hR
  have h₂ := right_ne_zero_of_mul hR
  refine ⟨?_, by rw [hφ], hp, ?_⟩
  · by_contra hne
    exact h₂ (Matrix.one_apply_ne hne)
  · rw [hφ]

end entries

/-! ## The codeword-recorded potentials of the searches -/

section main

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- The key of the label `lab` is unselected. -/
def cwU (lab : RLabel) (m : Mem) : Prop :=
  m.2 lab.layer lab.key = none

/-- The codeword-recorded predicate of the key of label `lab`: the `h`-cell not hardwired, the
key unselected, recorded with a value selecting it. -/
def cwHp (lab : RLabel) : HitPred X Z Mem :=
  fun xi z dh wm ↦ wm.1.1 z = none ∧ cwU lab wm.2 ∧
    ∃ v, dh z = some v ∧ Codeword.Valid (trunc128 (xi + v))

/-- A recorded `h`-cell that is not hardwired. -/
def anyHp : HitPred X Z Mem :=
  fun _ z dh wm ↦ wm.1.1 z = none ∧ ∃ v, dh z = some v

theorem cwHp_anyHp (lab : RLabel) (xi : X) (z : Z) (dh : Database Z X) (wm : Hw X Z × Mem)
    (h : cwHp lab xi z dh wm) : anyHp xi z dh wm := by
  obtain ⟨h1, -, v, h3, -⟩ := h
  exact ⟨h1, v, h3⟩

/-- **Trial `j` already started**: its block is recorded or hardwired, the key unselected. -/
def cwTD (P : PublicParameter) (lab : RLabel) (base : Randomizer) (j : ℕ) :
    Set (HwReg X Z Mem) :=
  {s | (s.1.2.1 (cwBlk P lab base j) ≠ none ∨ s.2.1.2.1 (cwBlk P lab base j) ≠ none) ∧
    cwU lab s.2.2}

/-- The trials' blocks are distinct. -/
theorem cwBlk_inj (P : PublicParameter) (lab : RLabel) (base : Randomizer) {i j : ℕ}
    (hi : i < randomizerAttemptLimit) (hj : j < randomizerAttemptLimit)
    (h : cwBlk P lab base i = cwBlk P lab base j) : i = j := by
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (length_blocks_trial P
    (hashDomainFields (.message lab.layer lab.key)) (RLabel.length_msg_le lab) base i)
  obtain ⟨b', hb'⟩ := List.length_eq_one_iff.mp (length_blocks_trial P
    (hashDomainFields (.message lab.layer lab.key)) (RLabel.length_msg_le lab) base j)
  have e1 : cwBlk P lab base i = b := by simp [cwBlk, hb]
  have e2 : cwBlk P lab base j = b' := by simp [cwBlk, hb']
  have hbb : b = b' := e1.symm.trans (h.trans e2)
  have hin := (thInput_injective P (blocks_injective (hb.trans (hbb ▸ hb'.symm)))).2
  have hr := littleEndianBytes_injective 16 (List.append_cancel_left hin)
  have hn := congrArg BitVec.toNat (add_left_cancel hr)
  simp only [BitVec.toNat_ofNat, digestBits] at hn
  have h32 : randomizerAttemptLimit < 2 ^ 128 := by unfold randomizerAttemptLimit; norm_num
  rwa [Nat.mod_eq_of_lt (hi.trans h32), Nat.mod_eq_of_lt (hj.trans h32)] at hn

/-- The index of the potentials: a `k'`-read's outcome, or a trial with four copies. -/
abbrev CwJ : Type := Option (Option Z × Mem) ⊕ (Fin randomizerAttemptLimit × Fin 4)

/-- **The potentials of the search modes**: after a trial's `k`-read, the codeword-recorded `h`-cell
through each outcome of its `k'`-read; after its `k'`-read, the codeword-recorded `h`-cell; in a
search, four times each later trial already started. -/
noncomputable def cwKp (π : Equiv.Perm (X × Z)) (P : PublicParameter) :
    CwMode → CwJ → Matrix (HwReg X Z Mem) (HwReg X Z Mem) ℂ
  | .afK lab base j a, .inl (some r) =>
      setProj (cwHit (cwHp lab) (π (cwBlk P lab base j, a)).1
        ((π (cwBlk P lab base j, a)).2 + r.1.getD 0)) *
        readKrausK' (π (cwBlk P lab base j, a)).1 (fun m _ ↦ m) r
  | .afK' lab _ _ xi z, .inl none => setProj (cwHit (cwHp lab) xi z)
  | .grd lab base j, .inr i => if j ≤ i.1.val then setProj (cwTD P lab base i.1) else 0
  | .afK lab base j _, .inr i => if j < i.1.val then setProj (cwTD P lab base i.1) else 0
  | .afK' lab base j _ _, .inr i => if j < i.1.val then setProj (cwTD P lab base i.1) else 0
  | _, _ => 0

/-- The charge of a reveal labelled `o`: four times each trial already started. -/
noncomputable def cwRevCharge (P : PublicParameter) (o : Option RLabel)
    (bse : RLabel → Randomizer)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  match o with
  | some lab => ∑ i : Fin randomizerAttemptLimit × Fin 4,
      diagMass {q : Unit × HwReg X Z Mem | q.2 ∈ cwTD P lab (bse lab) i.1} σ
  | none => 0

/-- **The charges**: at a `k`-read, its fresh part; at a reveal of a label's randomizer base, four
times each trial already started. -/
noncomputable def cwCharge (π : Equiv.Perm (X × Z)) (P : PublicParameter) (v : HPos → Digest) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
        ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ → ℝ≥0∞
  | .inl (.inl (.inr (.readK x _))), σ => ENNReal.ofReal (∑ s, cwFresh anyHp π x s * (σ s s).re)
  | .inr T, σ => cwRevCharge P (cwRevLab T) (fun lab ↦ v (.inr lab)) σ
  | _, _ => 0

/-- The no-`⊥` invariant at a call, in the decompressed basis. -/
def CwInv (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ) : Prop :=
  QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × HwReg X Z Mem ↦ m.2)
    {s | NoBot s} (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
      ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z Mem) σ)

/-! ### Facts per port -/

theorem cwU_of_upd (lab : RLabel) (x xi : X) (m : Mem) (o : Option X)
    (h : cwU lab (cwLiftHu (cwHu1 cwUpd) lab x xi m o)) : cwU lab m := by
  unfold cwU at h ⊢
  by_contra hm
  rcases o with _ | v
  · exact hm h
  · have he : cwUpd lab.layer lab.key x xi m.2 (some v) = m.2 := ite_eq_right hm
    exact hm (he ▸ h)

/-- **The codeword-recorded states are those whose recorded value moves the memory.** -/
theorem cwRec_iff (z : Z) (t : TrialPt) (s : HwReg X Z Mem) :
    CwRec z t s ↔ s.2.1.1 z = none ∧ ∃ v, s.1.1 z = some v ∧ trialUpd t s.2.2 (some v) ≠ s.2.2 := by
  constructor
  · rintro ⟨h1, h2, v, h3, h4⟩
    refine ⟨h1, v, h3, fun he ↦ ?_⟩
    have hs : cwUpd t.l t.e t.x t.xi s.2.2.2 (some v) = s.2.2.2 := congrArg Prod.snd he
    rw [cwUpd_some_of_none _ _ _ _ h2] at hs
    have hn := (cwSel_eq_none_iff h2 t.x t.xi v).not.mpr (not_not.mpr h4)
    exact hn (by rw [hs]; exact h2)
  · rintro ⟨h1, v, h3, h4⟩
    have h2 : s.2.2.2 t.l t.e = none := by
      by_contra hm
      exact h4 (Prod.ext rfl (ite_eq_right hm))
    refine ⟨h1, h2, v, h3, ?_⟩
    by_contra hv
    apply h4
    refine Prod.ext rfl ?_
    show cwUpd t.l t.e t.x t.xi s.2.2.2 (some v) = s.2.2.2
    rw [cwUpd_some_of_none _ _ _ _ h2]
    exact ite_eq_right hv

/-- **The codeword-recorded mass of a trial's `h`-read** is at most the potential of its mode. -/
theorem diagMass_cwSet_readH_le (lab : RLabel) (x xi : X) (z : Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    diagMass (cwSet (.inl (.inl (.inr (.readH z (cwLiftHu (cwHu1 cwUpd) lab x xi)))))) σ ≤
      potential (setProj (cwHit (cwHp lab) xi z)) σ := by
  rw [potential_setProj _ hσ]
  refine diagMass_mono (fun q hq ↦ ?_) σ
  obtain ⟨ht, hc⟩ := hq
  have he := eq_readH_trialOf trialUpd ht
  set zt := trialOf trialUpd (.readH z (cwLiftHu (cwHu1 cwUpd) lab x xi))
  obtain ⟨hz, hu⟩ := HwRead.readH.inj he
  obtain ⟨h1, v, h3, h4⟩ := (cwRec_iff _ _ _).1 hc
  rw [← hz] at h1 h3
  have h4' : cwLiftHu (cwHu1 cwUpd) lab x xi q.2.2.2 (some v) ≠ q.2.2.2 := by
    rw [hu]
    exact h4
  exact (cwRec_iff z ⟨lab.layer, lab.key, x, xi⟩ q.2).2 ⟨h1, v, h3, h4'⟩

theorem cwKp_free (π : Equiv.Perm (X × Z)) (P : PublicParameter) (J : CwJ) :
    cwKp π P .free J = 0 := by
  rcases J with (_ | _) | _ <;> rfl

theorem potential_ite_zero (c : Prop) [Decidable c] (K : Matrix (HwReg X Z Mem) (HwReg X Z Mem) ℂ)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) :
    potential (if c then K else 0) σ = if c then potential K σ else 0 := by
  split_ifs
  · rfl
  · exact potential_zero σ

/-- The trial `j` term splits off the trials from `j` on. -/
theorem sum_le_split (f : Fin randomizerAttemptLimit → ℝ≥0∞) {j : ℕ}
    (hj : j < randomizerAttemptLimit) :
    ∑ i : Fin randomizerAttemptLimit × Fin 4, (if j ≤ i.1.val then f i.1 else 0) =
      ∑ i : Fin randomizerAttemptLimit × Fin 4, (if j < i.1.val then f i.1 else 0) +
        4 * f ⟨j, hj⟩ := by
  have hp : ∀ i : Fin randomizerAttemptLimit, (if j ≤ i.val then f i else 0) =
      (if j < i.val then f i else 0) + if i = ⟨j, hj⟩ then f i else 0 := fun i ↦ by
    by_cases h1 : j < i.val
    · have h2 : i ≠ ⟨j, hj⟩ := fun h ↦ by rw [h] at h1; exact lt_irrefl _ h1
      rw [ite_eq_left h1.le, ite_eq_left h1, ite_eq_right h2, add_zero]
    · by_cases h3 : i = ⟨j, hj⟩
      · subst h3
        simp
      · have h4 : ¬ j ≤ i.val := fun h ↦ h3 (Fin.ext (le_antisymm (not_lt.mp h1) h))
        rw [ite_eq_right h4, ite_eq_right h1, ite_eq_right h3, add_zero]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hp, Finset.sum_add_distrib]
  norm_num

/-- The no-`⊥` invariant survives a read. -/
theorem cw_noBot_conj_read (c : HwRead X Z Mem) (r : c.Result)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (h : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z Mem) σ)) :
    QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z Mem)
        (MatrixMap.conj (hwReadKraus c r) σ)) := by
  have hd := decR_step_noBot (S := HPos) m0R (.inl (.inl (.inr c))) r _ h
  set U : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ :=
    (1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z Mem
  have hUh : Uᴴ = U := by
    simp only [U, conjTranspose_kronecker, conjTranspose_one, conjTranspose_compressReg]
  have hUU : ∀ N : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ, U * (U * N) = N :=
    fun N ↦ by
      rw [← Matrix.mul_assoc, show U * U = 1 by
        simp only [U, ← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self,
          one_kronecker_one], Matrix.one_mul]
  have he : MatrixMap.conj U (MatrixMap.conj (hwReadKraus c r) σ) =
      MatrixMap.conj (U * hwReadKraus c r * U) (MatrixMap.conj U σ) := by
    simp only [MatrixMap.conj_apply, conjTranspose_mul, hUh, Matrix.mul_assoc, hUU]
  rw [he]
  have hb := decR_branch_apply (S := HPos) (M := Selections) m0R (.inl (.inl (.inr c))) r _
    (runtime2_branch m0R (.inl (.inr c)) r) (MatrixMap.conj U σ)
  exact (congrArg (QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) {s | NoBot s}) hb).mp hd

/-- The register states of a trial already started, kept by a read of another `k`-cell. -/
theorem cwTD_keep_readK (P : PublicParameter) (lab : RLabel) (base : Randomizer) {i : ℕ}
    {x : X} (hx : x ≠ cwBlk P lab base i) (r : Option Z × Mem) (s' a : Unit × HwReg X Z Mem)
    (h : hwReadKraus (.readK x fun m _ ↦ m) r s' a ≠ 0) :
    s'.2 ∈ cwTD P lab base i ↔ a.2 ∈ cwTD P lab base i := by
  obtain ⟨-, hK⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) h
  obtain ⟨-, -, hk, hW, hm, hm'⟩ := cw_readKrausK_ne_zero x _ r hK
  have hmem : s'.2.2.2 = a.2.2.2 := by rw [hm', hm]
  simp only [cwTD, Set.mem_ofPred_eq, hk _ (Ne.symm hx), hW, hmem]

/-- The register states of a trial already started, kept by a read of a `k'`-cell. -/
theorem cwTD_keep_readK' (P : PublicParameter) (lab : RLabel) (base : Randomizer) (i : ℕ)
    (y : X) (r : Option Z × Mem) (s' a : Unit × HwReg X Z Mem)
    (h : hwReadKraus (.readK' y fun m _ ↦ m) r s' a ≠ 0) :
    s'.2 ∈ cwTD P lab base i ↔ a.2 ∈ cwTD P lab base i := by
  obtain ⟨-, hK⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) h
  obtain ⟨-, hk, hW, hm, hm'⟩ := cw_readKrausK'_ne_zero y _ r hK
  have hmem : s'.2.2.2 = a.2.2.2 := by rw [hm', hm]
  simp only [cwTD, Set.mem_ofPred_eq, hk, hW, hmem]

/-- The register states of a trial already started, kept by a record port. -/
theorem cwTD_keep_rec (P : PublicParameter) (lab : RLabel) (base : Randomizer) (i : ℕ)
    (T : Finset HPos) (m : Mem) (s' a : Unit × HwReg X Z Mem)
    (h : recKraus T m s' a ≠ 0) :
    s'.2 ∈ cwTD P lab base i ↔ a.2 ∈ cwTD P lab base i := by
  have he := eq_of_recKraus_ne_zero (u := a.1) (u' := s'.1) (s := a.2) (s' := s'.2) h
  rw [he]
  rfl

/-- **A trial's `h`-read lowers the trials already started**: it can only select the key. -/
theorem sum_pot_cwTD_readH_le (P : PublicParameter) (lab : RLabel) (base : Randomizer) (i : ℕ)
    (z : Z) (x xi : X) {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hσ : σ.PosSemidef) :
    ∑ r : Option X × Mem, potential (setProj (cwTD P lab base i))
        (MatrixMap.conj (hwReadKraus (.readH z (cwLiftHu (cwHu1 cwUpd) lab x xi)) r) σ) ≤
      potential (setProj (cwTD P lab base i)) σ := by
  classical
  set u := cwLiftHu (cwHu1 cwUpd) lab x xi
  refine cw_sum_pot_setProj_le (fun r ↦ hwReadKraus (.readH z u) r) (sum_hwReadKraus _) _ _
    (fun r ↦ if cwU lab (u r.2 r.1) then 1 else 0) (fun r ↦ by split_ifs <;> norm_num)
    (fun r s' a h ↦ ?_) (fun r s' a b ha hb ↦ ?_) hσ
  · obtain ⟨-, hK⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) h
    obtain ⟨hk, hW, hm, hm'⟩ := cw_readKrausH_ne_zero z u r hK
    by_cases hc : cwU lab (u r.2 r.1)
    · have hc' : cwU lab a.2.2.2 := hm ▸ cwU_of_upd lab x xi r.2 r.1 hc
      have hiff : s'.2 ∈ cwTD P lab base i ↔ a.2 ∈ cwTD P lab base i := by
        simp only [cwTD, Set.mem_ofPred_eq, hk, hW, hm', hm]
        rw [hm] at hc'
        simp only [hc, hc', and_true]
      rw [ite_eq_left hc, one_mul]
      by_cases ha : a.2 ∈ cwTD P lab base i
      · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hiff.2 ha), Pi.one_apply, Pi.one_apply]
      · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem (mt hiff.1 ha)]
    · rw [ite_eq_right hc, zero_mul]
      refine Set.indicator_of_notMem (fun hs ↦ hc ?_) _
      have := hs.2
      rwa [hm'] at this
  · obtain ⟨-, hKa⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) ha
    obtain ⟨-, hKb⟩ := one_kronecker_ne_zero (a := b.1) (a' := s'.1) (b := b.2) (b' := s'.2) hb
    obtain ⟨hka, hWa, hma, -⟩ := cw_readKrausH_ne_zero z u r hKa
    obtain ⟨hkb, hWb, hmb, -⟩ := cw_readKrausH_ne_zero z u r hKb
    have hiff : a.2 ∈ cwTD P lab base i ↔ b.2 ∈ cwTD P lab base i := by
      simp only [cwTD, Set.mem_ofPred_eq, ← hka, ← hkb, ← hWa, ← hWb, hma, hmb]
    by_cases ha' : a.2 ∈ cwTD P lab base i
    · rw [Set.indicator_of_mem ha', Set.indicator_of_mem (hiff.1 ha'), Pi.one_apply,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem ha', Set.indicator_of_notMem (mt hiff.2 ha')]

theorem cwRecHw_eq_indicator (P : PublicParameter) (lab : RLabel) (base : Randomizer) (j : ℕ)
    (s : Unit × HwReg X Z Mem) :
    cwRecHw (cwU lab) (cwBlk P lab base j) s = Set.indicator (cwTD P lab base j) 1 s.2 := by
  classical
  unfold cwRecHw
  by_cases h : s.2 ∈ cwTD P lab base j
  · rw [Set.indicator_of_mem h, Pi.one_apply]
    exact ite_eq_left h
  · rw [Set.indicator_of_notMem h]
    exact ite_eq_right h

theorem cw_potential_setProj_eq_sum (S : Set (HwReg X Z Mem))
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) :
    potential (setProj S) σ = ENNReal.ofReal (∑ s, (S.indicator 1 s.2 : ℝ) * (σ s s).re) :=
  cw_potential_setProj_eq_dW S σ

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter)

/-- **The step of a trial's `k`-read**: the potentials after it are at most those before plus its
fresh part. -/
theorem cw_step_readK (lab : RLabel) (base : Randomizer) {j : ℕ}
    (hj : j < randomizerAttemptLimit)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hinv : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z Mem) σ)) :
    ∑ r : Option Z × Mem, ∑ J, potential (cwKp π P (.afK lab base j (r.1.getD 0)) J)
        (MatrixMap.conj (hwReadKraus (.readK (cwBlk P lab base j) fun m _ ↦ m) r) σ) ≤
      ∑ J, potential (cwKp π P (.grd lab base j) J) σ +
        ENNReal.ofReal (∑ s, cwFresh anyHp π (cwBlk P lab base j) s * (σ s s).re) := by
  set x := cwBlk P lab base j with hx
  have hre : ∀ s, 0 ≤ (σ s s).re := fun s ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hσr := fun r : Option Z × Mem ↦ posSemidef_conj (hwReadKraus (.readK x fun m _ ↦ m) r) hσ
  have hL : ∀ r : Option Z × Mem, ∑ J, potential (cwKp π P (.afK lab base j (r.1.getD 0)) J)
      (MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) =
      ∑ r' : Option Z × Mem, potential (setProj (cwHit (cwHp lab) (π (x, r.1.getD 0)).1
          ((π (x, r.1.getD 0)).2 + r'.1.getD 0)) * readKrausK' (π (x, r.1.getD 0)).1
            (fun m _ ↦ m) r') (MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) +
        ∑ i : Fin randomizerAttemptLimit × Fin 4, (if j < i.1.val then
          potential (setProj (cwTD P lab base i.1))
            (MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) else 0) := fun r ↦ by
    rw [Fintype.sum_sum_type, Fintype.sum_option]
    simp only [cwKp, potential_zero, zero_add, potential_ite_zero]
    rfl
  have hR : ∑ J, potential (cwKp π P (.grd lab base j) J) σ =
      ∑ i : Fin randomizerAttemptLimit × Fin 4,
        (if j ≤ i.1.val then potential (setProj (cwTD P lab base i.1)) σ else 0) := by
    rw [Fintype.sum_sum_type, Fintype.sum_option]
    simp only [cwKp, potential_zero, zero_add, Finset.sum_const_zero, potential_ite_zero]
  simp only [hL, hR, Finset.sum_add_distrib]
  rw [sum_le_split (fun i ↦ potential (setProj (cwTD P lab base i)) σ) hj]
  -- the codeword-recorded part
  have hnb : CellNoBot (splitK x) (actK x) σ := readNoBot_of_noBot (.readK x fun m _ ↦ m) hinv
  have hnb' : ∀ r : Option Z × Mem, CellNoBot (splitK' (π (x, r.1.getD 0)).1)
      (actK' (π (x, r.1.getD 0)).1) (MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) :=
    fun r ↦ readNoBot_of_noBot (.readK' (π (x, r.1.getD 0)).1 fun m _ ↦ m)
      (cw_noBot_conj_read (.readK x fun m _ ↦ m) r hinv)
  have h1 := sum_pot_cw_le (cwHp lab) π x hσ hnb hnb'
  have hU : ∀ xi z dh wm, cwHp lab xi z dh wm → cwU lab wm.2 := fun _ _ _ _ h ↦ h.2.1
  have hpt : ∀ s, cB (splitK x) (actK x) (tauK x fun m _ ↦ m) (idxK x) (phiK x fun m _ ↦ m)
      (cwQOut (cwHp lab) π x) s * (σ s s).re ≤
      4 * ((cwTD P lab base j).indicator 1 s.2 * (σ s s).re) +
        cwFresh anyHp π x s * (σ s s).re := fun s ↦ by
    have hb := cB_out_le hU π x s
    have hf := cwFresh_mono (cwHp_anyHp lab) π x s
    rw [cwRecHw_eq_indicator] at hb
    nlinarith [hre s]
  have h2 : ENNReal.ofReal (∑ s, cB (splitK x) (actK x) (tauK x fun m _ ↦ m) (idxK x)
      (phiK x fun m _ ↦ m) (cwQOut (cwHp lab) π x) s * (σ s s).re) ≤
      4 * potential (setProj (cwTD P lab base j)) σ +
        ENNReal.ofReal (∑ s, cwFresh anyHp π x s * (σ s s).re) := by
    rw [cw_potential_setProj_eq_sum]
    have hn1 : 0 ≤ ∑ s, ((cwTD P lab base j).indicator 1 s.2 : ℝ) * (σ s s).re :=
      Finset.sum_nonneg fun s _ ↦ mul_nonneg (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
        (hre s)
    have hn2 : 0 ≤ ∑ s, cwFresh anyHp π x s * (σ s s).re :=
      Finset.sum_nonneg fun s _ ↦ mul_nonneg (cwFresh_nonneg _ _ _ _) (hre s)
    calc _ ≤ ENNReal.ofReal (4 * ∑ s, ((cwTD P lab base j).indicator 1 s.2 : ℝ) * (σ s s).re +
          ∑ s, cwFresh anyHp π x s * (σ s s).re) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun s _ ↦ hpt s
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) hn2, ENNReal.ofReal_mul (by norm_num)]
          norm_num
  -- the later trials
  have h3 : ∑ r : Option Z × Mem, ∑ i : Fin randomizerAttemptLimit × Fin 4,
      (if j < i.1.val then potential (setProj (cwTD P lab base i.1))
        (MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) else 0) ≤
      ∑ i : Fin randomizerAttemptLimit × Fin 4,
        (if j < i.1.val then potential (setProj (cwTD P lab base i.1)) σ else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    by_cases hi : j < i.1.val
    · simp only [ite_eq_left hi]
      have hne : x ≠ cwBlk P lab base i.1 := fun h ↦
        (Nat.ne_of_lt hi) (cwBlk_inj P lab base hj i.1.isLt h)
      exact cw_sum_pot_setProj_keep (fun r ↦ hwReadKraus (.readK x fun m _ ↦ m) r)
        (sum_hwReadKraus _) _ (cwTD_keep_readK P lab base hne) hσ
    · simp only [ite_eq_right hi, Finset.sum_const_zero, le_refl]
  calc _ ≤ (4 * potential (setProj (cwTD P lab base j)) σ +
        ENNReal.ofReal (∑ s, cwFresh anyHp π x s * (σ s s).re)) +
        ∑ i : Fin randomizerAttemptLimit × Fin 4,
          (if j < i.1.val then potential (setProj (cwTD P lab base i.1)) σ else 0) :=
        add_le_add (h1.trans h2) h3
    _ = _ := by ring

/-- **The step of a trial's `k'`-read**: the potentials move exactly. -/
theorem cw_step_readK' (lab : RLabel) (base : Randomizer) (j : ℕ) (a : Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    ∑ r : Option Z × Mem, ∑ J, potential (cwKp π P (.afK' lab base j
        (π (cwBlk P lab base j, a)).1 ((π (cwBlk P lab base j, a)).2 + r.1.getD 0)) J)
        (MatrixMap.conj (hwReadKraus (.readK' (π (cwBlk P lab base j, a)).1 fun m _ ↦ m) r) σ) ≤
      ∑ J, potential (cwKp π P (.afK lab base j a) J) σ := by
  set y := (π (cwBlk P lab base j, a)).1
  have hL : ∀ r : Option Z × Mem, ∑ J, potential (cwKp π P (.afK' lab base j y
      ((π (cwBlk P lab base j, a)).2 + r.1.getD 0)) J)
        (MatrixMap.conj (hwReadKraus (.readK' y fun m _ ↦ m) r) σ) =
      potential (setProj (cwHit (cwHp lab) y ((π (cwBlk P lab base j, a)).2 + r.1.getD 0)) *
        readKrausK' y (fun m _ ↦ m) r) σ +
        ∑ i : Fin randomizerAttemptLimit × Fin 4, (if j < i.1.val then
          potential (setProj (cwTD P lab base i.1))
            (MatrixMap.conj (hwReadKraus (.readK' y fun m _ ↦ m) r) σ) else 0) := fun r ↦ by
    rw [Fintype.sum_sum_type, Fintype.sum_option]
    simp only [cwKp, potential_zero, Finset.sum_const_zero, add_zero, potential_ite_zero]
    rw [← potential_conj_kron]
    rfl
  have hR : ∑ J, potential (cwKp π P (.afK lab base j a) J) σ =
      ∑ r : Option Z × Mem, potential (setProj (cwHit (cwHp lab) y
        ((π (cwBlk P lab base j, a)).2 + r.1.getD 0)) * readKrausK' y (fun m _ ↦ m) r) σ +
      ∑ i : Fin randomizerAttemptLimit × Fin 4,
        (if j < i.1.val then potential (setProj (cwTD P lab base i.1)) σ else 0) := by
    rw [Fintype.sum_sum_type, Fintype.sum_option]
    simp only [cwKp, potential_zero, zero_add, potential_ite_zero]
    rfl
  simp only [hL, hR, Finset.sum_add_distrib]
  refine add_le_add le_rfl ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  by_cases hi : j < i.1.val
  · simp only [ite_eq_left hi]
    exact cw_sum_pot_setProj_keep (fun r ↦ hwReadKraus (.readK' y fun m _ ↦ m) r)
      (sum_hwReadKraus _) _ (cwTD_keep_readK' P lab base i.1 y) hσ
  · simp only [ite_eq_right hi, Finset.sum_const_zero, le_refl]

/-- **The step of a trial's `h`-read**: its codeword-recorded mass is paid by the potential of its
mode; the later trials can only lose their unselected key. -/
theorem cw_step_readH (lab : RLabel) (base : Randomizer) (j : ℕ) (xi : X) (z : Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    diagMass (cwSet (.inl (.inl (.inr (.readH z
        (cwLiftHu (cwHu1 cwUpd) lab (cwBlk P lab base j) xi)))))) σ +
      ∑ r : Option X × Mem, ∑ J, potential (cwKp π P (.grd lab base (j + 1)) J)
        (MatrixMap.conj (hwReadKraus (.readH z
          (cwLiftHu (cwHu1 cwUpd) lab (cwBlk P lab base j) xi)) r) σ) ≤
      ∑ J, potential (cwKp π P (.afK' lab base j xi z) J) σ := by
  set u := cwLiftHu (cwHu1 cwUpd) lab (cwBlk P lab base j) xi
  have hL : ∀ r : Option X × Mem, ∑ J, potential (cwKp π P (.grd lab base (j + 1)) J)
      (MatrixMap.conj (hwReadKraus (.readH z u) r) σ) =
      ∑ i : Fin randomizerAttemptLimit × Fin 4, (if j < i.1.val then
        potential (setProj (cwTD P lab base i.1))
          (MatrixMap.conj (hwReadKraus (.readH z u) r) σ) else 0) := fun r ↦ by
    rw [Fintype.sum_sum_type, Fintype.sum_option]
    simp only [cwKp, potential_zero, zero_add, Finset.sum_const_zero, potential_ite_zero,
      Nat.succ_le_iff]
  have hR : ∑ J, potential (cwKp π P (.afK' lab base j xi z) J) σ =
      potential (setProj (cwHit (cwHp lab) xi z)) σ +
      ∑ i : Fin randomizerAttemptLimit × Fin 4,
        (if j < i.1.val then potential (setProj (cwTD P lab base i.1)) σ else 0) := by
    rw [Fintype.sum_sum_type, Fintype.sum_option]
    simp only [cwKp, potential_zero, Finset.sum_const_zero, add_zero, potential_ite_zero]
  simp only [hL, hR]
  refine add_le_add (diagMass_cwSet_readH_le lab _ xi z hσ) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  by_cases hi : j < i.1.val
  · simp only [ite_eq_left hi]
    exact sum_pot_cwTD_readH_le P lab base i.1 z _ xi hσ
  · simp only [ite_eq_right hi, Finset.sum_const_zero, le_refl]

theorem cw_step_readK_t (lab : RLabel) (base : Randomizer) {j : ℕ}
    (hj : j < randomizerAttemptLimit)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hinv : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z Mem) σ)) :
    ∑' r : Option Z × Mem, ∑ J, potential (cwKp π P (.afK lab base j (r.1.getD 0)) J)
        (MatrixMap.conj (hwReadKraus (.readK (cwBlk P lab base j) fun m _ ↦ m) r) σ) ≤
      ∑ J, potential (cwKp π P (.grd lab base j) J) σ +
        ENNReal.ofReal (∑ s, cwFresh anyHp π (cwBlk P lab base j) s * (σ s s).re) := by
  rw [tsum_fintype]
  exact cw_step_readK π P lab base hj hσ hinv

theorem cw_step_readK'_t (lab : RLabel) (base : Randomizer) (j : ℕ) (a : Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    ∑' r : Option Z × Mem, ∑ J, potential (cwKp π P (.afK' lab base j
        (π (cwBlk P lab base j, a)).1 ((π (cwBlk P lab base j, a)).2 + r.1.getD 0)) J)
        (MatrixMap.conj (hwReadKraus (.readK' (π (cwBlk P lab base j, a)).1 fun m _ ↦ m) r) σ) ≤
      ∑ J, potential (cwKp π P (.afK lab base j a) J) σ := by
  rw [tsum_fintype]
  exact cw_step_readK' π P lab base j a hσ

theorem cw_step_readH_t (lab : RLabel) (base : Randomizer) (j : ℕ) (xi : X) (z : Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    diagMass (cwSet (.inl (.inl (.inr (.readH z
        (cwLiftHu (cwHu1 cwUpd) lab (cwBlk P lab base j) xi)))))) σ +
      ∑' r : Option X × Mem, ∑ J, potential (cwKp π P (.grd lab base (j + 1)) J)
        (MatrixMap.conj (hwReadKraus (.readH z
          (cwLiftHu (cwHu1 cwUpd) lab (cwBlk P lab base j) xi)) r) σ) ≤
      ∑ J, potential (cwKp π P (.afK' lab base j xi z) J) σ := by
  rw [tsum_fintype]
  exact cw_step_readH π P lab base j xi z hσ

/-- **The step of a reveal**: the trials already started of the label it reveals. -/
theorem cw_step_rec (o : Option RLabel) (bse : RLabel → Randomizer) (T : Finset HPos)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    ∑' m : Mem, ∑ J, potential (cwKp π P (cwOptNx o bse) J)
        (MatrixMap.conj (recKraus (X := X) (Z := Z) T m) σ) ≤ cwRevCharge P o bse σ := by
  rw [tsum_fintype]
  rcases o with _ | lab
  · simp only [cwOptNx, cwKp_free, potential_zero, Finset.sum_const_zero, zero_le]
  · have hL : ∀ m : Mem, ∑ J, potential (cwKp π P (cwOptNx (some lab) bse) J)
        (MatrixMap.conj (recKraus (X := X) (Z := Z) T m) σ) =
        ∑ i : Fin randomizerAttemptLimit × Fin 4, potential (setProj (cwTD P lab (bse lab) i.1))
          (MatrixMap.conj (recKraus (X := X) (Z := Z) T m) σ) := fun m ↦ by
      rw [Fintype.sum_sum_type, Fintype.sum_option]
      simp only [cwOptNx, cwKp, potential_zero, zero_add, Finset.sum_const_zero, zero_le,
        ↓reduceIte]
    simp only [hL]
    rw [Finset.sum_comm]
    show _ ≤ ∑ i : Fin randomizerAttemptLimit × Fin 4,
      diagMass {q : Unit × HwReg X Z Mem | q.2 ∈ cwTD P lab (bse lab) i.1} σ
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [← potential_setProj _ hσ]
    exact cw_sum_pot_setProj_keep (fun m ↦ recKraus (X := X) (Z := Z) T m) (sum_recKraus T) _
      (cwTD_keep_rec P lab (bse lab) i.1 T) hσ

theorem diagMass_cwSet_of_not_readH (i : (recHwSpec X Z HPos Selections).Port)
    (hi : ∀ z u, i ≠ .inl (.inl (.inr (.readH z u))))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ) :
    diagMass (cwSet i) σ = 0 := by
  have h : cwSet i = ∅ := by
    rcases i with ((i | c) | c) | T
    · rfl
    · refine Set.eq_empty_of_forall_notMem fun q hq ↦ ?_
      obtain ⟨⟨zt, hzt⟩, -⟩ := hq
      exact hi zt.1 _ (by rw [hzt])
    · rfl
    · rfl
  rw [h, diagMass_empty]

/-- **The step condition of the search modes** on the no-`⊥` invariant: the codeword-recorded mass
of every allowed call plus the potentials after it is at most the potentials before plus the
charge. -/
theorem cw_step (v : HPos → Digest) (μ : CwMode) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ)
    (hσ : σ.PosSemidef) (hinv : CwInv i σ) (hok : cwOkZ π P (cwLiftHu (cwHu1 cwUpd)) μ i) :
    diagMass (cwSet i) σ + ∑' r, ∑ J, potential (cwKp π P (cwNxZ π P v μ i r) J)
        (((runtimeR m0R).step i).branch r σ) ≤
      ∑ J, potential (cwKp π P μ J) σ + cwCharge π P v i σ := by
  rcases i with ((i | c) | c) | T
  · rw [diagMass_cwSet_of_not_readH _ (fun _ _ h ↦ by cases h), zero_add]
    refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun r ↦ Finset.sum_eq_zero fun J _ ↦ ?_))
      zero_le
    rw [show cwKp π P (cwNxZ π P v μ (.inl (.inl (.inl i))) r) J = 0 from cwKp_free π P J]
    exact potential_zero _
  · have hb : ∀ r, ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
    simp only [hb]
    rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;>
      rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z'⟩
    all_goals try exact hok.elim
    · obtain ⟨rfl, rfl⟩ := hok
      exact (cw_step_readH_t π P lab base j xi z hσ).trans le_self_add
    · obtain ⟨hj, rfl, rfl⟩ := hok
      rw [diagMass_cwSet_of_not_readH _ (fun _ _ h ↦ by cases h), zero_add]
      exact cw_step_readK_t π P lab base hj hσ hinv
    · obtain ⟨rfl, rfl⟩ := hok
      rw [diagMass_cwSet_of_not_readH _ (fun _ _ h ↦ by cases h), zero_add]
      exact (cw_step_readK'_t π P lab base j a hσ).trans le_self_add
  · rw [diagMass_cwSet_of_not_readH _ (fun _ _ h ↦ by cases h), zero_add]
    refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun r ↦ Finset.sum_eq_zero fun J _ ↦ ?_))
      zero_le
    rw [show cwKp π P (cwNxZ π P v μ (.inl (.inr c)) r) J = 0 from cwKp_free π P J]
    exact potential_zero _
  · rw [diagMass_cwSet_of_not_readH _ (fun _ _ h ↦ by cases h), zero_add]
    exact (cw_step_rec π P (cwRevLab T) (fun lab ↦ v (.inr lab)) T hσ).trans le_add_self

/-- **The codeword-recorded mass of the challenge prefix is at most its charges**: the fresh parts
of the trials' `k`-reads and, at each reveal of a randomizer base, four times the trials of the
search already started (block recorded or hardwired, key unselected). -/
theorem cwRecT_le_charge (A : Adversary (X × Z)) (pub : Pub) (v : HPos → Digest) :
    cwRecT A pub v ≤ (runtimeR m0R).totalWeight .instruments (cwCharge pub.perm pub.param v)
      (realizeT v (prefixT Selections cwUpd pub A)) initR := by
  rw [← cwDiagT_eq]
  have h := totalWeight_le_modedP_inv (runtimeR m0R) .instruments (cwKp pub.perm pub.param)
    _ CwInv (fun _ _ _ h ↦ h) (fun i σ ↦ diagMass (cwSet i) σ) (cwCharge pub.perm pub.param v)
    (fun μ i σ hσ hi hok ↦ cw_step pub.perm pub.param v μ i σ hσ hi hok)
    (realizeT v (prefixT Selections cwUpd pub A)) .free (modedP_prefixR cwUpd pub A v)
    initR_posSemidef (forallQueries_noBot m0R .instruments _
      (noBot_init m0R (SubState.basis ()).matrix))
  refine h.trans (le_of_eq ?_)
  rw [Finset.sum_eq_zero fun J _ ↦ ?_, zero_add]
  rw [cwKp_free]
  exact potential_zero _

end main

/-! ## The fresh part of a `k`-read, counted -/

section freshCount

variable {X₁ Z₁ M : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [AddCommGroup Z₁]

/-- The value a `k'`-cell carries: hardwired, else recorded, else `0`. -/
def cwKVal (W : Hw X₁ Z₁) (dk' : Database X₁ Z₁) (y : X₁) : Z₁ :=
  match W.2.2 y, dk' y with
  | some c, _ => c
  | none, some c => c
  | none, none => 0

theorem ite_true_and_one {P Q : Prop} [Decidable (P ∧ Q)] [Decidable Q] (h : P) :
    (if P ∧ Q then (1 : ℝ) else 0) = if Q then 1 else 0 := by
  by_cases hq : Q
  · rw [ite_eq_left ⟨h, hq⟩, ite_eq_left hq]
  · rw [ite_eq_right (fun h' ↦ hq h'.2), ite_eq_right hq]

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [AddCommGroup Z₁] in
theorem cwInd_le_isSome {Hp : HitPred X₁ Z₁ M}
    (hH : ∀ xi z dh wm, Hp xi z dh wm → (dh z).isSome) (xi : X₁) (z : Z₁) (dh : Database Z₁ X₁)
    (wm : Hw X₁ Z₁ × M) : cwInd Hp xi z dh wm ≤ if (dh z).isSome then 1 else 0 := by
  classical
  unfold cwInd
  by_cases h : Hp xi z dh wm
  · rw [ite_eq_left h, ite_eq_left (hH _ _ _ _ h)]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num

omit [Fintype X₁] [DecidableEq X₁] [DecidableEq Z₁] in
theorem sum_isSome_add (dh : Database Z₁ X₁) (z0 : Z₁) :
    ∑ c : Z₁, (if (dh (z0 + c)).isSome then (1 : ℝ) else 0) = dh.size := by
  rw [show ∑ c : Z₁, (if (dh (z0 + c)).isSome then (1 : ℝ) else 0) =
      ∑ z : Z₁, (if (dh z).isSome then (1 : ℝ) else 0) from
    Fintype.sum_equiv (Equiv.addLeft z0) _ _ fun _ ↦ rfl, Finset.sum_boole]
  rfl

omit [Fintype X₁] [DecidableEq X₁] [DecidableEq Z₁] in
/-- The bound after a `k'`-read with a predicate of recorded cells. -/
theorem cwBetaIn_le_count [Nonempty Z₁] {Hp : HitPred X₁ Z₁ M}
    (hH : ∀ xi z dh wm, Hp xi z dh wm → (dh z).isSome) (y xi : X₁) (z0 : Z₁)
    (dh : Database Z₁ X₁) (dk' : Database X₁ Z₁) (wm : Hw X₁ Z₁ × M) :
    cwBetaIn Hp y xi z0 dh dk' wm ≤ 2 * dh.size / Fintype.card Z₁ +
      2 * (if (wm.1.2.2 y ≠ none ∨ dk' y ≠ none) ∧ (dh (z0 + cwKVal wm.1 dk' y)).isSome
        then 1 else 0) := by
  classical
  have hN : (0 : ℝ) < Fintype.card Z₁ := by exact_mod_cast Fintype.card_pos
  have h0 : (0 : ℝ) ≤ 2 * dh.size / Fintype.card Z₁ := by positivity
  rcases hW : wm.1.2.2 y with _ | c <;> rcases hd : dk' y with _ | c'
  · have hb : cwBetaIn Hp y xi z0 dh dk' wm =
        2 / Fintype.card Z₁ * ∑ c, cwInd Hp xi (z0 + c) dh wm := by
      simp only [cwBetaIn, hW, hd]
    rw [hb]
    have hs : ∑ c, cwInd Hp xi (z0 + c) dh wm ≤ dh.size := by
      rw [← sum_isSome_add dh z0]
      exact Finset.sum_le_sum fun c _ ↦ cwInd_le_isSome hH _ _ _ _
    calc 2 / (Fintype.card Z₁ : ℝ) * ∑ c, cwInd Hp xi (z0 + c) dh wm
        ≤ 2 / Fintype.card Z₁ * dh.size := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 2 * dh.size / Fintype.card Z₁ := by ring
      _ ≤ _ := le_add_of_nonneg_right (by split_ifs <;> norm_num)
  · have hb : cwBetaIn Hp y xi z0 dh dk' wm = 2 * cwInd Hp xi (z0 + c') dh wm := by
      simp only [cwBetaIn, hW, hd]
    have hk : cwKVal wm.1 dk' y = c' := by simp only [cwKVal, hW, hd]
    have hc := cwInd_le_isSome hH xi (z0 + c') dh wm
    rw [hb, hk]
    rw [ite_true_and_one (by simp)]
    linarith
  · have hb : cwBetaIn Hp y xi z0 dh dk' wm = cwInd Hp xi (z0 + c) dh wm := by
      simp only [cwBetaIn, hW]
    have hk : cwKVal wm.1 dk' y = c := by simp only [cwKVal, hW]
    have hc := cwInd_le_isSome hH xi (z0 + c) dh wm
    rw [hb, hk]
    rw [ite_true_and_one (by simp)]
    have : (0 : ℝ) ≤ if (dh (z0 + c)).isSome then 1 else 0 := by split_ifs <;> norm_num
    linarith
  · have hb : cwBetaIn Hp y xi z0 dh dk' wm = cwInd Hp xi (z0 + c) dh wm := by
      simp only [cwBetaIn, hW]
    have hk : cwKVal wm.1 dk' y = c := by simp only [cwKVal, hW]
    have hc := cwInd_le_isSome hH xi (z0 + c) dh wm
    rw [hb, hk]
    rw [ite_true_and_one (by simp)]
    have : (0 : ℝ) ≤ if (dh (z0 + c)).isSome then 1 else 0 := by split_ifs <;> norm_num
    linarith

/-- The hardwired `k'`-cells. -/
def hwK'Count (W : Hw X₁ Z₁) : ℕ :=
  (Finset.univ.filter fun y ↦ W.2.2 y ≠ none).card

omit [DecidableEq Z₁] in
/-- **The trials' `k'`-cells with a recorded `h`-cell**: through the permutation, at most one block
outcome per recorded or hardwired `k'`-cell and recorded `h`-cell. -/
theorem sum_ite_count_le (π : Equiv.Perm (X₁ × Z₁)) (x : X₁) (W : Hw X₁ Z₁) (dk' : Database X₁ Z₁)
    (dh : Database Z₁ X₁) :
    ∑ a : Z₁, (if (W.2.2 (π (x, a)).1 ≠ none ∨ dk' (π (x, a)).1 ≠ none) ∧
        (dh ((π (x, a)).2 + cwKVal W dk' (π (x, a)).1)).isSome then (1 : ℝ) else 0) ≤
      ((hwK'Count W + dk'.size) * dh.size : ℕ) := by
  classical
  set Y := Finset.univ.filter fun y ↦ W.2.2 y ≠ none ∨ dk' y ≠ none
  set D := Finset.univ.filter fun z ↦ (dh z).isSome
  rw [Finset.sum_boole]
  have hcard : (Finset.univ.filter fun a : Z₁ ↦ (W.2.2 (π (x, a)).1 ≠ none ∨
      dk' (π (x, a)).1 ≠ none) ∧ (dh ((π (x, a)).2 + cwKVal W dk' (π (x, a)).1)).isSome).card ≤
      (Y ×ˢ D).card := by
    refine Finset.card_le_card_of_injOn (fun a ↦ ((π (x, a)).1,
      (π (x, a)).2 + cwKVal W dk' (π (x, a)).1)) (fun a ha ↦ ?_) (fun a _ b _ hab ↦ ?_)
    · obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, h1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩)
    · obtain ⟨h1, h2⟩ := Prod.mk.inj hab
      have h3 : (π (x, a)).2 = (π (x, b)).2 := by
        rw [h1] at h2
        exact add_right_cancel h2
      have h4 : π (x, a) = π (x, b) := Prod.ext h1 h3
      exact (Prod.mk.inj (π.injective h4)).2
  have hY : Y.card ≤ hwK'Count W + dk'.size := by
    have hsub : Y ⊆ (Finset.univ.filter fun y ↦ W.2.2 y ≠ none) ∪
        Finset.univ.filter fun y ↦ (dk' y).isSome := by
      intro y hy
      rcases (Finset.mem_filter.mp hy).2 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Option.isSome_iff_ne_none.mpr h⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hD : D.card = dh.size := rfl
  rw [Finset.card_product] at hcard
  have := hcard.trans (Nat.mul_le_mul_right D.card hY)
  rw [hD] at this
  exact_mod_cast this

omit [DecidableEq Z₁] in
/-- **The fresh part of a `k`-read, counted**: at most `2/|Z|` times `2 N_h + 2 (H_k' + N_k') N_h`,
with `N_h`, `N_k'` the recorded `h`, `k'` cells and `H_k'` the hardwired `k'`-cells. -/
theorem cwFresh_le_count [Nonempty Z₁] {Hp : HitPred X₁ Z₁ M}
    (hH : ∀ xi z dh wm, Hp xi z dh wm → (dh z).isSome) (π : Equiv.Perm (X₁ × Z₁)) (x : X₁)
    (s : Unit × HwReg X₁ Z₁ M) :
    cwFresh Hp π x s ≤ 2 / Fintype.card Z₁ * (2 * s.2.1.1.size +
      2 * ((hwK'Count s.2.2.1 + s.2.1.2.2.size) * s.2.1.1.size : ℕ)) := by
  classical
  have hN : (0 : ℝ) < Fintype.card Z₁ := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ a, cwBetaIn Hp (π (x, a)).1 (π (x, a)).1 (π (x, a)).2 s.2.1.1 s.2.1.2.2 s.2.2 ≤
      2 * s.2.1.1.size + 2 * ((hwK'Count s.2.2.1 + s.2.1.2.2.size) * s.2.1.1.size : ℕ) := by
    refine (Finset.sum_le_sum fun a _ ↦ cwBetaIn_le_count hH _ _ _ _ _ _).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    have hc := sum_ite_count_le π x s.2.2.1 s.2.1.2.2 s.2.1.1
    have he : (Fintype.card Z₁ : ℝ) * (2 * s.2.1.1.size / Fintype.card Z₁) =
        2 * s.2.1.1.size := by field_simp
    rw [he]
    linarith
  unfold cwFresh
  split_ifs
  · exact mul_le_mul_of_nonneg_left hsum (by positivity)
  · positivity

end freshCount

/-! ## The fresh parts along the prefix -/

section freshRun

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

theorem hwK'Count_progUpdate_le {X₁ Z₁ : Type} [Fintype X₁] [DecidableEq X₁] [DecidableEq Z₁]
    (c : HwProg X₁ Z₁) (W : Hw X₁ Z₁) :
    hwK'Count (progUpdate c W) ≤ hwK'Count W + 1 := by
  classical
  cases c with
  | programH z v => exact Nat.le_succ _
  | programK x v => exact Nat.le_succ _
  | programK' x v =>
    unfold hwK'Count
    refine (Finset.card_le_card (t := insert x (Finset.univ.filter fun y ↦ W.2.2 y ≠ none))
      fun y hy ↦ ?_).trans (Finset.card_insert_le _ _)
    by_cases hyx : y = x
    · exact hyx ▸ Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      have h := (Finset.mem_filter.mp hy).2
      simpa [progUpdate, Function.update_of_ne hyx] using h

theorem querySupportedOn_recStep_hw {S M' : Type} [Fintype S] [DecidableEq S] [Fintype M']
    [DecidableEq M'] (T : Finset S) (r : Finset S × M') (t : ℕ)
    (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ)
    (hσ : QuerySupportedOn (fun q : Unit × HwReg X Z (Finset S × M') ↦ hwK'Count q.2.2.1)
      (Set.Iic t) σ) :
    QuerySupportedOn (fun q : Unit × HwReg X Z (Finset S × M') ↦ hwK'Count q.2.2.1)
      (Set.Iic (t + 1)) ((recStep (X := X) (Z := Z) T).branch r σ) := by
  rw [recStep_branch]
  refine QuerySupportedOn.conj hσ fun q' q hK hq ↦ ?_
  rw [eq_of_recKraus_ne_zero (u := q.1) (u' := q'.1) (s := q.2) (s' := q'.2) hK]
  exact (Set.mem_Iic.mp hq).trans (Nat.le_succ t)

/-- **Every port of `runtimeR` hardwires at most one more `k'`-cell.** -/
theorem querySupportedOn_runtimeR_step_hw (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i) (t : ℕ)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ)
    (hσ : QuerySupportedOn (fun q : (recHwSpec X Z HPos Selections).In i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ hwK'Count q.2.2.1) (Set.Iic t) σ) :
    QuerySupportedOn (fun q : (recHwSpec X Z HPos Selections).Out i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ hwK'Count q.2.2.1) (Set.Iic (t + 1))
        (((runtimeR (X := X) (Z := Z) m0R).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · have hb : ((runtimeR m0R).step (.inl (.inl (.inl i)))).branch r σ =
        MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m0R).U i) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m0R i r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    refine QuerySupportedOn.conj hσ fun q' q hK hq ↦ ?_
    have he := snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty X Z) m0R i q.1 q'.1 q.2 q'.2 hK
    show hwK'Count q'.2.2.1 ≤ t + 1
    rw [he]
    exact (Set.mem_Iic.mp hq).trans (Nat.le_succ t)
  · have hb : ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    refine QuerySupportedOn.conj hσ fun q' q hK hq ↦ ?_
    have he := hwReadKraus_ne_zero_hw c r (u := q.1) (u' := q'.1) (s := q.2) (s' := q'.2) hK
    show hwK'Count q'.2.2.1 ≤ t + 1
    rw [he]
    exact (Set.mem_Iic.mp hq).trans (Nat.le_succ t)
  · have hb : ((runtimeR m0R).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m0R c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    refine QuerySupportedOn.conj hσ fun q' q hK hq ↦ ?_
    have he := hwProgKraus_ne_zero_snd c r (u := q.1) (u' := q'.1) (s := q.2) (s' := q'.2) hK
    show hwK'Count q'.2.2.1 ≤ t + 1
    rw [he]
    exact (hwK'Count_progUpdate_le c _).trans (Nat.succ_le_succ (Set.mem_Iic.mp hq))
  · exact querySupportedOn_recStep_hw T r t σ hσ

/-- The initial state has no hardwired cell. -/
theorem querySupportedOn_initR_hwK' :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D ↦
      hwK'Count m.2.2.1) (Set.Iic 0) initR := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty X Z, m0R) : HwReg X Z Mem)).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · have h0 : hwK'Count (hwEmpty X Z) = 0 := by
      simp [hwK'Count, hwEmpty]
    refine ⟨?_, ?_⟩
    · show hwK'Count m.2.2.1 ≤ 0
      rw [← he.1]
      exact h0.le
    · show hwK'Count m'.2.2.1 ≤ 0
      rw [← he.2]
      exact h0.le
  · exact absurd rfl h

/-- The fresh constant: `2/|Z|` times `2 G + 2 (2 G) G`, for at most `G` recorded and hardwired
cells. -/
noncomputable def cwFreshEps (G : ℕ) : ℝ :=
  2 / Fintype.card Z * (2 * G + 2 * ((G + G) * G : ℕ))

/-- The fresh parts of the trials' `k`-reads. -/
noncomputable def cwFreshW (π : Equiv.Perm (X × Z)) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
        ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ → ℝ≥0∞
  | .inl (.inl (.inr (.readK x _))), σ => ENNReal.ofReal (∑ s, cwFresh anyHp π x s * (σ s s).re)
  | _, _ => 0

/-- The charges at the reveals of the randomizer bases. -/
noncomputable def cwRevW (P : PublicParameter) (v : HPos → Digest) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
        ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ → ℝ≥0∞
  | .inr T, σ => cwRevCharge P (cwRevLab T) (fun lab ↦ v (.inr lab)) σ
  | _, _ => 0

theorem cwCharge_le (π : Equiv.Perm (X × Z)) (P : PublicParameter) (v : HPos → Digest)
    (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ) :
    cwCharge π P v i σ ≤ cwFreshW π i σ + cwRevW P v i σ := by
  rcases i with ((i | c) | c) | T
  · exact zero_le
  · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
    · exact zero_le
    · exact le_self_add
    · exact zero_le
  · exact zero_le
  · exact le_add_self

/-- The fresh part at a `k`-read on states with at most `G` recorded and `G` hardwired cells. -/
theorem cwFresh_le_eps (π : Equiv.Perm (X × Z)) (x : X) {G : ℕ} (s : Unit × HwReg X Z Mem)
    (hg : dbGrade s.2.1 ≤ G) (hh : hwK'Count s.2.2.1 ≤ G) :
    cwFresh anyHp π x s ≤ cwFreshEps G := by
  have h1 : s.2.1.1.size ≤ G := (le_max_left _ _).trans hg
  have h2 : s.2.1.2.2.size ≤ G := ((le_max_right _ _).trans (le_max_right _ _)).trans hg
  refine (cwFresh_le_count (fun _ _ _ _ h ↦ ?_) π x s).trans ?_
  · obtain ⟨-, v, hv⟩ := h
    rw [hv]
    rfl
  · unfold cwFreshEps
    have hN : (0 : ℝ) ≤ 2 / Fintype.card Z := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hN
    have h3 : (hwK'Count s.2.2.1 + s.2.1.2.2.size) * s.2.1.1.size ≤ (G + G) * G :=
      Nat.mul_le_mul (Nat.add_le_add hh h2) h1
    have h4 : (s.2.1.1.size : ℝ) ≤ G := by exact_mod_cast h1
    have h5 : (((hwK'Count s.2.2.1 + s.2.1.2.2.size) * s.2.1.1.size : ℕ) : ℝ) ≤
        ((G + G) * G : ℕ) := by exact_mod_cast h3
    linarith

theorem cwFreshEps_nonneg (G : ℕ) : 0 ≤ cwFreshEps G := by
  unfold cwFreshEps
  positivity

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- The calls of the realized prefix: at most `6q + clsCap`. -/
theorem calls_prefixT (pub : Pub) (v : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT v (prefixT Selections cwUpd pub A)) (portCharge fun _ ↦ 1)
      (6 * q + clsCap) := by
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    ((chg_prefixT_of_gameT (hN_sponge cwUpd A hperm hsign pub v)).add
      (chg_prefixT_of_gameT (hN_cls cwUpd A hperm hsign pub v)))
  rcases a with o | ⟨i, E, ℓ⟩
  · exact le_rfl
  · show 1 ≤ (if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1) +
      (if extCls X Z Mem (recSpec HPos Selections) i then 1 else 0)
    split_ifs <;> omega

/-- **The fresh parts along the prefix**: at most `cwFreshEps (6q + clsCap)` per read call, at most
`clsCap` read calls. -/
theorem totalWeight_cwFreshW_le (pub : Pub) (v : HPos → Digest) :
    (runtimeR m0R).totalWeight .instruments (cwFreshW pub.perm)
        (realizeT v (prefixT Selections cwUpd pub A)) initR ≤
      ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) * clsCap := by
  set G := 6 * q + clsCap
  set x := realizeT v (prefixT Selections cwUpd pub A)
  have hg := forallQueries_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.1) (fun _ ↦ 1)
    (fun _ ↦ 0) (querySupportedOn_runtimeR_step m0R) .instruments x (calls_prefixT hperm hsign pub v)
    (isChargeBound_mono_charge (fun _ a ↦ by rcases a with _ | ⟨_, _, _⟩ <;> exact le_rfl)
      (isChargeBound_zero x)) querySupportedOn_initR
  have hh := forallQueries_of_charge_step (runtimeR m0R) (fun s ↦ hwK'Count s.2.1) (fun _ ↦ 1)
    (fun _ ↦ 0) querySupportedOn_runtimeR_step_hw .instruments x (calls_prefixT hperm hsign pub v)
    (isChargeBound_mono_charge (fun _ a ↦ by rcases a with _ | ⟨_, _, _⟩ <;> exact le_rfl)
      (isChargeBound_zero x)) querySupportedOn_initR_hwK'
  set κ : (recHwSpec X Z HPos Selections).Port → ℕ :=
    fun i ↦ if readRecPort Selections i = true then 1 else 0
  have hle := totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i σ ↦ QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
        (runtimeR (X := X) (Z := Z) m0R).D ↦ dbGrade m.2.1) (Set.Iic (0 + G)) σ ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
        (runtimeR (X := X) (Z := Z) m0R).D ↦ hwK'Count m.2.2.1) (Set.Iic (0 + G)) σ)
    (fun i E σ h ↦ ⟨querySupportedOn_traceRight h.1.2, querySupportedOn_traceRight h.2.2⟩)
    (w := cwFreshW pub.perm)
    (w' := fun i σ ↦ ENNReal.ofReal (cwFreshEps G) * (κ i * ENNReal.ofReal σ.trace.re))
    (fun i σ hσ hok ↦ ?_) x initR_posSemidef (forallQueries_and hg hh)
  · refine hle.trans ?_
    refine (le_of_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments
      (ENNReal.ofReal (cwFreshEps G)) (fun i σ ↦ (κ i : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) x
      initR)).trans ?_
    refine mul_le_mul_of_nonneg_left ((totalWeight_chargeTrace_le (runtimeR m0R) .instruments κ x
      (hN_readRec_prefixT hperm hsign pub v) initR_posSemidef).trans ?_) zero_le
    calc (clsCap : ℝ≥0∞) * ENNReal.ofReal initR.trace.re ≤ clsCap * 1 := by
          gcongr
          exact ofReal_trace_initR_le_one
      _ = clsCap := mul_one _
  · rcases i with ((i | c) | c) | T
    · exact zero_le
    · rcases c with ⟨z, u⟩ | ⟨y, u⟩ | ⟨y, u⟩
      · exact zero_le
      · show ENNReal.ofReal (∑ s, cwFresh anyHp pub.perm y s * (σ s s).re) ≤
          ENNReal.ofReal (cwFreshEps G) * (((1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re)
        rw [Nat.cast_one, one_mul, ← ENNReal.ofReal_mul (cwFreshEps_nonneg G)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Matrix.trace, Complex.re_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun s _ ↦ ?_
        have hre : 0 ≤ (σ s s).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
        by_cases h0 : σ s s = 0
        · exact le_of_eq_of_le (by rw [h0, Complex.zero_re, mul_zero])
            (mul_nonneg (cwFreshEps_nonneg G) hre)
        · have hb1 := (hok.1 s s h0).1
          have hb2 := (hok.2 s s h0).1
          simp only [Set.mem_Iic, zero_add] at hb1 hb2
          exact mul_le_mul_of_nonneg_right (cwFresh_le_eps pub.perm y s hb1 hb2) hre
      · exact zero_le
    · exact zero_le
    · exact zero_le

end freshRun

/-! ## The codeword-recorded mass from the reveals -/

section view

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

variable {q : ℕ} {A : Adversary (X × Z)}

/-- **The remaining bound: the trials already started at the reveals**. For every public datum,
the charges at the reveals of the randomizer bases (four times each trial of the search whose block
is recorded or hardwired while the key is unselected), summed over the hidden values, are at most
`R` per hidden value. -/
def CwRevView (A : Adversary (X × Z)) (R : ℝ≥0∞) : Prop :=
  ∀ p : RP, ∑ v : HPos → Digest, (runtimeR m0R).totalWeight .instruments
    (cwRevW (pubR p).param v) (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR ≤
      R * Fintype.card (HPos → Digest)

/-- **`CwRecView` from the reveals**: the codeword-recorded mass is at most the charges at the
reveals plus the fresh parts, `clsCap · cwFreshEps (6q + clsCap)`. -/
theorem cwRecView_of_revView
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime) {R : ℝ≥0∞}
    (hrev : CwRevView A R) :
    CwRecView A (R + ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) * clsCap) := by
  intro p
  have hv : ∀ v : HPos → Digest, cwRecT A (pubR p) v ≤
      ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) * clsCap +
        (runtimeR m0R).totalWeight .instruments (cwRevW (pubR p).param v)
          (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR := fun v ↦ by
    refine (cwRecT_le_charge A (pubR p) v).trans ?_
    refine (totalWeight_le_totalWeight (runtimeR m0R) .instruments
      (w' := fun i σ ↦ cwFreshW (pubR p).perm i σ + cwRevW (pubR p).param v i σ)
      (fun i σ _ ↦ cwCharge_le _ _ v i σ) _ initR_posSemidef).trans ?_
    refine (le_of_eq (totalWeight_add_weight (runtimeR m0R) .instruments
      (cwFreshW (pubR p).perm) (cwRevW (pubR p).param v) _ initR)).trans ?_
    exact add_le_add (totalWeight_cwFreshW_le hperm hsign (pubR p) v) le_rfl
  calc ∑ v, cwRecT A (pubR p) v
      ≤ ∑ v : HPos → Digest, (ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) * clsCap +
          (runtimeR m0R).totalWeight .instruments (cwRevW (pubR p).param v)
            (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR) :=
        Finset.sum_le_sum fun v _ ↦ hv v
    _ ≤ ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) * clsCap * Fintype.card (HPos → Digest) +
          R * Fintype.card (HPos → Digest) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
        exact add_le_add le_rfl (hrev p)
    _ = _ := by ring

end view

end Quantum.Xmss.Assembly

end
