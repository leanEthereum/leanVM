module

public import Quantum.Xmss.Assembly.TrialSource
public import Quantum.Xmss.Assembly.EventSqrt
public import Quantum.Xmss.Assembly.TrialHit

@[expose] public section

/-!
# The randomizer trials' hidden read mass (`htrial`)

TrialSource moves the hidden mass of the challenge prefix's reads onto the trials' `k`-reads
(`totalWeight_prefixT_le_trialW`, the trial charge `trialW`). Here the trial charge is bounded and
summed over the hidden values, which gives GradedMasked's `htrial` on the good hidden values
`TrialHidGood` in the shape of TrialSource's `uavg_mask_readMass_le_xmssR0_good`.

* **One trial on the diagonal** (over abstract `X₁`, `Z₁`; `sum_potential_inner_le`,
  `sum_potential_trial_le`): TrialSource's `re_trace_gramQ_le` twice, at the `k'`-cell with the
  weight of the `h`-cell after it (`wIn`), then at the `k`-cell with the weight of the `k'`-read
  (`qOut`). On a state with no decompressed `⊥` the charge of a `k`-read at `x` is at most the
  diagonal `trialDiag`: the fresh part `(2 cK + 4 cH) / |Z|` (`cK` bounds the outcomes leading `x`
  to a hidden `k'`-cell, `cH` the values leading a capacity to a hidden `h`-cell), four times the
  sources `srcK'`, `srcH` of a filled `k`-cell, `4 / |Z|` times those of an empty one per outcome
  (`srcHE`).
* **The view lemma with a base set** (`sum_queryWeight_view_le_base`): Disclose's view lemma with
  the masses of a base `B ⊇ C v` on the right. At the `k`-read ports
  (`sum_totalWeight_readKSet_h_le`, `sum_totalWeight_readKSet_k'_le`, MassSources'
  `sourcesSlotInv`): the sources weigh `2^-128` of the recorded trial cells `baseK`, `baseK'`.
* **The charge along the prefix** (`totalWeight_trialW_le`): `NoBot` (EndReads' `noBot_runtimeR`
  through EventSqrt's `forallQueries_noBot`) and `SlotInv` (`forallQueries_of_hp`) at every call.
* **Counts** (`cellsK'`, `cellsH`): at most `8 · 498 · 2^32` hidden `k'`- and `h`-cells, so
  `cK = 18 · 8 · 498 · 2^32` (`PermGood π 18`) and `cH = 8 · 498 · 2^32`.
* **`htrial`** (`sum_trialMass_le`): summed over the hidden values, at most `htrialTau R` per hidden
  value, `htrialTau R = clsCap · 2^-462 + 8 · 2^-128 · R`, given the recorded trial cells
  (`trialRecW`) of at most `R` per hidden value.
* **The bad fraction of `TrialHidGood`** (`trialHidGood_r0G_frac_le_keccak`): the trial blocks of
  both layers (`trialSetAll`, at most `2^551`) name no in-table slot (`not_inTable_of_trialBlock`),
  so a hidden `k`-cell that is a trial block is a later `k`-cell of an in-table path (TrialsOff's
  `frac_pathTrial_le`): at most `2^-400` of the padded tables in ReparamR0's good set.
-/

open IPFunctor Matrix MeasureTheory
open scoped ENNReal ComplexOrder Kronecker

universe u v w u₁ v₁

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid

/-! ## Indicators -/

section indicators

private theorem ind_eq_ind {α β : Type} {S : Set α} {T : Set β} {d : α} {e : β}
    (h : d ∈ S ↔ e ∈ T) :
    S.indicator (1 : α → ℝ) d = T.indicator 1 e := by
  by_cases hd : d ∈ S
  · rw [Set.indicator_of_mem hd, Set.indicator_of_mem (h.1 hd)]
    simp only [Pi.one_apply]
  · rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem fun h' ↦ hd (h.2 h')]

private theorem ind_le_ind {α β : Type} {S : Set α} {T : Set β} {d : α} {e : β}
    (h : d ∈ S → e ∈ T) :
    S.indicator (1 : α → ℝ) d ≤ T.indicator 1 e := by
  by_cases hd : d ∈ S
  · rw [Set.indicator_of_mem hd, Set.indicator_of_mem (h hd)]
    simp only [Pi.one_apply, le_refl]
  · rw [Set.indicator_of_notMem hd]
    exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) e

private theorem ind_nonneg {α : Type} (S : Set α) (d : α) : 0 ≤ S.indicator (1 : α → ℝ) d :=
  Set.indicator_nonneg (fun _ _ ↦ zero_le_one) d

private theorem ind_le_one {α : Type} (S : Set α) (d : α) : S.indicator (1 : α → ℝ) d ≤ 1 := by
  by_cases hd : d ∈ S
  · rw [Set.indicator_of_mem hd]
    simp only [Pi.one_apply, le_refl]
  · rw [Set.indicator_of_notMem hd]
    exact zero_le_one

theorem nonneg_of_sum_ind_le {α β : Type} [Fintype β] [Nonempty β] {S : Set α} (f : β → α)
    {c : ℝ} (h : ∑ b, S.indicator (1 : α → ℝ) (f b) ≤ c) : 0 ≤ c :=
  (Finset.sum_nonneg fun b _ ↦ ind_nonneg S (f b)).trans h

end indicators

/-! ## One trial's reads on the diagonal, over abstract types -/

section generic

variable {X₁ Z₁ Mem : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [Fintype Mem] [DecidableEq Mem]

/-! ### Matrices -/

omit [Fintype Mem] in
theorem kron_setProjG (S : Set (HwReg X₁ Z₁ Mem)) :
    (1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S =
      diagonal fun t : Unit × HwReg X₁ Z₁ Mem ↦ (((S.indicator 1 t.2 : ℝ)) : ℂ) := by
  rw [one_kronecker_setProj]
  ext t t'
  simp only [setProj, diagonal_apply, Set.indicator, Pi.one_apply]
  split_ifs <;> simp_all

theorem potential_setProj_mul_eqG (S : Set (HwReg X₁ Z₁ Mem))
    (N : Matrix (HwReg X₁ Z₁ Mem) (HwReg X₁ Z₁ Mem) ℂ)
    (ρ : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ) :
    potential (setProj S * N) ρ = ENNReal.ofReal
      ((((1 : Matrix Unit Unit ℂ) ⊗ₖ N)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ N) * ρ).trace.re) := by
  have e : Nᴴ * setProj S * (setProj S * N) = Nᴴ * setProj S * N := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc Nᴴ, setProj_mul_self]
  rw [potential_eq, conjTranspose_mul, conjTranspose_setProj, e, conjTranspose_kronecker,
    conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]

/-- The potential of a projector on basis states: the weighted diagonal. -/
theorem potential_setProj_eq_sum (S : Set (HwReg X₁ Z₁ Mem))
    (ρ : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ) :
    potential (setProj S) ρ = ENNReal.ofReal (∑ s, S.indicator 1 s.2 * (ρ s s).re) := by
  rw [potential_eq, conjTranspose_setProj, setProj_mul_self, kron_setProjG, re_trace_diagonal_mul]

theorem re_trace_diag_conj (g : Unit × HwReg X₁ Z₁ Mem → ℝ)
    (K σ : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ) :
    ∑ s, g s * ((MatrixMap.conj K σ) s s).re =
      ((Kᴴ * diagonal (fun s ↦ ((g s : ℝ) : ℂ)) * K) * σ).trace.re := by
  rw [← re_trace_diagonal_mul, MatrixMap.conj_apply]
  congr 1
  calc (diagonal (fun s ↦ ((g s : ℝ) : ℂ)) * (K * σ * Kᴴ)).trace
      = (diagonal (fun s ↦ ((g s : ℝ) : ℂ)) * K * σ * Kᴴ).trace := by
        simp only [Matrix.mul_assoc]
    _ = (Kᴴ * (diagonal (fun s ↦ ((g s : ℝ) : ℂ)) * K * σ)).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem re_trace_kraus_diag_nonneg (g : Unit × HwReg X₁ Z₁ Mem → ℝ) (hg : ∀ s, 0 ≤ g s)
    (K : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ)
    {σ : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ} (hσ : σ.PosSemidef) :
    0 ≤ ((Kᴴ * diagonal (fun s ↦ ((g s : ℝ) : ℂ)) * K) * σ).trace.re := by
  have hP : (diagonal fun s ↦ ((g s : ℝ) : ℂ)).PosSemidef :=
    PosSemidef.diagonal fun s ↦ show (0 : ℂ) ≤ ((g s : ℝ) : ℂ) from Complex.zero_le_real.mpr (hg s)
  exact (hP.conjTranspose_mul_mul_same K).trace_mul_re_nonneg hσ

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype Mem] [DecidableEq Mem] in
theorem diag_re_nonneg {σ : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ}
    (hσ : σ.PosSemidef) (s : Unit × HwReg X₁ Z₁ Mem) : 0 ≤ (σ s s).re :=
  (Complex.nonneg_iff.1 hσ.diag_nonneg).1

omit [DecidableEq Mem] in
theorem posSemidef_conjK (K : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ)
    {σ : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ} (hσ : σ.PosSemidef) :
    (MatrixMap.conj K σ).PosSemidef := by
  rw [MatrixMap.conj_apply]
  exact hσ.mul_mul_conjTranspose_same K

variable [AddCommGroup X₁] [AddCommGroup Z₁] [Nonempty X₁] [Nonempty Z₁]

/-! ### The cells of a trial -/

/-- The value of the `k`-cell `x` of a register state: the hardwired one, else the recorded one. -/
def kValG (x : X₁) (d : HwReg X₁ Z₁ Mem) : Option Z₁ :=
  (d.2.1.2.1 x).or (d.1.2.1 x)

/-- The value of the `k'`-cell `y` of a register state: the hardwired one, else the recorded
one. -/
def k'ValG (y : X₁) (d : HwReg X₁ Z₁ Mem) : Option Z₁ :=
  (d.2.1.2.2 y).or (d.1.2.2 y)

/-- The states whose `h`-cell `z` is hidden and not hardwired (TrialSource's `hSet`). -/
def hSetG (Hh : Set Z₁) (z : Z₁) : Set (HwReg X₁ Z₁ Mem) :=
  {d | z ∈ Hh ∧ d.2.1.1 z = none}

/-- The states whose `k'`-cell `y` is hidden and not hardwired (TrialSource's `k'Set`). -/
def k'SetG (Hk' : Set X₁) (y : X₁) : Set (HwReg X₁ Z₁ Mem) :=
  {d | y ∈ Hk' ∧ d.2.1.2.2 y = none}

/-- The states whose `k'`-cell `y` holds a value `w` with the `h`-cell `z₀ + w` hidden and not
hardwired. -/
def e2At (Hh : Set Z₁) (y : X₁) (z₀ : Z₁) : Set (HwReg X₁ Z₁ Mem) :=
  {d | ∃ w, k'ValG y d = some w ∧ d ∈ hSetG Hh (z₀ + w)}

variable (π : Equiv.Perm (X₁ × Z₁)) (Hh : Set Z₁) (Hk' : Set X₁) (x : X₁)

/-- **Sources through the `k'`-cell**: the `k`-cell `x` holds `a` and the trial's `k'`-cell
`π (x, a)` is hidden and not hardwired. -/
def srcK' : Set (HwReg X₁ Z₁ Mem) :=
  {d | ∃ a, kValG x d = some a ∧ d ∈ k'SetG Hk' (π (x, a)).1}

/-- **Sources through the `h`-cell**: the `k`-cell `x` holds `a`, the trial's `k'`-cell holds a
value and the `h`-cell after it is hidden and not hardwired. -/
def srcH : Set (HwReg X₁ Z₁ Mem) :=
  {d | ∃ a, kValG x d = some a ∧ d ∈ e2At Hh (π (x, a)).1 (π (x, a)).2}

/-- **Sources of an empty `k`-cell**: the `k`-cell `x` is empty, the trial's `k'`-cell at the
outcome `a` holds a value and the `h`-cell after it is hidden and not hardwired. -/
def srcHE (a : Z₁) : Set (HwReg X₁ Z₁ Mem) :=
  {d | kValG x d = none ∧ d ∈ e2At Hh (π (x, a)).1 (π (x, a)).2}

/-- The states whose `k`-cell `x` holds a value. -/
def baseK : Set (HwReg X₁ Z₁ Mem) :=
  {d | kValG x d ≠ none}

/-- The states whose trial `k'`-cell at the outcome `a` holds a value. -/
def baseK' (a : Z₁) : Set (HwReg X₁ Z₁ Mem) :=
  {d | k'ValG (π (x, a)).1 d ≠ none}

/-- **The diagonal bound of a trial's `k`-read at `x`**: the fresh part `(2 cK + 4 cH) / |Z|`, four
times the sources of a filled `k`-cell, `4 / |Z|` times those of an empty one per outcome. -/
noncomputable def trialDiag (cK cH : ℝ) (s : Unit × HwReg X₁ Z₁ Mem) : ℝ :=
  (2 * cK + 4 * cH) / Fintype.card Z₁ + 4 * (srcK' π Hk' x).indicator 1 s.2 +
    4 * (srcH π Hh x).indicator 1 s.2 +
    4 / Fintype.card Z₁ * ∑ a, (srcHE π Hh x a).indicator 1 s.2

/-- The weight of the `k'`-read's outcome: the `h`-cell `z₀ + o` hidden and not hardwired. -/
noncomputable def wIn (y : X₁) (z₀ : Z₁) (o : Option Z₁) (r : RestK X₁ Z₁ Mem y) : ℝ :=
  (hSetG Hh (z₀ + o.getD 0)).indicator 1 ((splitK' y).symm (none, r)).2

/-- The diagonal bound after the `k`-read with outcome `a`. -/
noncomputable def gOut (cH : ℝ) (a : Z₁) (s : Unit × HwReg X₁ Z₁ Mem) : ℝ :=
  (k'SetG Hk' (π (x, a)).1).indicator 1 s.2 +
    (2 * (e2At Hh (π (x, a)).1 (π (x, a)).2).indicator 1 s.2 + 2 * cH / Fintype.card Z₁)

/-- The weight of the `k`-read's outcome. -/
noncomputable def qOut (cH : ℝ) (o : Option Z₁) (r : RestK X₁ Z₁ Mem x) : ℝ :=
  gOut π Hh Hk' x cH (o.getD 0) ((splitK x).symm (none, r))

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype Mem] [DecidableEq Mem]
  [AddCommGroup X₁] [AddCommGroup Z₁] [Nonempty X₁] [Nonempty Z₁] in
theorem mem_srcK'_iff {π : Equiv.Perm (X₁ × Z₁)} {Hk' : Set X₁} {x : X₁} {d : HwReg X₁ Z₁ Mem}
    {a : Z₁} (hk : kValG x d = some a) : d ∈ srcK' π Hk' x ↔ d ∈ k'SetG Hk' (π (x, a)).1 :=
  ⟨fun ⟨a', ha', h⟩ ↦ by rw [hk] at ha'; cases ha'; exact h, fun h ↦ ⟨a, hk, h⟩⟩

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype Mem] [DecidableEq Mem]
  [AddCommGroup X₁] [Nonempty X₁] [Nonempty Z₁] in
theorem mem_srcH_iff {π : Equiv.Perm (X₁ × Z₁)} {Hh : Set Z₁} {x : X₁} {d : HwReg X₁ Z₁ Mem}
    {a : Z₁} (hk : kValG x d = some a) :
    d ∈ srcH π Hh x ↔ d ∈ e2At Hh (π (x, a)).1 (π (x, a)).2 :=
  ⟨fun ⟨a', ha', h⟩ ↦ by rw [hk] at ha'; cases ha'; exact h, fun h ↦ ⟨a, hk, h⟩⟩

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype Mem] [DecidableEq Mem]
  [AddCommGroup X₁] [Nonempty X₁] [Nonempty Z₁] in
theorem mem_srcHE_iff {π : Equiv.Perm (X₁ × Z₁)} {Hh : Set Z₁} {x : X₁} {d : HwReg X₁ Z₁ Mem}
    (hk : kValG x d = none) (a : Z₁) :
    d ∈ srcHE π Hh x a ↔ d ∈ e2At Hh (π (x, a)).1 (π (x, a)).2 :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨hk, h⟩⟩

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype Mem] [DecidableEq Mem]
  [AddCommGroup X₁] [AddCommGroup Z₁] [Nonempty X₁] [Nonempty Z₁] in
theorem ind_hSetG_le (Hh : Set Z₁) (z : Z₁) (d : HwReg X₁ Z₁ Mem) :
    (hSetG Hh z).indicator 1 d ≤ Hh.indicator (1 : Z₁ → ℝ) z :=
  ind_le_ind fun h ↦ h.1

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype Mem] [DecidableEq Mem]
  [AddCommGroup X₁] [AddCommGroup Z₁] [Nonempty X₁] [Nonempty Z₁] in
theorem ind_k'SetG_le (Hk' : Set X₁) (y : X₁) (d : HwReg X₁ Z₁ Mem) :
    (k'SetG Hk' y).indicator 1 d ≤ Hk'.indicator (1 : X₁ → ℝ) y :=
  ind_le_ind fun h ↦ h.1

/-! ### No decompressed `⊥` after the `k`-read -/

omit [Nonempty X₁] in
theorem noBot_conj_readK (r : Option Z₁ × Mem)
    {σ : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ}
    (hnb : QuerySupportedOn (fun m : Unit × HwReg X₁ Z₁ Mem ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X₁ Z₁ Mem) σ)) :
    QuerySupportedOn (fun m : Unit × HwReg X₁ Z₁ Mem ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X₁ Z₁ Mem)
        (MatrixMap.conj (hwReadKraus (.readK x (fun m _ ↦ m)) r) σ)) := by
  set U : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ :=
    (1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X₁ Z₁ Mem with hUdef
  have hU : U * U = 1 := by
    rw [hUdef, ← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self, one_kronecker_one]
  have hUh : Uᴴ = U := by
    rw [hUdef, conjTranspose_kronecker, conjTranspose_one, conjTranspose_compressReg]
  set K := hwReadKraus (.readK x (fun (m : Mem) (_ : Option Z₁) ↦ m)) r with hK
  have e : MatrixMap.conj U (MatrixMap.conj K σ) =
      MatrixMap.conj (U * K * U) (MatrixMap.conj U σ) := by
    simp only [MatrixMap.conj_apply, conjTranspose_mul, hUh, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc U U, hU, Matrix.one_mul]
  rw [e]
  refine QuerySupportedOn.conj hnb fun m' m hK' hm ↦ ?_
  exact noBot_of_clsKraus _ _ _ (fun b ↦ keepsNoBot_of_cells cellKeeps_compressAll_one
    (cellKeeps_compressAll_cellRead _ _ _) cellKeeps_compressAll_one) m' m hK' hm

/-! ### The `k'`-read: the inner bound -/

omit [Fintype Mem] [AddCommGroup X₁] [Nonempty X₁] [Nonempty Z₁] in
theorem wDiag_wIn (y : X₁) (z₀ : Z₁) (o : Option Z₁) :
    wDiag (splitK' (Z₁ := Z₁) (M := Mem) y) (wIn Hh y z₀) o =
      (1 : Matrix Unit Unit ℂ) ⊗ₖ setProj (hSetG Hh (z₀ + o.getD 0)) := by
  rw [kron_setProjG, wDiag]
  refine congrArg diagonal (funext fun t ↦ ?_)
  rw [wIn, splitK'_symm_fill]
  exact congrArg (fun r : ℝ ↦ (r : ℂ)) (ind_eq_ind Iff.rfl)

omit [Fintype X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype Mem] [DecidableEq Mem] [AddCommGroup X₁]
  [Nonempty X₁] [Nonempty Z₁] in
theorem wIn_nonneg (y : X₁) (z₀ : Z₁) (o : Option Z₁) (r : RestK X₁ Z₁ Mem y) :
    0 ≤ wIn Hh y z₀ o r :=
  ind_nonneg _ _

omit [Fintype X₁] [DecidableEq Z₁] [Fintype Mem] [DecidableEq Mem] [AddCommGroup X₁]
  [Nonempty X₁] in
/-- The inner diagonal bound of the `k'`-read at `y` before the `h`-cell `z₀ + w`. -/
theorem cB_wIn_le (y : X₁) (z₀ : Z₁) (cH : ℝ)
    (hcH : ∑ w : Z₁, Hh.indicator (1 : Z₁ → ℝ) (z₀ + w) ≤ cH) (s : Unit × HwReg X₁ Z₁ Mem) :
    cB (splitK' y) (actK' y) (tauK y (fun m _ ↦ m)) (idxK' y) (phiK' y (fun m _ ↦ m))
        (wIn Hh y z₀) s ≤
      2 * (e2At Hh y z₀).indicator 1 s.2 + 2 * cH / Fintype.card Z₁ := by
  have hcH0 : 0 ≤ cH := nonneg_of_sum_ind_le _ hcH
  have hN : (0 : ℝ) < Fintype.card Z₁ := Nat.cast_pos.2 Fintype.card_pos
  have hc : 0 ≤ 2 * cH / Fintype.card Z₁ := by positivity
  have he2 : ∀ w, k'ValG y s.2 = some w →
      (hSetG Hh (z₀ + w)).indicator 1 s.2 ≤
        (e2At Hh y z₀).indicator (1 : HwReg X₁ Z₁ Mem → ℝ) s.2 :=
    fun w hw ↦ ind_le_ind fun h ↦ ⟨w, hw, h⟩
  unfold cB
  split_ifs with hact
  · have hhw : s.2.2.1.2.2 y = none := hact
    rcases hd : s.2.1.2.2 y with _ | w
    · have h1 : (splitK' y s).1 = none := hd
      rw [h1, Option.elim_none]
      have hle : ∑ w : Z₁, wIn Hh y z₀ (some w) (tauK y (fun m _ ↦ m) (some w) (splitK' y s).2)
          ≤ cH := by
        refine le_trans (Finset.sum_le_sum fun w _ ↦ ?_) hcH
        exact ind_hSetG_le Hh _ _
      have h2 : 2 / (Fintype.card Z₁ : ℝ) * ∑ w : Z₁,
          wIn Hh y z₀ (some w) (tauK y (fun m _ ↦ m) (some w) (splitK' y s).2) ≤
          2 * cH / Fintype.card Z₁ := by
        rw [div_mul_eq_mul_div]
        gcongr
      have h3 := ind_nonneg (e2At Hh y z₀) s.2
      linarith
    · have h1 : (splitK' y s).1 = some w := hd
      rw [h1, Option.elim_some]
      have hw : k'ValG y s.2 = some w := by
        show (s.2.2.1.2.2 y).or (s.2.1.2.2 y) = some w
        rw [hhw, hd]
        rfl
      have h2 : wIn Hh y z₀ (some w) (tauK y (fun m _ ↦ m) (some w) (splitK' y s).2) =
          (hSetG Hh (z₀ + w)).indicator 1 s.2 := by
        show (hSetG Hh (z₀ + w)).indicator 1 ((splitK' y).symm (none, (splitK' y s).2)).2 = _
        rw [splitK'_symm_fill]
        exact ind_eq_ind Iff.rfl
      rw [h2]
      linarith [he2 w hw]
  · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp (show s.2.2.1.2.2 y ≠ none from hact)
    have h1 : (idxK' y s).1 = some w := hw
    have hv : k'ValG y s.2 = some w := by
      show (s.2.2.1.2.2 y).or (s.2.1.2.2 y) = some w
      rw [hw]
      rfl
    have h2 : wIn Hh y z₀ (idxK' y s).1 (splitK' y (phiK' y (fun m _ ↦ m) s)).2 =
        (hSetG Hh (z₀ + w)).indicator 1 s.2 := by
      rw [h1]
      show (hSetG Hh (z₀ + w)).indicator 1 ((splitK' y).symm (none, (splitK' y s).2)).2 = _
      rw [splitK'_symm_fill]
      exact ind_eq_ind Iff.rfl
    rw [h2]
    linarith [he2 w hv, ind_nonneg (hSetG Hh (z₀ + w)) s.2]

omit [AddCommGroup X₁] [Nonempty X₁] in
/-- **The `k'`-read and the `h`-cell after it**: at most `2` on a hidden `h`-cell after a value
of the `k'`-cell, and `2 cH / |Z|` on an empty `k'`-cell. -/
theorem sum_potential_inner_le (y : X₁) (z₀ : Z₁) (cH : ℝ)
    (hcH : ∑ w : Z₁, Hh.indicator (1 : Z₁ → ℝ) (z₀ + w) ≤ cH)
    {σ : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitK' y) (actK' y) σ) :
    ∑ r : Option Z₁ × Mem, potential (setProj (hSetG Hh (z₀ + r.1.getD 0)) *
        readKrausK' y (fun m _ ↦ m) r) σ ≤
      ENNReal.ofReal (∑ s, (2 * (e2At Hh y z₀).indicator 1 s.2 + 2 * cH / Fintype.card Z₁) *
        (σ s s).re) := by
  set K : Option Z₁ × Mem → Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ :=
    fun r ↦ hwReadKraus (.readK' y (fun (m : Mem) (_ : Option Z₁) ↦ m)) r with hKdef
  have hterm : ∀ r : Option Z₁ × Mem, potential (setProj (hSetG Hh (z₀ + r.1.getD 0)) *
      readKrausK' y (fun m _ ↦ m) r) σ =
      ENNReal.ofReal (((K r)ᴴ * wDiag (splitK' y) (wIn Hh y z₀) r.1 * K r * σ).trace.re) := by
    intro r
    rw [potential_setProj_mul_eqG, wDiag_wIn]
    rfl
  have hnn : ∀ r ∈ (Finset.univ : Finset (Option Z₁ × Mem)),
      0 ≤ ((K r)ᴴ * wDiag (splitK' y) (wIn Hh y z₀) r.1 * K r * σ).trace.re := by
    intro r _
    rw [wDiag]
    exact re_trace_kraus_diag_nonneg _ (fun _ ↦ wIn_nonneg Hh y z₀ _ _) _ hσ
  simp only [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsum : ∑ r, ((K r)ᴴ * wDiag (splitK' y) (wIn Hh y z₀) r.1 * K r * σ).trace.re =
      ((∑ r, (K r)ᴴ * wDiag (splitK' y) (wIn Hh y z₀) r.1 * K r) * σ).trace.re := by
    rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  rw [hsum]
  refine (re_trace_gramQ_le (cellRead_readK' y (fun m _ ↦ m)) (clsOff_readK' y (fun m _ ↦ m))
    (wIn Hh y z₀) (wIn_nonneg Hh y z₀) hσ hnb).trans
    (Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_right ?_ (diag_re_nonneg hσ s))
  exact cB_wIn_le Hh y z₀ cH hcH s

/-! ### The `k`-read: the outer bound -/

omit [Fintype X₁] [DecidableEq Z₁] [Fintype Mem] [DecidableEq Mem] [AddCommGroup X₁] [Nonempty X₁]
  [Nonempty Z₁] in
theorem gOut_splitK (cH : ℝ) (a : Z₁) (t : Unit × HwReg X₁ Z₁ Mem) :
    gOut π Hh Hk' x cH a ((splitK x).symm (none, (splitK x t).2)) = gOut π Hh Hk' x cH a t := by
  rw [splitK_symm_fill]
  exact congrArg₂ (· + ·) (ind_eq_ind Iff.rfl)
    (congrArg (fun r ↦ 2 * r + 2 * cH / Fintype.card Z₁) (ind_eq_ind Iff.rfl))

omit [Fintype Mem] [AddCommGroup X₁] [Nonempty X₁] [Nonempty Z₁] in
theorem wDiag_qOut (cH : ℝ) (o : Option Z₁) :
    wDiag (splitK (Z₁ := Z₁) (M := Mem) x) (qOut π Hh Hk' x cH) o =
      diagonal fun t ↦ ((gOut π Hh Hk' x cH (o.getD 0) t : ℝ) : ℂ) := by
  rw [wDiag]
  refine congrArg diagonal (funext fun t ↦ ?_)
  rw [qOut, gOut_splitK]

omit [Fintype X₁] [DecidableEq X₁] [DecidableEq Z₁] [Fintype Mem] [DecidableEq Mem]
  [AddCommGroup X₁] [Nonempty X₁] [Nonempty Z₁] in
theorem gOut_nonneg (cH : ℝ) (hcH : 0 ≤ cH) (a : Z₁) (t : Unit × HwReg X₁ Z₁ Mem) :
    0 ≤ gOut π Hh Hk' x cH a t := by
  unfold gOut
  have h1 := ind_nonneg (k'SetG Hk' (π (x, a)).1) t.2
  have h2 := ind_nonneg (e2At Hh (π (x, a)).1 (π (x, a)).2) t.2
  have h3 : 0 ≤ 2 * cH / (Fintype.card Z₁ : ℝ) := by positivity
  linarith

omit [Fintype X₁] [DecidableEq X₁] [DecidableEq Z₁] [Fintype Mem] [DecidableEq Mem]
  [AddCommGroup X₁] [Nonempty X₁] [Nonempty Z₁] in
theorem gOut_eq_of_kVal (cH : ℝ) {a : Z₁} {t : Unit × HwReg X₁ Z₁ Mem} (hk : kValG x t.2 = some a) :
    gOut π Hh Hk' x cH a t = (srcK' π Hk' x).indicator 1 t.2 +
      (2 * (srcH π Hh x).indicator 1 t.2 + 2 * cH / Fintype.card Z₁) := by
  unfold gOut
  rw [ind_eq_ind (mem_srcK'_iff hk).symm, ind_eq_ind (mem_srcH_iff hk).symm]

omit [Fintype X₁] [DecidableEq Z₁] [Fintype Mem] [DecidableEq Mem] [AddCommGroup X₁]
  [Nonempty X₁] in
/-- The outer diagonal bound of the `k`-read at `x`, pointwise. -/
theorem cB_qOut_le (cK cH : ℝ) (hcK : ∑ a : Z₁, Hk'.indicator (1 : X₁ → ℝ) (π (x, a)).1 ≤ cK)
    (hcH0 : 0 ≤ cH) (s : Unit × HwReg X₁ Z₁ Mem) :
    cB (splitK x) (actK x) (tauK x (fun m _ ↦ m)) (idxK x) (phiK x (fun m _ ↦ m))
      (qOut π Hh Hk' x cH) s ≤ trialDiag π Hh Hk' x cK cH s := by
  have hcK0 : 0 ≤ cK := nonneg_of_sum_ind_le _ hcK
  have hN : (0 : ℝ) < Fintype.card Z₁ := Nat.cast_pos.2 Fintype.card_pos
  have hs1 := ind_nonneg (srcK' π Hk' x) s.2
  have hs2 := ind_nonneg (srcH π Hh x) s.2
  have hs3 : 0 ≤ 4 / (Fintype.card Z₁ : ℝ) * ∑ a, (srcHE π Hh x a).indicator 1 s.2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ ↦ ind_nonneg _ _)
  have hcN : 2 * cH / (Fintype.card Z₁ : ℝ) ≤ (2 * cK + 4 * cH) / Fintype.card Z₁ := by
    gcongr
    linarith
  have hcN2 : 2 * (2 * cH / (Fintype.card Z₁ : ℝ)) ≤ (2 * cK + 4 * cH) / Fintype.card Z₁ := by
    rw [mul_div_assoc']
    gcongr
    linarith
  unfold cB
  split_ifs with hact
  · have hhw : s.2.2.1.2.1 x = none := hact
    rcases hd : s.2.1.2.1 x with _ | a
    · have h1 : (splitK x s).1 = none := hd
      have hk : kValG x s.2 = none := by
        show (s.2.2.1.2.1 x).or (s.2.1.2.1 x) = none
        rw [hhw, hd]
        rfl
      rw [h1, Option.elim_none]
      have hq : ∀ a, qOut π Hh Hk' x cH (some a) (tauK x (fun m _ ↦ m) (some a) (splitK x s).2) =
          gOut π Hh Hk' x cH a s := fun a ↦ gOut_splitK π Hh Hk' x cH a s
      simp only [hq]
      have hNN : (Fintype.card Z₁ : ℝ) * (2 * cH / Fintype.card Z₁) = 2 * cH := by
        field_simp
      have hsum : ∑ a, gOut π Hh Hk' x cH a s ≤
          cK + (2 * ∑ a, (srcHE π Hh x a).indicator 1 s.2 + 2 * cH) := by
        unfold gOut
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, hNN]
        refine add_le_add ((Finset.sum_le_sum fun a _ ↦ ind_k'SetG_le Hk' _ s.2).trans hcK)
          (le_of_eq ?_)
        rw [Finset.sum_congr rfl fun a _ ↦ ind_eq_ind (mem_srcHE_iff hk a).symm]
      calc 2 / (Fintype.card Z₁ : ℝ) * ∑ a, gOut π Hh Hk' x cH a s
          ≤ 2 / (Fintype.card Z₁ : ℝ) *
            (cK + (2 * ∑ a, (srcHE π Hh x a).indicator 1 s.2 + 2 * cH)) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (2 * cK + 4 * cH) / Fintype.card Z₁ +
            4 / Fintype.card Z₁ * ∑ a, (srcHE π Hh x a).indicator 1 s.2 := by ring
        _ ≤ trialDiag π Hh Hk' x cK cH s := by
            unfold trialDiag
            linarith
    · have h1 : (splitK x s).1 = some a := hd
      have hk : kValG x s.2 = some a := by
        show (s.2.2.1.2.1 x).or (s.2.1.2.1 x) = some a
        rw [hhw, hd]
        rfl
      rw [h1, Option.elim_some]
      show 2 * gOut π Hh Hk' x cH a ((splitK x).symm (none, (splitK x s).2)) ≤ _
      rw [gOut_splitK, gOut_eq_of_kVal π Hh Hk' x cH hk]
      unfold trialDiag
      linarith
  · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (show s.2.2.1.2.1 x ≠ none from hact)
    have hk : kValG x s.2 = some a := by
      show (s.2.2.1.2.1 x).or (s.2.1.2.1 x) = some a
      rw [ha]
      rfl
    have h1 : (idxK x s).1 = some a := ha
    rw [h1]
    show gOut π Hh Hk' x cH a ((splitK x).symm (none, (splitK x s).2)) ≤ _
    rw [gOut_splitK, gOut_eq_of_kVal π Hh Hk' x cH hk]
    unfold trialDiag
    linarith

/-- **A trial's `k`-read with the `k'`- and `h`-reads after it** (TrialSource's `trialW` at a
`k`-read): at most the diagonal bound `trialDiag` of the input state. -/
theorem sum_potential_trial_le (cK cH : ℝ)
    (hcK : ∑ a : Z₁, Hk'.indicator (1 : X₁ → ℝ) (π (x, a)).1 ≤ cK)
    (hcH : ∀ z : Z₁, ∑ w : Z₁, Hh.indicator (1 : Z₁ → ℝ) (z + w) ≤ cH)
    {σ : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ} (hσ : σ.PosSemidef)
    (hnb : QuerySupportedOn (fun m : Unit × HwReg X₁ Z₁ Mem ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X₁ Z₁ Mem) σ)) :
    ∑ r : Option Z₁ × Mem, (potential (setProj (k'SetG Hk' (π (x, r.1.getD 0)).1))
        (MatrixMap.conj (hwReadKraus (.readK x (fun m _ ↦ m)) r) σ) +
      ∑ r' : Option Z₁ × Mem,
        potential (setProj (hSetG Hh ((π (x, r.1.getD 0)).2 + r'.1.getD 0)) *
          readKrausK' (π (x, r.1.getD 0)).1 (fun m _ ↦ m) r')
        (MatrixMap.conj (hwReadKraus (.readK x (fun m _ ↦ m)) r) σ)) ≤
      ENNReal.ofReal (∑ s, trialDiag π Hh Hk' x cK cH s * (σ s s).re) := by
  have hcH0 : 0 ≤ cH := nonneg_of_sum_ind_le _ (hcH 0)
  have hper : ∀ r : Option Z₁ × Mem,
      potential (setProj (k'SetG Hk' (π (x, r.1.getD 0)).1))
          (MatrixMap.conj (hwReadKraus (.readK x (fun m _ ↦ m)) r) σ) +
        ∑ r' : Option Z₁ × Mem,
          potential (setProj (hSetG Hh ((π (x, r.1.getD 0)).2 + r'.1.getD 0)) *
            readKrausK' (π (x, r.1.getD 0)).1 (fun m _ ↦ m) r')
          (MatrixMap.conj (hwReadKraus (.readK x (fun m _ ↦ m)) r) σ) ≤
        ENNReal.ofReal (((hwReadKraus (.readK x (fun m _ ↦ m)) r)ᴴ *
          wDiag (splitK x) (qOut π Hh Hk' x cH) r.1 * hwReadKraus (.readK x (fun m _ ↦ m)) r *
            σ).trace.re) := by
    intro r
    have hσr := posSemidef_conjK (hwReadKraus (.readK x (fun (m : Mem) (_ : Option Z₁) ↦ m)) r) hσ
    have hnbr : CellNoBot (splitK' (π (x, r.1.getD 0)).1) (actK' (π (x, r.1.getD 0)).1)
        (MatrixMap.conj (hwReadKraus (.readK x (fun (m : Mem) (_ : Option Z₁) ↦ m)) r) σ) :=
      readNoBot_of_noBot (.readK' (π (x, r.1.getD 0)).1 (fun m _ ↦ m)) (noBot_conj_readK x r hnb)
    rw [potential_setProj_eq_sum, wDiag_qOut,
      ← re_trace_diag_conj (fun t ↦ gOut π Hh Hk' x cH (r.1.getD 0) t)]
    refine (add_le_add le_rfl (sum_potential_inner_le Hh _ _ cH (hcH _) hσr hnbr)).trans ?_
    have hc : 0 ≤ 2 * cH / (Fintype.card Z₁ : ℝ) := by positivity
    rw [← ENNReal.ofReal_add (Finset.sum_nonneg fun s _ ↦
      mul_nonneg (ind_nonneg _ _) (diag_re_nonneg hσr s)) (Finset.sum_nonneg fun s _ ↦
      mul_nonneg (add_nonneg (mul_nonneg zero_le_two (ind_nonneg _ _)) hc)
        (diag_re_nonneg hσr s)), ← Finset.sum_add_distrib]
    refine le_of_eq (congrArg ENNReal.ofReal (Finset.sum_congr rfl fun s _ ↦ ?_))
    unfold gOut
    ring
  have hnn : ∀ r ∈ (Finset.univ : Finset (Option Z₁ × Mem)),
      0 ≤ ((hwReadKraus (.readK x (fun m _ ↦ m)) r)ᴴ *
        wDiag (splitK x) (qOut π Hh Hk' x cH) r.1 * hwReadKraus (.readK x (fun m _ ↦ m)) r *
          σ).trace.re := by
    intro r _
    rw [wDiag_qOut]
    exact re_trace_kraus_diag_nonneg _ (gOut_nonneg π Hh Hk' x cH hcH0 _) _ hσ
  refine (Finset.sum_le_sum fun r _ ↦ hper r).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul]
  refine (re_trace_gramQ_le (cellRead_readK x (fun m _ ↦ m)) (clsOff_readK x (fun m _ ↦ m))
    (qOut π Hh Hk' x cH) (fun o _ ↦ gOut_nonneg π Hh Hk' x cH hcH0 _ _) hσ
    (readNoBot_of_noBot (.readK x (fun m _ ↦ m)) hnb)).trans
    (Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_right ?_ (diag_re_nonneg hσ s))
  exact cB_qOut_le π Hh Hk' x cK cH hcK hcH0 s

/-! ### The diagonal bound as masses -/

omit [DecidableEq Mem] [AddCommGroup X₁] [AddCommGroup Z₁] [Nonempty X₁] [Nonempty Z₁] in
theorem diagMass_snd_eq (S : Set (HwReg X₁ Z₁ Mem))
    {σ : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ} (hσ : σ.PosSemidef) :
    diagMass {p : Unit × HwReg X₁ Z₁ Mem | p.2 ∈ S} σ =
      ENNReal.ofReal (∑ s, S.indicator 1 s.2 * (σ s s).re) := by
  rw [diagMass, ENNReal.ofReal_sum_of_nonneg fun s _ ↦
    mul_nonneg (ind_nonneg _ _) (diag_re_nonneg hσ s)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases h : s.2 ∈ S
  · rw [Set.indicator_of_mem (show s ∈ {p : Unit × HwReg X₁ Z₁ Mem | p.2 ∈ S} from h),
      Set.indicator_of_mem h, Pi.one_apply, one_mul]
  · rw [Set.indicator_of_notMem (show s ∉ {p : Unit × HwReg X₁ Z₁ Mem | p.2 ∈ S} from h),
      Set.indicator_of_notMem h, zero_mul, ENNReal.ofReal_zero]

omit [DecidableEq Mem] [AddCommGroup X₁] [Nonempty X₁] [Nonempty Z₁] in
/-- **The diagonal bound as masses**: the fresh part times the trace, four times the masses of the
sources of a filled `k`-cell, `4 / |Z|` times those of an empty one per outcome. -/
theorem ofReal_trialDiag_eq (cK cH : ℝ) (hcK : 0 ≤ cK) (hcH : 0 ≤ cH)
    {σ : Matrix (Unit × HwReg X₁ Z₁ Mem) (Unit × HwReg X₁ Z₁ Mem) ℂ} (hσ : σ.PosSemidef) :
    ENNReal.ofReal (∑ s, trialDiag π Hh Hk' x cK cH s * (σ s s).re) =
      ENNReal.ofReal ((2 * cK + 4 * cH) / Fintype.card Z₁) * ENNReal.ofReal σ.trace.re +
        4 * diagMass {p : Unit × HwReg X₁ Z₁ Mem | p.2 ∈ srcK' π Hk' x} σ +
        4 * diagMass {p : Unit × HwReg X₁ Z₁ Mem | p.2 ∈ srcH π Hh x} σ +
        ∑ a, ENNReal.ofReal (4 / Fintype.card Z₁) *
          diagMass {p : Unit × HwReg X₁ Z₁ Mem | p.2 ∈ srcHE π Hh x a} σ := by
  have hN : (0 : ℝ) < Fintype.card Z₁ := Nat.cast_pos.2 Fintype.card_pos
  have hF : 0 ≤ (2 * cK + 4 * cH) / (Fintype.card Z₁ : ℝ) := by positivity
  have h4 : (0 : ℝ) ≤ 4 / Fintype.card Z₁ := by positivity
  have hd := diag_re_nonneg hσ
  have hB : ∀ S : Set (HwReg X₁ Z₁ Mem), 0 ≤ ∑ s, S.indicator 1 s.2 * (σ s s).re :=
    fun S ↦ Finset.sum_nonneg fun s _ ↦ mul_nonneg (ind_nonneg _ _) (hd s)
  have htr0 : 0 ≤ ∑ s, (σ s s).re := Finset.sum_nonneg fun s _ ↦ hd s
  have htr : σ.trace.re = ∑ s, (σ s s).re := by
    rw [Matrix.trace, Complex.re_sum]
    rfl
  have hsplit : ∑ s, trialDiag π Hh Hk' x cK cH s * (σ s s).re =
      (2 * cK + 4 * cH) / Fintype.card Z₁ * ∑ s, (σ s s).re +
        4 * ∑ s, (srcK' π Hk' x).indicator 1 s.2 * (σ s s).re +
        4 * ∑ s, (srcH π Hh x).indicator 1 s.2 * (σ s s).re +
        ∑ a, 4 / Fintype.card Z₁ * ∑ s, (srcHE π Hh x a).indicator 1 s.2 * (σ s s).re := by
    simp only [trialDiag, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
      mul_assoc]
    rw [Finset.sum_comm (f := fun s a ↦ 4 / (Fintype.card Z₁ : ℝ) *
      ((srcHE π Hh x a).indicator 1 s.2 * (σ s s).re))]
  rw [hsplit, ENNReal.ofReal_add (add_nonneg (add_nonneg (mul_nonneg hF htr0)
      (mul_nonneg zero_le_four (hB _))) (mul_nonneg zero_le_four (hB _)))
      (Finset.sum_nonneg fun a _ ↦ mul_nonneg h4 (hB _)),
    ENNReal.ofReal_add (add_nonneg (mul_nonneg hF htr0) (mul_nonneg zero_le_four (hB _)))
      (mul_nonneg zero_le_four (hB _)),
    ENNReal.ofReal_add (mul_nonneg hF htr0) (mul_nonneg zero_le_four (hB _)),
    ENNReal.ofReal_mul hF, ENNReal.ofReal_mul zero_le_four, ENNReal.ofReal_mul zero_le_four,
    ENNReal.ofReal_sum_of_nonneg fun a _ ↦ mul_nonneg h4 (hB _), ENNReal.ofReal_ofNat, htr]
  simp only [diagMass_snd_eq _ hσ, ENNReal.ofReal_mul h4]

end generic

/-! ## Disclose's view lemma with a base set -/

section baseView

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)]

/-- **The pointwise count with a base set** (`sum_agree_diagMass_le` with the masses of the
states of the base `B ⊇ C u` labelled `T` on the right). -/
theorem sum_agree_diagMass_le_base [∀ s, Nonempty (D s)] {α : Type} [Fintype α] [DecidableEq α]
    (lab : α → Finset S) (T : Finset S) (v : (s : S) → D s) (C : ((s : S) → D s) → Set α)
    (B : Set α) (hCB : ∀ u, C u ⊆ B)
    (srcs : α → Finset S) (F : α → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ a s u d, F a s (Function.update u s d) = F a s u)
    (hsrc : ∀ u a, a ∈ C u → ∃ s ∈ srcs a, s ∉ lab a ∧ u s ∈ F a s u) (κ : ℝ≥0∞)
    (hκ : ∀ a u, ∑ s ∈ srcs a,
      ((F a s u).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ) (σ : Matrix α α ℂ) :
    ∑ u, (if Agree T v u then diagMass (C u ∩ {a | lab a = T}) σ else 0) ≤
      κ * (∑ u, if Agree T v u then (1 : ℝ≥0∞) else 0) * diagMass (B ∩ {a | lab a = T}) σ := by
  classical
  set σ' : Matrix α α ℂ := diagonal fun a ↦ if a ∈ B then σ a a else 0 with hσ'
  have hC : ∀ u, diagMass (C u ∩ {a | lab a = T}) σ = diagMass (C u ∩ {a | lab a = T}) σ' := by
    intro u
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    by_cases ha : a ∈ C u ∩ {a | lab a = T}
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, hσ', diagonal_apply_eq,
        ite_eq_left (hCB u ha.1)]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]
  have hB : diagMass {a | lab a = T} σ' = diagMass (B ∩ {a | lab a = T}) σ := by
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    by_cases hl : a ∈ {a | lab a = T}
    · rw [Set.indicator_of_mem hl, hσ', diagonal_apply_eq]
      by_cases hb : a ∈ B
      · rw [ite_eq_left hb,
          Set.indicator_of_mem (show a ∈ B ∩ {a | lab a = T} from ⟨hb, hl⟩)]
      · rw [ite_eq_right hb, Set.indicator_of_notMem fun h ↦ hb h.1, Complex.zero_re,
          ENNReal.ofReal_zero]
    · rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem fun h ↦ hl h.2]
  simp only [hC]
  rw [← hB]
  exact sum_agree_diagMass_le lab T v C srcs F hF hsrc κ hκ σ'

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

/-- **`sum_queryWeight_cut_le` with a base set**: the masses at the states labelled `T` of the
sets `C v ⊆ B` are at most `κ` times those of `B`. -/
theorem sum_queryWeight_cut_le_base [∀ s, Nonempty (D s)] (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (P : spec.Port → Prop) (hview : ViewByOn R I P lab x ρ j)
    (C : ((s : S) → D s) → ∀ i, Set (spec.In i × R.D)) (B : ∀ i, Set (spec.In i × R.D))
    (hCP : ∀ v i, ¬ P i → C v i = ∅) (hCB : ∀ v i, C v i ⊆ B i)
    (srcs : ∀ i, spec.In i × R.D → Finset S)
    (F : ∀ i, spec.In i × R.D → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ i p s v d, F i p s (Function.update v s d) = F i p s v)
    (hsrc : ∀ v i p, p ∈ C v i → ∃ s ∈ srcs i p, s ∉ lab p.2 ∧ v s ∈ F i p s v)
    (κ : ℝ≥0∞)
    (hκ : ∀ i p v, ∑ s ∈ srcs i p,
      ((F i p s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ) (T : Finset S) :
    ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v) (ρ v) j ≤
      κ * ∑ v, R.queryWeight I (fun i ↦ diagMass (B i ∩ {p | lab p.2 = T})) (x v) (ρ v) j := by
  classical
  obtain ⟨v₀⟩ : Nonempty ((s : S) → D s) := inferInstance
  set N : ℝ≥0∞ := ∑ u, if Agree T v₀ u then 1 else 0 with hN
  have hNv : ∀ v, ∑ u, (if Agree T v u then (1 : ℝ≥0∞) else 0) = N :=
    fun v ↦ sum_agree_eq T v v₀
  have hN1 : 1 ≤ N := by
    have h := Finset.single_le_sum (f := fun u ↦ if Agree T v₀ u then (1 : ℝ≥0∞) else 0)
      (fun _ _ ↦ by simp) (Finset.mem_univ v₀)
    simp only [show Agree T v₀ v₀ from fun _ _ ↦ rfl, ↓reduceIte] at h
    exact h
  have hN0 : N ≠ 0 := (zero_lt_one.trans_le hN1).ne'
  have hNtop : N ≠ ⊤ := by
    rw [hN]
    exact ENNReal.sum_ne_top.mpr fun u _ ↦ by split_ifs <;> simp
  have hv : ∀ v, ∑ u, (if Agree T v u then
      R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j else 0) ≤
        κ * N * R.queryWeight I (fun i ↦ diagMass (B i ∩ {p | lab p.2 = T})) (x v) (ρ v) j := by
    intro v
    have hstep : ∀ u, (if Agree T v u then
        R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j else 0) =
          R.queryWeight I (fun i σ ↦ if Agree T v u then
            diagMass (C u i ∩ {p | lab p.2 = T}) σ else 0) (x v) (ρ v) j := by
      intro u
      by_cases h : Agree T v u
      · simp only [h, ↓reduceIte]
        exact (hview T v u h (fun i ↦ C u i ∩ {p | lab p.2 = T}) (fun i p hp ↦ hp.2)
          fun i hi ↦ by rw [hCP u i hi, Set.empty_inter]).symm
      · simp only [h, ↓reduceIte]
        exact (queryWeight_zero_weight R I (x v) (ρ v) j).symm
    simp only [hstep]
    rw [← queryWeight_fintype_sum, ← R.queryWeight_const_mul]
    refine R.queryWeight_mono I (fun i σ _ ↦ ?_) (x v) (hρ v) j
    have h := sum_agree_diagMass_le_base (fun p : spec.In i × R.D ↦ lab p.2) T v
      (fun u ↦ C u i) (B i) (fun u ↦ hCB u i) (srcs i) (F i) (hF i) (fun u p hp ↦ hsrc u i p hp)
      κ (fun p u ↦ hκ i p u) σ
    rwa [hNv v] at h
  have h1 : N * ∑ u, R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u)
      (ρ u) j = ∑ v, ∑ u, (if Agree T v u then
        R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j
          else 0) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [← hNv u, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    have hs : Agree T u v ↔ Agree T v u := ⟨Agree.symm, Agree.symm⟩
    by_cases h : Agree T v u <;> simp [h, hs]
  have h2 : N * ∑ u, R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u)
      (ρ u) j ≤ N * (κ * ∑ v, R.queryWeight I
        (fun i ↦ diagMass (B i ∩ {p | lab p.2 = T})) (x v) (ρ v) j) := by
    rw [h1, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ ↦ (hv v).trans_eq (by ring)
  exact (ENNReal.mul_le_mul_iff_right hN0 hNtop).mp h2

/-- **The adaptive view lemma with a base set**: under the lazy-sampling property, if every input
state of `C v i ⊆ B i` names an undisclosed source with its value in `F`, the masses of `C v` add
up over the hidden values to at most `κ` times the masses of the base `B`. -/
theorem sum_queryWeight_view_le_base [∀ s, Nonempty (D s)] (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (P : spec.Port → Prop) (hview : ViewByOn R I P lab x ρ j)
    (C : ((s : S) → D s) → ∀ i, Set (spec.In i × R.D)) (B : ∀ i, Set (spec.In i × R.D))
    (hCP : ∀ v i, ¬ P i → C v i = ∅) (hCB : ∀ v i, C v i ⊆ B i)
    (srcs : ∀ i, spec.In i × R.D → Finset S)
    (F : ∀ i, spec.In i × R.D → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ i p s v d, F i p s (Function.update v s d) = F i p s v)
    (hsrc : ∀ v i p, p ∈ C v i → ∃ s ∈ srcs i p, s ∉ lab p.2 ∧ v s ∈ F i p s v)
    (κ : ℝ≥0∞)
    (hκ : ∀ i p v, ∑ s ∈ srcs i p,
      ((F i p s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ) :
    ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j ≤
      κ * ∑ v, R.queryWeight I (fun i ↦ diagMass (B i)) (x v) (ρ v) j := by
  classical
  have hpart : ∀ (E : ∀ i, Set (spec.In i × R.D)) v,
      R.queryWeight I (fun i ↦ diagMass (E i)) (x v) (ρ v) j =
        ∑ T, R.queryWeight I (fun i ↦ diagMass (E i ∩ {p | lab p.2 = T})) (x v) (ρ v) j :=
    fun E v ↦ by
      rw [← queryWeight_fintype_sum]
      refine congrArg (fun w ↦ R.queryWeight I w (x v) (ρ v) j) (funext fun i ↦ funext fun σ ↦ ?_)
      exact diagMass_eq_sum_label (fun p ↦ lab p.2) (E i) σ
  calc ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j
      = ∑ T, ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v)
          (ρ v) j := by
        simp only [fun v ↦ hpart (C v) v]
        exact Finset.sum_comm
    _ ≤ ∑ T, κ * ∑ v, R.queryWeight I (fun i ↦ diagMass (B i ∩ {p | lab p.2 = T})) (x v)
          (ρ v) j :=
        Finset.sum_le_sum fun T _ ↦ sum_queryWeight_cut_le_base R I lab x ρ hρ j P hview C B hCP
          hCB srcs F hF hsrc κ hκ T
    _ = κ * ∑ v, R.queryWeight I (fun i ↦ diagMass (B i)) (x v) (ρ v) j := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [fun v ↦ hpart B v]

end baseView

/-! ## The trial charge along the challenge prefix -/

section program

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

variable {M : Type} [Fintype M] [DecidableEq M]

/-- The input states of a `k`-read port at the cell `x` in `G x` satisfying `Inv`; none at the
other ports. -/
def readKSet (G : X → Set (HwReg X Z (Finset HPos × M)))
    (Inv : HwReg X Z (Finset HPos × M) → Prop) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      Set ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)))
  | .inl (.inl (.inr (.readK x _))) => {p | p.2 ∈ G x ∧ Inv p.2}
  | _ => ∅

/-- The sources of the hidden `h`-cells `zc x d` at the `k`-read ports. -/
noncomputable def srcsH (pub : Pub) (zc : X → HwReg X Z (Finset HPos × M) → Z) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      (recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)) → Finset HPos
  | .inl (.inl (.inr (.readK x _))), p => (sourcesSlotInv M pub).sh (zc x p.2) p.2
  | _, _ => ∅

/-- The source values of the hidden `h`-cells `zc x d` at the `k`-read ports. -/
noncomputable def valsH (pub : Pub) (zc : X → HwReg X Z (Finset HPos × M) → Z) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      (recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)) →
        (s : HPos) → ((s : HPos) → XD s) → Finset (XD s)
  | .inl (.inl (.inr (.readK x _))), p => (sourcesSlotInv M pub).Fh (zc x p.2) p.2
  | _, _ => fun _ _ ↦ ∅

/-- The sources of the hidden `k'`-cells `yc x d` at the `k`-read ports. -/
noncomputable def srcsK' (pub : Pub) (yc : X → HwReg X Z (Finset HPos × M) → X) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      (recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)) → Finset HPos
  | .inl (.inl (.inr (.readK x _))), p => (sourcesSlotInv M pub).sk' (yc x p.2) p.2
  | _, _ => ∅

/-- The source values of the hidden `k'`-cells `yc x d` at the `k`-read ports. -/
noncomputable def valsK' (pub : Pub) (yc : X → HwReg X Z (Finset HPos × M) → X) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      (recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)) →
        (s : HPos) → ((s : HPos) → XD s) → Finset (XD s)
  | .inl (.inl (.inr (.readK x _))), p => (sourcesSlotInv M pub).Fk' (yc x p.2) p.2
  | _, _ => fun _ _ ↦ ∅

variable (upd : TrialUpd M)

theorem readKSet_eq_empty (G : X → Set (HwReg X Z (Finset HPos × M)))
    (Inv : HwReg X Z (Finset HPos × M) → Prop) (i : (recHwSpec X Z HPos M).Port)
    (hi : ¬ i.isLeft = true) : readKSet G Inv i = ∅ := by
  rcases i with ((i | c) | c) | T
  · exact absurd rfl hi
  · exact absurd rfl hi
  · exact absurd rfl hi
  · rfl

theorem readKSet_mono {G G' : X → Set (HwReg X Z (Finset HPos × M))}
    {Inv Inv' : HwReg X Z (Finset HPos × M) → Prop} (hG : ∀ x d, d ∈ G x → Inv d → d ∈ G' x)
    (hI : ∀ d, Inv d → Inv' d) (i : (recHwSpec X Z HPos M).Port) :
    readKSet G Inv i ⊆ readKSet G' Inv' i := by
  rcases i with ((i | c) | c) | T
  · exact Set.empty_subset _
  · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
    · exact Set.empty_subset _
    · exact fun p hp ↦ ⟨hG x p.2 hp.1 hp.2, hI p.2 hp.2⟩
    · exact Set.empty_subset _
  · exact Set.empty_subset _
  · exact Set.empty_subset _

/-- **The view lemma at the `k`-read ports, through hidden `h`-cells**: when every state of
`G v x` on the invariant has the hidden, not hardwired `h`-cell `zc x d`, the masses of `G v`
along the challenge prefix add up over the hidden values to `2^-128` times those of a base
`Bs ⊇ G v`. -/
theorem sum_totalWeight_readKSet_h_le (m₀ : Finset HPos × M) (pub : Pub) (A : Adversary (X × Z))
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (G : (HPos → Digest) → X → Set (HwReg X Z (Finset HPos × M)))
    (Bs : X → Set (HwReg X Z (Finset HPos × M))) (hGB : ∀ v x, G v x ⊆ Bs x)
    (zc : X → HwReg X Z (Finset HPos × M) → Z)
    (hz : ∀ v x d, d ∈ G v x → d ∈ hSetG (hidH pub fun q ↦ v (.inl q)) (zc x d)) :
    ∑ v : HPos → Digest, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (fun i ↦ diagMass (readKSet (G v) (SlotInv M pub v) i))
        (realizeT v (prefixT M upd pub A)) ρ ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ * ∑ v : HPos → Digest,
        (runtimeR m₀).totalWeight LocalSig.Interp.instruments
          (fun i ↦ diagMass (readKSet Bs (fun _ ↦ True) i)) (realizeT v (prefixT M upd pub A)) ρ :=
  sum_totalWeight_le_of_forall (runtimeR m₀) LocalSig.Interp.instruments _ _ _ _ _ fun j ↦
    sum_queryWeight_view_le_base (runtimeR m₀) LocalSig.Interp.instruments (fun r ↦ r.2.2.1)
      (fun v ↦ realizeT v (prefixT M upd pub A)) (fun _ ↦ ρ) (fun _ ↦ hρ) j _
      ((viewBy_runtimeR_of_disc LocalSig.Interp.instruments m₀ (prefixT M upd pub A) ∅
        (disc_prefixT M upd pub A ∅) (fun _ ↦ ρ) (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ)
          j).viewByOn fun i ↦ i.isLeft = true)
      (fun v ↦ readKSet (G v) (SlotInv M pub v)) (readKSet Bs fun _ ↦ True)
      (fun v i hi ↦ readKSet_eq_empty _ _ i hi)
      (fun v i ↦ readKSet_mono (fun x d hd _ ↦ hGB v x hd) (fun _ _ ↦ trivial) i)
      (srcsH pub zc) (valsH pub zc) (fun i p s v d ↦ by
        rcases i with ((i | c) | c) | T
        · rfl
        · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
          · rfl
          · exact (sourcesSlotInv M pub).hFh _ _ s v d
          · rfl
        · rfl
        · rfl)
      (fun v i p hp ↦ by
        rcases i with ((i | c) | c) | T
        · exact hp.elim
        · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
          · exact hp.elim
          · obtain ⟨hG, hI⟩ := hp
            obtain ⟨hm, hn⟩ := hz v x p.2 hG
            exact (sourcesSlotInv M pub).hh v (zc x p.2) p.2 hI hm hn
          · exact hp.elim
        · exact hp.elim
        · exact hp.elim)
      _ (fun i p v ↦ by
        rcases i with ((i | c) | c) | T
        · simp [srcsH]
        · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
          · simp [srcsH]
          · exact (sourcesSlotInv M pub).hκh _ _ v
          · simp [srcsH]
        · simp [srcsH]
        · simp [srcsH])

/-- **The view lemma at the `k`-read ports, through hidden `k'`-cells** (as
`sum_totalWeight_readKSet_h_le`). -/
theorem sum_totalWeight_readKSet_k'_le (m₀ : Finset HPos × M) (pub : Pub) (A : Adversary (X × Z))
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (G : (HPos → Digest) → X → Set (HwReg X Z (Finset HPos × M)))
    (Bs : X → Set (HwReg X Z (Finset HPos × M))) (hGB : ∀ v x, G v x ⊆ Bs x)
    (yc : X → HwReg X Z (Finset HPos × M) → X)
    (hy : ∀ v x d, d ∈ G v x → d ∈ k'SetG (hidK' pub fun q ↦ v (.inl q)) (yc x d)) :
    ∑ v : HPos → Digest, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (fun i ↦ diagMass (readKSet (G v) (SlotInv M pub v) i))
        (realizeT v (prefixT M upd pub A)) ρ ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ * ∑ v : HPos → Digest,
        (runtimeR m₀).totalWeight LocalSig.Interp.instruments
          (fun i ↦ diagMass (readKSet Bs (fun _ ↦ True) i)) (realizeT v (prefixT M upd pub A)) ρ :=
  sum_totalWeight_le_of_forall (runtimeR m₀) LocalSig.Interp.instruments _ _ _ _ _ fun j ↦
    sum_queryWeight_view_le_base (runtimeR m₀) LocalSig.Interp.instruments (fun r ↦ r.2.2.1)
      (fun v ↦ realizeT v (prefixT M upd pub A)) (fun _ ↦ ρ) (fun _ ↦ hρ) j _
      ((viewBy_runtimeR_of_disc LocalSig.Interp.instruments m₀ (prefixT M upd pub A) ∅
        (disc_prefixT M upd pub A ∅) (fun _ ↦ ρ) (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ)
          j).viewByOn fun i ↦ i.isLeft = true)
      (fun v ↦ readKSet (G v) (SlotInv M pub v)) (readKSet Bs fun _ ↦ True)
      (fun v i hi ↦ readKSet_eq_empty _ _ i hi)
      (fun v i ↦ readKSet_mono (fun x d hd _ ↦ hGB v x hd) (fun _ _ ↦ trivial) i)
      (srcsK' pub yc) (valsK' pub yc) (fun i p s v d ↦ by
        rcases i with ((i | c) | c) | T
        · rfl
        · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
          · rfl
          · exact (sourcesSlotInv M pub).hFk' _ _ s v d
          · rfl
        · rfl
        · rfl)
      (fun v i p hp ↦ by
        rcases i with ((i | c) | c) | T
        · exact hp.elim
        · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
          · exact hp.elim
          · obtain ⟨hG, hI⟩ := hp
            obtain ⟨hm, hn⟩ := hy v x p.2 hG
            exact (sourcesSlotInv M pub).hk' v (yc x p.2) p.2 hI hm hn
          · exact hp.elim
        · exact hp.elim
        · exact hp.elim)
      _ (fun i p v ↦ by
        rcases i with ((i | c) | c) | T
        · simp [srcsK']
        · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
          · simp [srcsK']
          · exact (sourcesSlotInv M pub).hκk' _ _ v
          · simp [srcsK']
        · simp [srcsK']
        · simp [srcsK'])

/-- **The weight bounding the trial charge** at the `k`-reads (`sum_potential_trial_le`,
`ofReal_trialDiag_eq`): the fresh part `F` per read call, four times the sources of a filled
`k`-cell, `4 / |Z|` times those of an empty one per outcome, on the invariant `SlotInv`. -/
noncomputable def trialBnd (pub : Pub) (v : HPos → Digest) (F : ℝ≥0∞) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      Matrix ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)))
        ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M))) ℂ → ℝ≥0∞ :=
  fun i σ ↦ F * (if readRecPort M i = true then ENNReal.ofReal σ.trace.re else 0) +
    4 * diagMass (readKSet (srcK' pub.perm (hidK' pub fun q ↦ v (.inl q))) (SlotInv M pub v) i)
      σ +
    4 * diagMass (readKSet (srcH pub.perm (hidH pub fun q ↦ v (.inl q))) (SlotInv M pub v) i)
      σ +
    ∑ a, ENNReal.ofReal (4 / Fintype.card Z) * diagMass
      (readKSet (fun x ↦ srcHE pub.perm (hidH pub fun q ↦ v (.inl q)) x a) (SlotInv M pub v) i) σ

/-- **The trial charge on the invariant**: along the challenge prefix, TrialSource's `trialW` is at
most `trialBnd` with the fresh part `(2 cK + 4 cH) / |Z|`, when `cK` bounds the outcomes leading
a trial block to a hidden `k'`-cell and `cH` the values leading a capacity to a hidden `h`-cell. -/
theorem totalWeight_trialW_le (m₀ : Finset HPos × M) (pub : Pub) (A : Adversary (X × Z))
    (v : HPos → Digest)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    (hnb : QuerySupportedOn (fun m : QReg.of Unit × HwReg X Z (Finset HPos × M) ↦ m.2)
      {s | NoBot s} (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg X Z (Finset HPos × M)) ρ))
    (cK cH : ℝ)
    (hcK : ∀ x, ∑ a : Z, (hidK' pub fun q ↦ v (.inl q)).indicator (1 : X → ℝ) (pub.perm (x, a)).1 ≤
      cK)
    (hcH : ∀ z : Z, ∑ w : Z, (hidH pub fun q ↦ v (.inl q)).indicator (1 : Z → ℝ) (z + w) ≤ cH) :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (trialW pub.perm (hidH pub fun q ↦ v (.inl q)) (hidK' pub fun q ↦ v (.inl q)))
        (realizeT v (prefixT M upd pub A)) ρ ≤
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (trialBnd pub v (ENNReal.ofReal ((2 * cK + 4 * cH) / Fintype.card Z)))
        (realizeT v (prefixT M upd pub A)) ρ := by
  have hcK0 : 0 ≤ cK := nonneg_of_sum_ind_le _ (hcK 0)
  have hcH0 : 0 ≤ cH := nonneg_of_sum_ind_le _ (hcH 0)
  refine totalWeight_le_of_forallQueries (runtimeR m₀) LocalSig.Interp.instruments
    (fun i σ ↦ QuerySupportedOn
      (fun m : (recHwSpec X Z HPos M).In i × HwReg X Z (Finset HPos × M) ↦ m.2) {s | NoBot s}
        (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos M).In i)
          ((recHwSpec X Z HPos M).In i) ℂ) ⊗ₖ compressReg X Z (Finset HPos × M)) σ) ∧
      (readRecPort M i = true → ∀ a, ¬ SlotInv M pub v a.2 → σ a a = 0))
    (fun i E τ hτ ↦ ⟨hτ.1, fun hQ a ha ↦ traceRight_diag_eq_zero fun e ↦ hτ.2 hQ (a, e) ha⟩)
    (fun i σ hσ hok ↦ ?_) _ hρ
    (forallQueries_and (forallQueries_noBot m₀ LocalSig.Interp.instruments _ hnb)
      (forallQueries_of_hp (fun c ↦ readRecPort_prog c) m₀ _ pub v _ ∅ ∅
        (hp_prefixT upd pub v A) ρ
        (hs.imp fun _ ha ↦ invP_of_label_empty (Set.mem_singleton_iff.1 ha))))
  rcases i with ((i | c) | c) | T
  · exact zero_le
  · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
    · exact zero_le
    · have hinv : ∀ a, a ∉ {p : Unit × HwReg X Z (Finset HPos × M) | SlotInv M pub v p.2} →
          σ a a = 0 := fun a ha ↦ hok.2 rfl a ha
      show ∑ r, ∑ j, potential (kpot pub.perm (hidH pub fun q ↦ v (.inl q))
          (hidK' pub fun q ↦ v (.inl q)) (.afK x (r.1.getD 0)) j)
          (MatrixMap.conj (hwReadKraus (.readK x (fun m _ ↦ m)) r) σ) ≤ _
      simp only [Fintype.sum_option, kpot]
      refine (sum_potential_trial_le pub.perm _ _ x cK cH (hcK x) hcH hσ hok.1).trans ?_
      rw [ofReal_trialDiag_eq pub.perm _ _ x cK cH hcK0 hcH0 hσ]
      refine add_le_add (add_le_add (add_le_add (le_of_eq rfl) ?_) ?_)
        (Finset.sum_le_sum fun a _ ↦ ?_)
      · exact mul_le_mul_of_nonneg_left (diagMass_eq_inter _ _ hinv).le zero_le
      · exact mul_le_mul_of_nonneg_left (diagMass_eq_inter _ _ hinv).le zero_le
      · exact mul_le_mul_of_nonneg_left (diagMass_eq_inter _ _ hinv).le zero_le
    · exact zero_le
  · exact zero_le
  · exact zero_le

end program

/-! ## The cells of the in-table slots, counted -/

section cells

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- The `k'`-cells of the in-table slots at `pub`, `w`, by output position and round. -/
noncomputable def cellsK' (pub : Pub) (w : ValPos → Digest) : Finset X :=
  Finset.univ.image fun q : ValPos × Fin 8 ↦ srcCellK' pub (outSlot q.1) w q.2

/-- The `h`-cells of the in-table slots at `pub`, `w`, by output position and round. -/
noncomputable def cellsH (pub : Pub) (w : ValPos → Digest) : Finset Z :=
  Finset.univ.image fun q : ValPos × Fin 8 ↦ srcCellH pub (outSlot q.1) w q.2

theorem exists_cellK'_of_mem {pub : Pub} {w : ValPos → Digest} {y : X} (hy : y ∈ hidK' pub w) :
    ∃ q : ValPos × Fin 8, srcCellK' pub (outSlot q.1) w q.2 = y := by
  have hy' : SrcGood pub w ∧ ∃ s, InTable s ∧ ∃ j < nBlocks pub s, srcCellK' pub s w j = y := hy
  refine hy'.2.elim fun s hs ↦ hs.2.elim fun j hj ↦ ⟨(slotOutPos s, ⟨j, hj.1.trans_le
    (nBlocks_le_eight hs.1 pub)⟩), ?_⟩
  show srcCellK' pub (outSlot (slotOutPos s)) w j = y
  rw [outSlot_slotOutPos hs.1]
  exact hj.2

theorem exists_cellH_of_mem {pub : Pub} {w : ValPos → Digest} {z : Z} (hz : z ∈ hidH pub w) :
    ∃ q : ValPos × Fin 8, srcCellH pub (outSlot q.1) w q.2 = z := by
  have hz' : SrcGood pub w ∧ ∃ s, InTable s ∧ ∃ j < nBlocks pub s, srcCellH pub s w j = z := hz
  refine hz'.2.elim fun s hs ↦ hs.2.elim fun j hj ↦ ⟨(slotOutPos s, ⟨j, hj.1.trans_le
    (nBlocks_le_eight hs.1 pub)⟩), ?_⟩
  show srcCellH pub (outSlot (slotOutPos s)) w j = z
  rw [outSlot_slotOutPos hs.1]
  exact hj.2

theorem mem_cellsK' {pub : Pub} {w : ValPos → Digest} {y : X} (hy : y ∈ hidK' pub w) :
    y ∈ cellsK' pub w := by
  simp only [cellsK', Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_cellK'_of_mem hy

theorem mem_cellsH {pub : Pub} {w : ValPos → Digest} {z : Z} (hz : z ∈ hidH pub w) :
    z ∈ cellsH pub w := by
  simp only [cellsH, Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_cellH_of_mem hz

theorem card_cellsK'_le (pub : Pub) (w : ValPos → Digest) :
    (cellsK' pub w).card ≤ 8 * (498 * 2 ^ 32) :=
  Finset.card_image_le.trans (by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    exact (Nat.mul_le_mul_right 8 card_valPos_le).trans_eq (by ring))

theorem card_cellsH_le (pub : Pub) (w : ValPos → Digest) :
    (cellsH pub w).card ≤ 8 * (498 * 2 ^ 32) :=
  Finset.card_image_le.trans (by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    exact (Nat.mul_le_mul_right 8 card_valPos_le).trans_eq (by ring))

attribute [irreducible] cellsK' cellsH

end cells

/-! ## Counting over abstract types -/

section count

variable {X₁ Z₁ : Type} [Fintype Z₁] [DecidableEq X₁] [DecidableEq Z₁] [AddCommGroup Z₁]

omit [DecidableEq Z₁] in
/-- A trial at `x` reaches a `k'`-cell of `H ⊆ K` for at most `G |K|` outcomes. -/
theorem sum_ind_rate_le {π : Equiv.Perm (X₁ × Z₁)} {G : ℕ} (hπ : PermGood π G) (x : X₁)
    (H : Set X₁) (K : Finset X₁) (hHK : ∀ y ∈ H, y ∈ K) {c : ℕ} (hc : K.card ≤ c) :
    ∑ a : Z₁, H.indicator (1 : X₁ → ℝ) (π (x, a)).1 ≤ ((G * c : ℕ) : ℝ) := by
  calc ∑ a : Z₁, H.indicator (1 : X₁ → ℝ) (π (x, a)).1
      ≤ ∑ a : Z₁, (((if (π (x, a)).1 ∈ K then 1 else 0 : ℕ)) : ℝ) :=
        Finset.sum_le_sum fun a _ ↦ by
          by_cases h : (π (x, a)).1 ∈ H
          · rw [Set.indicator_of_mem h, ite_eq_left (hHK _ h)]
            simp
          · rw [Set.indicator_of_notMem h]
            positivity
    _ = (((∑ a : Z₁, if (π (x, a)).1 ∈ K then 1 else 0 : ℕ)) : ℝ) := by push_cast; rfl
    _ ≤ ((G * c : ℕ) : ℝ) := by
        exact_mod_cast (sum_rate_mem_le hπ x K).trans (Nat.mul_le_mul_left G hc)

omit [DecidableEq X₁] in
/-- A capacity `z` plus a value lands in `H ⊆ K` for at most `|K|` values. -/
theorem sum_ind_add_le (z : Z₁) (H : Set Z₁) (K : Finset Z₁) (hHK : ∀ y ∈ H, y ∈ K) {c : ℕ}
    (hc : K.card ≤ c) : ∑ w : Z₁, H.indicator (1 : Z₁ → ℝ) (z + w) ≤ (c : ℝ) := by
  calc ∑ w : Z₁, H.indicator (1 : Z₁ → ℝ) (z + w)
      ≤ ∑ w : Z₁, (((if z + w ∈ K then 1 else 0 : ℕ)) : ℝ) :=
        Finset.sum_le_sum fun w _ ↦ by
          by_cases h : z + w ∈ H
          · rw [Set.indicator_of_mem h, ite_eq_left (hHK _ h)]
            simp
          · rw [Set.indicator_of_notMem h]
            positivity
    _ = (((∑ w : Z₁, if z + w ∈ K then 1 else 0 : ℕ)) : ℝ) := by push_cast; rfl
    _ ≤ (c : ℝ) := by exact_mod_cast (sum_add_mem_le z K).trans hc

end count

/-! ## Total weights of sums, over a generic runtime -/

section twGen

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

theorem totalWeight_four_eq {K : Type*} [Fintype K] (F c : ℝ≥0∞)
    (w₀ w₁ w₂ : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (w₃ : K → ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec Ω A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I (fun i σ ↦ F * w₀ i σ + 4 * w₁ i σ + 4 * w₂ i σ + ∑ k, c * w₃ k i σ) x ρ =
      F * R.totalWeight I w₀ x ρ + 4 * R.totalWeight I w₁ x ρ + 4 * R.totalWeight I w₂ x ρ +
        ∑ k, c * R.totalWeight I (w₃ k) x ρ := by
  rw [totalWeight_add_weight, totalWeight_add_weight, totalWeight_add_weight,
    totalWeight_const_mul_weight, totalWeight_const_mul_weight, totalWeight_const_mul_weight,
    totalWeight_fintype_sum]
  simp only [totalWeight_const_mul_weight]

theorem totalWeight_two_eq {K : Type*} [Fintype K] (c : ℝ≥0∞)
    (w₀ : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (w₃ : K → ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec Ω A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I (fun i σ ↦ w₀ i σ + ∑ k, c * w₃ k i σ) x ρ =
      R.totalWeight I w₀ x ρ + ∑ k, c * R.totalWeight I (w₃ k) x ρ := by
  rw [totalWeight_add_weight, totalWeight_fintype_sum]
  simp only [totalWeight_const_mul_weight]

end twGen

/-! ## `htrial` -/

section htrial

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- **The good hidden values of the trials**: a `PermGood π 18` permutation and no trial block (of
either layer) a hidden `k`-cell. -/
def TrialHidGood (pub : Pub) (v : HPos → Digest) : Prop :=
  PermGood pub.perm 18 ∧ ∀ x, TrialBlock pub.param x → x ∉ hidK pub fun q ↦ v (.inl q)

/-- `TrialHidGood`, decided classically. -/
noncomputable instance instDecidableTrialHidGood (pub : Pub) :
    DecidablePred (TrialHidGood pub) :=
  Classical.decPred _

variable {M : Type} [Fintype M] [DecidableEq M]

/-- **The recorded trial cells**: at a `k`-read at `x`, the mass of the states whose `k`-cell `x`
holds a value (recorded or hardwired) plus, averaged over the outcomes `a`, the mass of those whose
trial `k'`-cell `π (x, a)` holds a value. -/
noncomputable def trialRecW (π : Equiv.Perm (X × Z)) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      Matrix ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)))
        ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M))) ℂ → ℝ≥0∞ :=
  fun i σ ↦ diagMass (readKSet baseK (fun _ ↦ True) i) σ +
    ∑ a, (Fintype.card Z : ℝ≥0∞)⁻¹ * diagMass (readKSet (fun x ↦ baseK' π x a) (fun _ ↦ True) i) σ

/-- **The trials' hidden read mass per hidden value**: `clsCap · 2^-462` for the fresh trial cells
(`40 · 8 · 498 · 2^32 / 2^512` per read call) plus `8 · 2^-128` per unit `R` of recorded trial
cells. -/
noncomputable def htrialTau (R : ℝ≥0∞) : ℝ≥0∞ :=
  (clsCap : ℝ≥0∞) * (2 ^ 462 : ℝ≥0∞)⁻¹ + 8 * (2 ^ 128 : ℝ≥0∞)⁻¹ * R

set_option exponentiation.threshold 1024 in
/-- The fresh trial cells at Keccak's sizes: `40 · 8 · 498 · 2^32 / 2^512 ≤ 2^-462`. -/
theorem freshTerm_le {cZ : ℕ} (hZ : cZ = 2 ^ 512) :
    ENNReal.ofReal ((2 * ((18 * (8 * (498 * 2 ^ 32)) : ℕ) : ℝ) +
      4 * ((8 * (498 * 2 ^ 32) : ℕ) : ℝ)) / (cZ : ℝ)) ≤ (2 ^ 462 : ℝ≥0∞)⁻¹ := by
  subst hZ
  rw [inv_two_pow_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  norm_num

theorem ofReal_four_div (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (4 / (n : ℝ)) = 4 * (n : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast,
    ENNReal.ofReal_ofNat, div_eq_mul_inv]

/-- The arithmetic of the final bound, over abstract quantities. -/
theorem htrial_arith (F N κ V T K1 K2 K3 S S' R : ℝ≥0∞) (hT : T ≤ N * V) (h1 : K1 ≤ κ * S)
    (h2 : K2 ≤ κ * S) (h3 : K3 ≤ 4 * κ * S') (hS : S + S' ≤ R * V) :
    F * T + 4 * K1 + 4 * K2 + K3 ≤ (F * N + 8 * κ * R) * V := by
  calc F * T + 4 * K1 + 4 * K2 + K3
      ≤ F * (N * V) + 4 * (κ * S) + 4 * (κ * S) + 4 * κ * S' := by gcongr
    _ = F * (N * V) + 8 * κ * S + 4 * κ * S' := by ring
    _ ≤ F * (N * V) + 8 * κ * S + 8 * κ * S' := by gcongr; norm_num
    _ = F * (N * V) + 8 * κ * (S + S') := by ring
    _ ≤ F * (N * V) + 8 * κ * (R * V) := by gcongr
    _ = (F * N + 8 * κ * R) * V := by ring

/-- The sums of the final bound, over abstract quantities. -/
theorem htrial_sum_arith {V' β : Type} [Fintype V'] [Fintype β] (F N κ V c R : ℝ≥0∞)
    (T K1 K2 K : V' → ℝ≥0∞) (K3 S3 : V' → β → ℝ≥0∞) (hT : ∑ v, T v ≤ N * V)
    (h1 : ∑ v, K1 v ≤ κ * ∑ v, K v) (h2 : ∑ v, K2 v ≤ κ * ∑ v, K v)
    (h3 : ∀ a, ∑ v, K3 v a ≤ κ * ∑ v, S3 v a)
    (hS : ∑ v, (K v + ∑ a, c * S3 v a) ≤ R * V) :
    ∑ v, (F * T v + 4 * K1 v + 4 * K2 v + ∑ a, 4 * c * K3 v a) ≤ (F * N + 8 * κ * R) * V := by
  have e3 : ∑ v, ∑ a, 4 * c * K3 v a ≤ 4 * κ * ∑ v, ∑ a, c * S3 v a := by
    calc ∑ v, ∑ a, 4 * c * K3 v a = ∑ a, 4 * c * ∑ v, K3 v a := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ ≤ ∑ a, 4 * c * (κ * ∑ v, S3 v a) :=
          Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (h3 a) zero_le
      _ = 4 * κ * ∑ v, ∑ a, c * S3 v a := by
          rw [Finset.sum_comm (f := fun v a ↦ c * S3 v a)]
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun v _ ↦ by ring
  rw [Finset.sum_add_distrib] at hS
  refine le_trans (le_of_eq ?_) (htrial_arith F N κ V (∑ v, T v) (∑ v, K1 v) (∑ v, K2 v) _ _ _ R
    hT h1 h2 e3 hS)
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

variable (upd : TrialUpd M)

theorem totalWeight_trialBnd_eq (m₀ : Finset HPos × M) (pub : Pub) (v : HPos → Digest)
    (F : ℝ≥0∞) {Ω : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments (recHwSpec X Z HPos M) Ω A)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset HPos × M)))
      (A × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments (trialBnd pub v F) x ρ =
      F * (runtimeR m₀).totalWeight LocalSig.Interp.instruments
          (fun i σ ↦ if readRecPort M i = true then ENNReal.ofReal σ.trace.re else 0) x ρ +
        4 * (runtimeR m₀).totalWeight LocalSig.Interp.instruments (fun i ↦ diagMass
          (readKSet (srcK' pub.perm (hidK' pub fun q ↦ v (.inl q))) (SlotInv M pub v) i)) x ρ +
        4 * (runtimeR m₀).totalWeight LocalSig.Interp.instruments (fun i ↦ diagMass
          (readKSet (srcH pub.perm (hidH pub fun q ↦ v (.inl q))) (SlotInv M pub v) i)) x ρ +
        ∑ a, ENNReal.ofReal (4 / Fintype.card Z) *
          (runtimeR m₀).totalWeight LocalSig.Interp.instruments (fun i ↦ diagMass
            (readKSet (fun x ↦ srcHE pub.perm (hidH pub fun q ↦ v (.inl q)) x a)
              (SlotInv M pub v) i)) x ρ := by
  exact totalWeight_four_eq (runtimeR m₀) LocalSig.Interp.instruments F
    (ENNReal.ofReal (4 / Fintype.card Z))
    (fun i σ ↦ if readRecPort M i = true then ENNReal.ofReal σ.trace.re else 0)
    (fun i ↦ diagMass
      (readKSet (srcK' pub.perm (hidK' pub fun q ↦ v (.inl q))) (SlotInv M pub v) i))
    (fun i ↦ diagMass
      (readKSet (srcH pub.perm (hidH pub fun q ↦ v (.inl q))) (SlotInv M pub v) i))
    (fun a i ↦ diagMass (readKSet (fun x ↦ srcHE pub.perm (hidH pub fun q ↦ v (.inl q)) x a)
      (SlotInv M pub v) i)) x ρ

theorem totalWeight_trialRecW_eq (m₀ : Finset HPos × M) (π : Equiv.Perm (X × Z))
    {Ω : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments (recHwSpec X Z HPos M) Ω A)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset HPos × M)))
      (A × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments (trialRecW π) x ρ =
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments
          (fun i ↦ diagMass (readKSet baseK (fun _ ↦ True) i)) x ρ +
        ∑ a, (Fintype.card Z : ℝ≥0∞)⁻¹ * (runtimeR m₀).totalWeight LocalSig.Interp.instruments
          (fun i ↦ diagMass (readKSet (fun x ↦ baseK' π x a) (fun _ ↦ True) i)) x ρ := by
  exact totalWeight_two_eq (runtimeR m₀) LocalSig.Interp.instruments
    (Fintype.card Z : ℝ≥0∞)⁻¹ (fun i ↦ diagMass (readKSet baseK (fun _ ↦ True) i))
    (fun a i ↦ diagMass (readKSet (fun x ↦ baseK' π x a) (fun _ ↦ True) i)) x ρ

variable (A : Adversary (X × Z)) {q : ℕ}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The randomizer trials' hidden read mass** (TrialSource's `htrial` at one public datum, on
the good hidden values `TrialHidGood`): summed over the hidden values, at most `htrialTau R` per
hidden value, given the recorded trial cells `R` per hidden value. -/
theorem sum_trialMass_le (m₀ : Finset HPos × M) (pub : Pub)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    (hnb : QuerySupportedOn (fun m : QReg.of Unit × HwReg X Z (Finset HPos × M) ↦ m.2)
      {s | NoBot s} (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg X Z (Finset HPos × M)) ρ))
    (R : ℝ≥0∞)
    (hrec : ∑ v : HPos → Digest, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (trialRecW pub.perm) (realizeT v (prefixT M upd pub A)) ρ ≤
        R * Fintype.card (HPos → Digest)) :
    ∑ v : HPos → Digest, (if TrialHidGood pub v then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (hidH pub fun q ↦ v (.inl q))
        (hidK pub fun q ↦ v (.inl q)) (hidK' pub fun q ↦ v (.inl q)))
      (realizeT v (prefixT M upd pub A)) ρ else 0) ≤
      htrialTau R * Fintype.card (HPos → Digest) := by
  set C : ℕ := 8 * (498 * 2 ^ 32) with hC
  set cK : ℝ := ((18 * C : ℕ) : ℝ) with hcKdef
  set cH : ℝ := (C : ℝ) with hcHdef
  set F : ℝ≥0∞ := ENNReal.ofReal ((2 * cK + 4 * cH) / Fintype.card Z) with hF
  set κ : ℝ≥0∞ := (Fintype.card Digest : ℝ≥0∞)⁻¹ with hκ
  have hN : ∀ v, IFreeM.IsChargeBound (realizeT v (prefixT M upd pub A))
      (portCharge fun i ↦ if readRecPort M i = true then 1 else 0) clsCap := fun v ↦ by
    have h := hN_readRec upd A hperm hsign pub v
    rw [gameT_eq_prefixT_bind, realizeT_bind₂] at h
    exact isChargeBound_of_bind₂ h
  have hper : ∀ v, (if TrialHidGood pub v then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (hidH pub fun q ↦ v (.inl q))
        (hidK pub fun q ↦ v (.inl q)) (hidK' pub fun q ↦ v (.inl q)))
          (realizeT v (prefixT M upd pub A)) ρ else 0) ≤
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments (trialBnd pub v F)
        (realizeT v (prefixT M upd pub A)) ρ := by
    intro v
    by_cases hT : TrialHidGood pub v
    · rw [ite_eq_left hT]
      have hcK : ∀ x, ∑ a : Z, (hidK' pub fun q ↦ v (.inl q)).indicator (1 : X → ℝ)
          (pub.perm (x, a)).1 ≤ cK := fun x ↦
        sum_ind_rate_le hT.1 x _ (cellsK' pub fun q ↦ v (.inl q)) (fun _ hy ↦ mem_cellsK' hy)
          (card_cellsK'_le pub _)
      have hcH : ∀ z : Z, ∑ w : Z, (hidH pub fun q ↦ v (.inl q)).indicator (1 : Z → ℝ) (z + w) ≤
          cH := fun z ↦
        sum_ind_add_le z _ (cellsH pub fun q ↦ v (.inl q)) (fun _ hz ↦ mem_cellsH hz)
          (card_cellsH_le pub _)
      exact (totalWeight_prefixT_le_trialW upd m₀ pub A v _ hT.2 hρ).trans
        (totalWeight_trialW_le upd m₀ pub A v ρ hρ hs hnb cK cH hcK hcH)
    · rw [ite_eq_right hT]
      exact zero_le
  refine (Finset.sum_le_sum fun v _ ↦ hper v).trans ?_
  refine (Finset.sum_congr rfl fun v _ ↦ totalWeight_trialBnd_eq m₀ pub v F
    (realizeT v (prefixT M upd pub A)) ρ).trans_le ?_
  rw [ofReal_four_div (Fintype.card Z) Fintype.card_pos]
  refine (htrial_sum_arith F clsCap κ (Fintype.card (HPos → Digest)) (Fintype.card Z : ℝ≥0∞)⁻¹ R
    _ _ _ (fun v ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (fun i ↦ diagMass (readKSet baseK (fun _ ↦ True) i)) (realizeT v (prefixT M upd pub A)) ρ)
    _ (fun v a ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (fun i ↦ diagMass (readKSet (fun x ↦ baseK' pub.perm x a) (fun _ ↦ True) i))
      (realizeT v (prefixT M upd pub A)) ρ) ?_ ?_ ?_ ?_ ?_).trans ?_
  · calc ∑ v, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
          (fun i σ ↦ if readRecPort M i = true then ENNReal.ofReal σ.trace.re else 0)
          (realizeT v (prefixT M upd pub A)) ρ
        ≤ ∑ _v : HPos → Digest, (clsCap : ℝ≥0∞) :=
          Finset.sum_le_sum fun v _ ↦ (totalWeight_trace_le_of_isChargeBound' (runtimeR m₀)
            LocalSig.Interp.instruments (fun i ↦ readRecPort M i = true)
            (realizeT v (prefixT M upd pub A)) (hN v) hρ).trans
            ((mul_le_mul_of_nonneg_left hρ1 zero_le).trans_eq (mul_one _))
      _ = (clsCap : ℝ≥0∞) * Fintype.card (HPos → Digest) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  · exact sum_totalWeight_readKSet_k'_le upd m₀ pub A ρ hρ
      (fun v ↦ srcK' pub.perm (hidK' pub fun q ↦ v (.inl q))) baseK
      (fun _ _ _ ⟨_, ha, _⟩ h0 ↦ by rw [ha] at h0; cases h0)
      (fun x d ↦ (pub.perm (x, (kValG x d).getD 0)).1)
      (fun _ _ _ ⟨_, ha, h⟩ ↦ by rw [ha, Option.getD_some]; exact h)
  · exact sum_totalWeight_readKSet_h_le upd m₀ pub A ρ hρ
      (fun v ↦ srcH pub.perm (hidH pub fun q ↦ v (.inl q))) baseK
      (fun _ _ _ ⟨_, ha, _⟩ h0 ↦ by rw [ha] at h0; cases h0)
      (fun x d ↦ (pub.perm (x, (kValG x d).getD 0)).2 +
        (k'ValG (pub.perm (x, (kValG x d).getD 0)).1 d).getD 0)
      (fun _ _ _ ⟨_, ha, _, hw, h⟩ ↦ by rw [ha, Option.getD_some, hw, Option.getD_some]; exact h)
  · intro a
    exact sum_totalWeight_readKSet_h_le upd m₀ pub A ρ hρ
      (fun v x ↦ srcHE pub.perm (hidH pub fun q ↦ v (.inl q)) x a) (fun x ↦ baseK' pub.perm x a)
      (fun _ _ _ ⟨_, _, hw, _⟩ h0 ↦ by rw [hw] at h0; cases h0)
      (fun x d ↦ (pub.perm (x, a)).2 + (k'ValG (pub.perm (x, a)).1 d).getD 0)
      (fun _ _ _ ⟨_, _, hw, h⟩ ↦ by rw [hw, Option.getD_some]; exact h)
  · simpa only [totalWeight_trialRecW_eq] using hrec
  · rw [hκ, card_digest_inv, htrialTau]
    refine mul_le_mul_of_nonneg_right (add_le_add ?_ le_rfl) zero_le
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (freshTerm_le rnCard_Z) zero_le

end htrial

/-! ## The bad fraction of `TrialHidGood` -/

section trialGoodFrac

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- The first block of a tweakable-hash input names, whatever its payload, the slot of its prefix
and address at some index. -/
theorem exists_slotOfBlock_thInput (P Q : PublicParameter) (fields : TweakFields)
    (payload : HashInput) : ∃ idx, slotOfBlock P (blockOf (firstBlock (thInput Q fields payload))) =
      slotOfAddress P Q fields idx := by
  set x := blockOf (firstBlock (thInput Q fields payload))
  have hx : ∀ j (hj : j < 192), x ⟨j, by omega⟩ = inputBit (thInput Q fields payload) j :=
    fun j hj ↦ blockOf_firstBlock _ _ (by rw [length_thInput]; simp only; omega)
  have hQ : rateSlice x 0 128 (by norm_num) = Q := rateSlice_eq fun j hj ↦ by
    rw [hx (0 + j) (by omega), zero_add, inputBit_thInput_prefix _ _ _ _ hj]
  have hlo : rateSlice x 128 32 (by norm_num) = fields.lo := rateSlice_eq fun j hj ↦ by
    rw [hx (128 + j) (by omega), inputBit_thInput_address _ _ _ _ (by omega),
      inputBit_addressBytes_lo _ _ hj]
  have hhi : rateSlice x 160 24 (by norm_num) = fields.hi := rateSlice_eq fun j hj ↦ by
    rw [hx (160 + j) (by omega), show 160 + j = 128 + (32 + j) by omega,
      inputBit_thInput_address _ _ _ _ (by omega), inputBit_addressBytes_hi _ _ hj]
  have htag : rateSlice x 184 5 (by norm_num) = fields.tag := rateSlice_eq fun j hj ↦ by
    rw [hx (184 + j) (by omega), show 184 + j = 128 + (56 + j) by omega,
      inputBit_thInput_address _ _ _ _ (by omega), inputBit_addressBytes_stepTag _ _ (by omega),
      BitVec.getLsbD_append, ite_eq_left hj]
  have hstep : rateSlice x 189 3 (by norm_num) = fields.step := rateSlice_eq fun j hj ↦ by
    rw [hx (189 + j) (by omega), show 189 + j = 128 + (56 + (5 + j)) by omega,
      inputBit_thInput_address _ _ _ _ (by omega), inputBit_addressBytes_stepTag _ _ (by omega),
      BitVec.getLsbD_append, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  exact ⟨rateSlice x 384 128 (by norm_num), by rw [slotOfBlock, hQ, hlo, hhi, htag, hstep]⟩

/-- **A trial block names no in-table slot**, of either layer, at any parameter. -/
theorem not_inTable_of_trialBlock {P : PublicParameter} {x : X} (hx : TrialBlock P x)
    (P₀ : PublicParameter) {s : Slot} (hs : slotOfBlock P₀ x = some s) : ¬InTable s := by
  obtain ⟨l, e, msg, ρ, -, hb⟩ := hx
  have hh := head?_blocks
    (thInput P (hashDomainFields (.message l e)) (msg ++ littleEndianBytes 16 ρ))
  rw [hb, List.head?_cons] at hh
  rw [Option.some.inj hh] at hs
  obtain ⟨idx, hidx⟩ := exists_slotOfBlock_thInput P₀ P (hashDomainFields (.message l e))
    (msg ++ littleEndianBytes 16 ρ)
  rw [hidx] at hs
  exact not_inTable_of_slotOfAddress_message P₀ P l e idx hs

/-- The first block of a message-digest input at a parameter, layer, key and at most `48` payload
bytes. -/
def trialBlkAll (a : PublicParameter × Layer × KeyIndex × (Fin 49 × (Fin 48 → BitVec 8))) : X :=
  (blocks (thInput a.1 (hashDomainFields (.message a.2.1 a.2.2.1))
    (List.ofFn fun i : Fin a.2.2.2.1 ↦
      (⟨a.2.2.2.2 ⟨i, lt_of_lt_of_le i.2 (Nat.le_of_lt_succ a.2.2.2.1.2)⟩⟩ : UInt8)))).getD 0 0

/-- **The trial blocks of both layers**: the first blocks of the message-digest inputs with at most
`48` payload bytes (irreducible after `mem_trialSetAll_of`). -/
def trialSetAll : Finset X :=
  Finset.univ.image trialBlkAll

theorem mem_trialSetAll_of
    (a : PublicParameter × Layer × KeyIndex × (Fin 49 × (Fin 48 → BitVec 8))) :
    trialBlkAll a ∈ trialSetAll := by
  simp only [trialSetAll, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨a, rfl⟩

attribute [irreducible] trialSetAll

theorem ofFn_toBitVec_getD (L : List UInt8) :
    (List.ofFn fun i : Fin L.length ↦ (⟨(L.getD i 0).toBitVec⟩ : UInt8)) = L := by
  refine List.ext_getElem (List.length_ofFn) fun i h₁ h₂ ↦ ?_
  rw [List.getElem_ofFn]
  show (⟨(L.getD i 0).toBitVec⟩ : UInt8) = L[i]
  rw [List.getD_eq_getElem _ _ h₂]

theorem mem_trialSetAll {P : PublicParameter} {x : X} (hx : TrialBlock P x) :
    x ∈ trialSetAll := by
  obtain ⟨l, e, msg, ρ, hm, hb⟩ := hx
  set L := msg ++ littleEndianBytes 16 ρ with hL
  have hlen : L.length < 49 := by
    rw [hL, List.length_append]
    simp only [littleEndianBytes, List.length_ofFn]
    omega
  have h := mem_trialSetAll_of (P, l, e, ⟨L.length, hlen⟩, fun i ↦ (L.getD i 0).toBitVec)
  have he : trialBlkAll (P, l, e, ⟨L.length, hlen⟩, fun i ↦ (L.getD i 0).toBitVec) = x := by
    show (blocks (thInput P (hashDomainFields (.message l e))
      (List.ofFn fun i : Fin L.length ↦ (⟨(L.getD i 0).toBitVec⟩ : UInt8)))).getD 0 0 = x
    rw [ofFn_toBitVec_getD, hb]
    rfl
  rw [he] at h
  exact h

theorem card_layer : Fintype.card Layer = 2 := by
  rw [Fintype.card_fin]
  rfl

theorem card_bitVec8 : Fintype.card (BitVec 8) = 2 ^ 8 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

set_option exponentiation.threshold 4096 in
/-- **At most `2^551` trial blocks** of both layers. -/
theorem card_trialSetAll_le : trialSetAll.card ≤ 2 ^ 551 := by
  unfold trialSetAll
  refine Finset.card_image_le.trans ?_
  have hd : Fintype.card (Fin 49 × (Fin 48 → BitVec 8)) = 49 * (2 ^ 8) ^ 48 := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, card_bitVec8]
  rw [Finset.card_univ, card_prod_four card_publicParameter card_layer card_keyIndex hd]
  norm_num

/-- **A trial block among the in-table cells** at `pub`, `v`: a `k`-cell of an in-table slot is a
trial block of either layer. -/
def TrialBadAll (pub : Pub) (v : ValPos → Digest) : Prop :=
  ∃ s, InTable s ∧ ∃ j < nBlocks pub s, TrialBlock pub.param (srcCellK pub s v j)

theorem exists_rnd_of_trialBadAll {w : XW} {h : Z → X} {v : ValPos → Digest}
    (hb : TrialBadAll (xPub w h) v) :
    ∃ a ∈ rnds xI (xLen w.1), 1 ≤ a.2 ∧
      famK w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 a ∈ trialSetAll := by
  obtain ⟨s, hs, j, hj, hT⟩ := hb
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact not_inTable_of_trialBlock hT (xPub w h).param
      (slotOfBlock_cellK_zero (xPub w h) hs v) hs
  obtain ⟨p, hp, rfl⟩ : ∃ p, InPos p ∧ outSlot p = s :=
    ⟨slotOutPos s, inPos_slotOutPos hs, outSlot_slotOutPos hs⟩
  refine ⟨(p, j), mem_rnds.mpr ⟨mem_xI.mpr hp, ?_⟩, Nat.one_le_iff_ne_zero.mpr hj0, ?_⟩
  · show j < xLen w.1 p
    rw [← nBlocks_xPub_eq w h p]
    exact hj
  · have e : famK w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 (p, j) =
        srcCellK (xPub w h) (outSlot p) v j :=
      (srcCellK_eq_rnK w h (outSlot p) v hj).symm
    rw [e]
    exact mem_trialSetAll hT

/-- `TrialHidGood` on the values at the value positions. -/
def TrialHidGoodV (pub : Pub) (w : ValPos → Digest) : Prop :=
  PermGood pub.perm 18 ∧ ∀ x, TrialBlock pub.param x → x ∉ hidK pub w

theorem trialBadAll_of_not {pub : Pub} {w : ValPos → Digest} (h : ¬TrialHidGoodV pub w) :
    ¬PermGood pub.perm 18 ∨ (PermGood pub.perm 18 ∧ TrialBadAll pub w) := by
  by_cases hπ : PermGood pub.perm 18
  · refine Or.inr ⟨hπ, ?_⟩
    simp only [TrialHidGoodV, hπ, true_and, not_forall, not_not] at h
    obtain ⟨x, hT, hx⟩ := h
    have hx' : SrcGood pub w ∧ ∃ s, InTable s ∧ ∃ j < nBlocks pub s, srcCellK pub s w j = x := hx
    obtain ⟨-, s, hs, j, hj, hjx⟩ := hx'
    exact ⟨s, hs, j, hj, hjx ▸ hT⟩
  · exact Or.inl hπ

open scoped Classical in
/-- **`TrialHidGood` fails** for at most the bad permutations plus
`N² / |X| + N² (G + 1) / |Z| + N |trialSetAll| / |X|` of the public data and hidden values,
`N = 8 |xI|`, `G = 18`. -/
theorem trialHidGoodV_frac_le :
    (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          ¬TrialHidGoodV (pubX y.1) y.2).card ≤
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π 18).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        (((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
          ((8 * xI.card * (8 * xI.card) * (18 + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
          ((8 * xI.card * trialSetAll.card : ℕ) : ℝ≥0∞) / Fintype.card X) := by
  set N := Fintype.card (PX × (ValPos → Digest))
  have hsub := card_filter_le_add_of_imp
    (fun y : PX × (ValPos → Digest) ↦ ¬TrialHidGoodV (pubX y.1) y.2)
    (fun y : PX × (ValPos → Digest) ↦ ¬PermGood (pxPermEquiv y).1 18)
    (fun y : PX × (ValPos → Digest) ↦ PermGood y.1.1.2.2.1 18 ∧ TrialBadAll (pubX y.1) y.2)
    fun y hy ↦ trialBadAll_of_not hy
  have hgood := frac_pathTrial_le sEquiv (fun q ↦ q.2.1) (fun q ↦ xBlk q.1 q.2.2.2)
    (fun q ↦ xLen q.1) xI (fun q ↦ xBlk_injOn q.1 q.2.2.2) 18 _ (fun q ↦ card_rnds_xI_le q.1)
    trialSetAll (fun y : PX × (ValPos → Digest) ↦
      PermGood y.1.1.2.2.1 18 ∧ TrialBadAll (pubX y.1) y.2) fun q t hb ↦
      ⟨hb.1, exists_rnd_of_trialBadAll (w := (q.1, q.2.1, t.2.1, t.2.2)) (h := t.1)
        (v := q.2.2.2) hb.2⟩
  calc (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
        ¬TrialHidGoodV (pubX y.1) y.2).card
      ≤ (N : ℝ≥0∞)⁻¹ * (((Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          ¬PermGood (pxPermEquiv y).1 18).card : ℝ≥0∞) +
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 18 ∧ TrialBadAll (pubX y.1) y.2).card) := by
        gcongr
        exact_mod_cast hsub
    _ = (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          ¬PermGood (pxPermEquiv y).1 18).card +
        (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 18 ∧ TrialBadAll (pubX y.1) y.2).card := mul_add _ _ _
    _ ≤ _ := by
        rw [inv_card_mul_card_filter_comp_fst pxPermEquiv fun π ↦ ¬PermGood π 18]
        exact add_le_add le_rfl hgood

set_option exponentiation.threshold 4096 in
/-- The trial term at Keccak's sizes, for `n ≤ 498 · 2^32` outputs and at most `2^551` trial
blocks: `2^595 / 2^1088`. -/
theorem trialTermAll_le {n m cX : ℕ} (hn : n ≤ 498 * 2 ^ 32) (hm : m ≤ 2 ^ 551)
    (hX : cX = 2 ^ 1088) : ((8 * n * m : ℕ) : ℝ≥0∞) / cX ≤ ENNReal.ofReal (1 / 2 ^ 490) := by
  subst hX
  have hK : 8 * n * m ≤ 2 ^ 598 :=
    calc 8 * n * m ≤ 8 * (498 * 2 ^ 32) * 2 ^ 551 := by gcongr
      _ ≤ 2 ^ 598 := by norm_num
  rw [natCast_div_eq_ofReal _ (2 ^ 1088) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc ((8 * n * m : ℕ) : ℝ) / ((2 ^ 1088 : ℕ) : ℝ) ≤ 2 ^ 598 / 2 ^ 1088 := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hK) (by positivity)
    _ ≤ 1 / 2 ^ 490 := by norm_num

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **`TrialHidGood` fails at Keccak's sizes** for at most `2^-400` of the public data and hidden
values (the bad permutations `2^-777`, the collisions `2^-401`, the trial blocks `2^-490`). -/
theorem trialHidGoodV_frac_le_keccak :
    (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          ¬TrialHidGoodV (pubX y.1) y.2).card ≤
      ENNReal.ofReal (1 / 2 ^ 400) := by
  refine (trialHidGoodV_frac_le.trans (add_le_add permTerm_le_keccak
    (add_le_add (collTerms_le card_xI_le rnCard_X rnCard_Z)
      (trialTermAll_le card_xI_le card_trialSetAll_le rnCard_X)))).trans ?_
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 401)
      (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 490),
    ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 777) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

open scoped Classical in
/-- **The good tables violating `TrialHidGood`** at the reparametrization `r0E`: at most `2^-400`
of the padded tables are in ReparamR0's good set `r0G treeQ 18` while `TrialHidGood` fails at
their public datum and hidden values (the coordinates of Reparam-good tables are distinct). -/
theorem trialHidGood_r0G_frac_le_keccak :
    (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦
          r0G treeQ 18 t ∧ ¬TrialHidGood (pubR (r0E t).1) (r0E t).2.1).card ≤
      ENNReal.ofReal (1 / 2 ^ 400) := by
  refine le_trans ?_ trialHidGoodV_frac_le_keccak
  have hC := card_filter_le_of_injOn
    (fun t ↦ ((((fwd xmssFix xO (r0Phi t).1.1).1, (r0Phi t).1.2), (fwd xmssFix xO (r0Phi t).1.1).2),
      (r0Phi t).2) :
        HonestTable × RE → (PX × (ValPos → Digest)) × (CoinSlots R0.RLabel × SeedKS))
    (fun t ↦ r0G treeQ 18 t ∧ ¬TrialHidGood (pubR (r0E t).1) (r0E t).2.1)
    (fun z : (PX × (ValPos → Digest)) × (CoinSlots R0.RLabel × SeedKS) ↦
      ¬TrialHidGoodV (pubX z.1.1) z.1.2)
    (fun _ h ↦ h.2) fun t₁ t₂ h₁ h₂ e ↦ by
      have hf : fwd xmssFix xO (r0Phi t₁).1.1 = fwd xmssFix xO (r0Phi t₂).1.1 :=
        Prod.ext (congrArg (fun z ↦ z.1.1.1) e :) (congrArg (fun z ↦ z.1.2) e :)
      have hθ := injOn_fwd xO_consistent (good_of_xGood h₁.1.2.2.1) (good_of_xGood h₂.1.2.2.1) hf
      exact r0Phi.injective (Prod.ext (Prod.ext hθ (congrArg (fun z ↦ z.1.1.2) e :))
        (congrArg (fun z ↦ z.2) e :))
  have hP := card_filter_pad (W := CoinSlots R0.RLabel × SeedKS)
    (fun y : PX × (ValPos → Digest) ↦ ¬TrialHidGoodV (pubX y.1) y.2)
  have hN : Fintype.card (HonestTable × RE) =
      Fintype.card (PX × (ValPos → Digest)) * Fintype.card (CoinSlots R0.RLabel × SeedKS) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr (r0Phi.trans (pxEquiv.symm.prodCongr (Equiv.refl _)))
  calc (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦
          r0G treeQ 18 t ∧ ¬TrialHidGood (pubR (r0E t).1) (r0E t).2.1).card
      ≤ (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun z : (PX × (ValPos → Digest)) × (CoinSlots R0.RLabel × SeedKS) ↦
            ¬TrialHidGoodV (pubX z.1.1) z.1.2).card := by
        gcongr
    _ = (((Fintype.card (PX × (ValPos → Digest)) * Fintype.card (CoinSlots R0.RLabel × SeedKS) :
          ℕ) : ℝ≥0∞))⁻¹ * (((Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
            ¬TrialHidGoodV (pubX y.1) y.2).card *
              Fintype.card (CoinSlots R0.RLabel × SeedKS) : ℕ) :
              ℝ≥0∞) := by
        rw [hP, hN, Nat.cast_mul, Nat.cast_mul]
    _ = _ := natCast_mul_inv_mul_cancel _ _ _ Fintype.card_ne_zero

end trialGoodFrac

end Quantum.Xmss.Assembly

end
