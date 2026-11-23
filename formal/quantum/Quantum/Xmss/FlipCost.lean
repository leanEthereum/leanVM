module

public import Quantum.Xmss.Events

@[expose] public section

/-!
# Flip costs of the classical ports for the XMSS event

S5's classical ports cost `flipCost S K P σ = ε + p + 2 √(ε' p)` (`Hardwired/Read.lean`), with the
flip operator `F = ∑ᵣ K rᴴ Q K r - Q`, `ε = tr (P' F P' σ)`, `ε' = tr (P' F P F P' σ)`,
`p = tr (P σ)` and `P' = 1 - P`. This file bounds these terms by the per-state flip counts of
`Quantum.Xmss.Events`.

* **Program ports** (`flipCost_prog_le`): the Kraus operators move basis states to basis states,
  so `F` is diagonal; with `P = 0` the cost is the weight of the states the program moves into the
  event. Averaged over the programmed value (`sum_flipCost_prog_le`, `sum_flipCost_prog_le_card`):
  `2^-128 tr σ` for `h` (`flipCost_programH_avg_le`), `0` for intermediate cells of multi-block
  honest paths (`flipCost_programH_short`), capacity-scale for `k`, `k'`
  (`flipCost_programK_avg_le`, `flipCost_programK'_avg_le`).
* **Read ports** (`CellRead`, `re_trace_eps_le`, `re_trace_eps'_le`): a read of one cell is
  `C |o⟩⟨o| C` on the cell (`C` the compression) and moves the memory; its Gram operator is block
  diagonal in the rest of the state and `C diag(g) C` on the cell (`gram_apply`). With `P` the
  states whose cell is recorded or whose rest is not selected, both `ε` and `ε'` are at most
  `∑ Δ / N σ_ss` over the empty cells, `Δ` the number of outcomes that change the event for some
  cell content (`chw_le_card`). For the selecting read of a message-digest trial
  (`flipCost_selectRead_le`): `E = ∑_{SelectRead, ∉ Bad} msgCount · 2^960 / |X| σ_ss`, at most
  `(N + t) 2^-128 tr σ` on states with at most `N` hardwired and `t` database entries per function
  (`selectReadE_le`).
-/

open Matrix
open scoped Kronecker ENNReal ComplexOrder

namespace Quantum.Sponge

open Quantum

/-! ## The one-cell compression, as real entries -/

section cr

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- The entries of the one-cell compression `cellCompress Y`, as real numbers. -/
noncomputable def cr : Option Y → Option Y → ℝ
  | none, none => 0
  | none, some _ => (Real.sqrt (Fintype.card Y))⁻¹
  | some _, none => (Real.sqrt (Fintype.card Y))⁻¹
  | some y, some y' => (if y = y' then 1 else 0) - (Fintype.card Y : ℝ)⁻¹

theorem cellCompress_eq_cr (a b : Option Y) : cellCompress Y a b = (cr a b : ℂ) := by
  rcases a with _ | y <;> rcases b with _ | y'
  · simp [cr]
  · simp [cr, cellAmp]
  · simp [cr, cellAmp]
  · simp only [cellCompress_some_some, cr]
    split_ifs <;> push_cast <;> ring

theorem cr_comm (a b : Option Y) : cr a b = cr b a := by
  rcases a with _ | y <;> rcases b with _ | y' <;> simp [cr, eq_comm]

theorem cr_none_some_sq (y : Y) : cr none (some y) ^ 2 = (Fintype.card Y : ℝ)⁻¹ := by
  simp [cr, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- The columns of the compression have norm one. -/
theorem sum_cr_sq [Nonempty Y] (y : Y) : ∑ a, cr a (some y) ^ 2 = 1 := by
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.2 Fintype.card_pos
  rw [Fintype.sum_option, cr_none_some_sq]
  have h : ∀ y' : Y, cr (some y') (some y) ^ 2 =
      (if y' = y then 1 else 0) * (1 - 2 * (Fintype.card Y : ℝ)⁻¹) +
        ((Fintype.card Y : ℝ)⁻¹) ^ 2 := fun y' ↦ by
    simp only [cr]
    split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

end cr

/-! ## Reads of one cell -/

section core

variable {n Y R M0 : Type} [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y]
  [Fintype R] [DecidableEq R] [Fintype M0] [DecidableEq M0]

/-- The indicator of a set of basis states. -/
def ind (S : Set n) [DecidablePred (· ∈ S)] (s : n) : ℝ := if s ∈ S then 1 else 0

/-- **A read of one cell.** The basis states split as `e s = (cell, rest)`. The Kraus operator of
outcome `o` and memory `m0` acts, on the columns of active rests, as `C |o⟩⟨o| C` on the cell
(`C` the compression), accepts the memory `μ = m0` and moves the rest by `τ o`, injectively for a
fixed memory; it keeps the active rests apart from the others. -/
structure CellRead (e : n ≃ Option Y × R) (act : R → Prop) (μ : R → M0) (τ : Option Y → R → R)
    (K : Option Y × M0 → Matrix n n ℂ) : Prop where
  entry : ∀ o m0 t s, act (e s).2 → K (o, m0) t s =
    if μ (e s).2 = m0 ∧ (e t).2 = τ o (e s).2 then ((cr (e t).1 o * cr o (e s).1 : ℝ) : ℂ) else 0
  inj : ∀ o r r', μ r = μ r' → τ o r = τ o r' → r = r'
  act_τ : ∀ o r, act r → act (τ o r)
  off : ∀ i t' t, ¬ act (e t).2 → K i t' t ≠ 0 → ¬ act (e t').2

variable {e : n ≃ Option Y × R} {act : R → Prop} {μ : R → M0} {τ : Option Y → R → R}
  {K : Option Y × M0 → Matrix n n ℂ} (S : Set n) [DecidablePred (· ∈ S)]

variable (e τ) in
/-- The weight of the event in the image of outcome `o`, from the rest `r`:
`g o r = ∑ₐ C(a, o)² 1_S (a, τ o r)`. -/
noncomputable def gw (o : Option Y) (r : R) : ℝ :=
  ∑ a, cr a o ^ 2 * ind S (e.symm (a, τ o r))

/-- The event projector. -/
noncomputable def indProj : Matrix n n ℂ := diagonal fun s ↦ ((ind S s : ℝ) : ℂ)

omit [Fintype n] [DecidableEq n] [Fintype R] [Fintype M0] in
theorem cellRead_ne_zero (h : CellRead e act μ τ K) {i : Option Y × M0} {t s : n}
    (hs : act (e s).2) (hK : K i t s ≠ 0) : μ (e s).2 = i.2 ∧ (e t).2 = τ i.1 (e s).2 := by
  rw [show i = (i.1, i.2) from rfl, h.entry _ _ _ _ hs] at hK
  by_contra hc
  exact hK (ite_eq_right_of_eq_false _ _ (eq_false hc))

/-- **The Gram operator of a cell read, on an active column**: block diagonal in the rest, and
`C diag(g) C` on the cell. -/
theorem gram_apply (h : CellRead e act μ τ K) {s : n} (hs : act (e s).2) (t : n) :
    (∑ i, (K i)ᴴ * indProj S * K i) t s =
      if (e t).2 = (e s).2 then
        ((∑ o, cr (e t).1 o * gw e τ S o (e s).2 * cr o (e s).1 : ℝ) : ℂ) else 0 := by
  have hterm : ∀ i, ((K i)ᴴ * indProj S * K i) t s =
      ∑ u, star (K i u t) * ((ind S u : ℝ) : ℂ) * K i u s := fun i ↦ by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [indProj, mul_diagonal, conjTranspose_apply]
  simp only [Matrix.sum_apply, hterm]
  split_ifs with hts
  · have ht : act (e t).2 := hts ▸ hs
    rw [Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    rw [Finset.sum_eq_single (μ (e s).2)]
    · rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm,
        Finset.sum_eq_single (τ o (e s).2)]
      · simp only [gw]
        push_cast
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [h.entry _ _ _ _ ht, h.entry _ _ _ _ hs]
        simp only [Equiv.apply_symm_apply, hts, and_self, ↓reduceIte, Complex.star_def,
          Complex.conj_ofReal]
        push_cast
        rw [cr_comm o (e t).1]
        ring
      · intro r _ hr
        refine Finset.sum_eq_zero fun a _ ↦ ?_
        rw [h.entry _ _ _ _ hs]
        simp [hr]
      · simp
    · intro m0 _ hm
      refine Finset.sum_eq_zero fun u _ ↦ ?_
      rw [h.entry _ _ _ _ hs]
      simp [Ne.symm hm]
    · simp
  · refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun u _ ↦ ?_
    by_cases hKs : K i u s = 0
    · simp [hKs]
    obtain ⟨hμ, hτ⟩ := cellRead_ne_zero h hs hKs
    have hKt : K i u t = 0 := by
      by_contra hKt
      by_cases ht : act (e t).2
      · obtain ⟨hμ', hτ'⟩ := cellRead_ne_zero h ht hKt
        exact hts (h.inj i.1 _ _ (hμ'.trans hμ.symm) (hτ'.symm.trans hτ))
      · exact h.off i u t ht hKt (hτ ▸ h.act_τ _ _ hs)
    simp [hKt]

variable (e τ) in
/-- The weight of the event at the empty cell of the rest `r`. -/
noncomputable def q0 (r : R) : ℝ := ind S (e.symm (none, r))

variable (e τ) in
/-- The change of the event under outcome `some y` from the empty cell of the rest `r`, weighted
by the squared column of the compression: `δ y r = ∑ₐ C(a, y)² 1[1_S (a, τ y r) ≠ 1_S (⊥, r)]`. -/
noncomputable def dw (y : Y) (r : R) : ℝ :=
  ∑ a, cr a (some y) ^ 2 * (if ind S (e.symm (a, τ (some y) r)) = q0 e S r then 0 else 1)

variable (e τ) in
/-- **The change weight of the rest `r`**: `Δ r = ∑ y, δ y r`. -/
noncomputable def chw (r : R) : ℝ := ∑ y, dw e τ S y r

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
theorem ind_mem (s : n) : ind S s = 0 ∨ ind S s = 1 := by
  unfold ind
  split_ifs <;> simp

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
theorem ind_nonneg (s : n) : 0 ≤ ind S s := by
  rcases ind_mem S s with h | h <;> simp [h]

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
theorem ind_le_one (s : n) : ind S s ≤ 1 := by
  rcases ind_mem S s with h | h <;> simp [h]

section bounds

variable [Nonempty Y]

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
theorem dw_le_one (y : Y) (r : R) : dw e τ S y r ≤ 1 := by
  rw [← sum_cr_sq y, dw]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  have := sq_nonneg (cr a (some y))
  split_ifs <;> nlinarith

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
theorem abs_gw_sub_le (y : Y) (r : R) : |gw e τ S (some y) r - q0 e S r| ≤ dw e τ S y r := by
  have h : gw e τ S (some y) r - q0 e S r =
      ∑ a, cr a (some y) ^ 2 * (ind S (e.symm (a, τ (some y) r)) - q0 e S r) := by
    have hq : q0 e S r = ∑ a, cr a (some y) ^ 2 * q0 e S r := by
      rw [← Finset.sum_mul, sum_cr_sq, one_mul]
    conv_lhs => rw [hq, gw, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  rw [h, dw]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  split_ifs with he
  · rw [he, sub_self, abs_zero]
  · rcases ind_mem S (e.symm (a, τ (some y) r)) with h1 | h1 <;>
      rcases ind_mem S (e.symm (none, r)) with h2 | h2 <;> simp_all [q0]

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
theorem sq_gw_sub_le (y : Y) (r : R) : (gw e τ S (some y) r - q0 e S r) ^ 2 ≤ dw e τ S y r := by
  have h1 := abs_gw_sub_le S (e := e) (τ := τ) y r
  have h2 := dw_le_one S (e := e) (τ := τ) y r
  have h3 := abs_nonneg (gw e τ S (some y) r - q0 e S r)
  rw [← sq_abs]
  nlinarith

/-- The mean minimizes the sum of squares. -/
theorem sum_sq_sub_mean_le {ι : Type} [Fintype ι] [Nonempty ι] (g : ι → ℝ) (c : ℝ) :
    ∑ i, (g i - (∑ j, g j) / Fintype.card ι) ^ 2 ≤ ∑ i, (g i - c) ^ 2 := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  set m := (∑ j, g j) / Fintype.card ι
  have hm : ∑ j, g j = Fintype.card ι * m := by
    simp only [m]
    field_simp
  have key : ∑ i, (g i - c) ^ 2 - ∑ i, (g i - m) ^ 2 = Fintype.card ι * (m - c) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    have : ∀ i, (g i - c) ^ 2 - (g i - m) ^ 2 = 2 * (m - c) * g i + (c ^ 2 - m ^ 2) :=
      fun i ↦ by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hm, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  nlinarith [sq_nonneg (m - c)]

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
/-- The diagonal flip of an empty cell is at most `Δ / N`. -/
theorem diag_le (r : R) :
    (∑ y, gw e τ S (some y) r) / Fintype.card Y - q0 e S r ≤ chw e τ S r / Fintype.card Y := by
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.2 Fintype.card_pos
  rw [sub_le_iff_le_add, div_le_iff₀ hN, add_mul, div_mul_cancel₀ _ hN.ne', chw]
  have : q0 e S r * Fintype.card Y = ∑ _y : Y, q0 e S r := by
    simp [mul_comm]
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  have := abs_gw_sub_le S (e := e) (τ := τ) y r
  linarith [le_abs_self (gw e τ S (some y) r - q0 e S r)]

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
/-- The flips from an empty cell to a recorded one weigh at most `Δ / N`. -/
theorem offdiag_le (r : R) :
    ∑ y, ((gw e τ S (some y) r - (∑ y', gw e τ S (some y') r) / Fintype.card Y) /
      Real.sqrt (Fintype.card Y)) ^ 2 ≤ chw e τ S r / Fintype.card Y := by
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.2 Fintype.card_pos
  simp only [div_pow, Real.sq_sqrt hN.le, ← Finset.sum_div]
  refine div_le_div_of_nonneg_right ((sum_sq_sub_mean_le _ (q0 e S r)).trans ?_) hN.le
  exact Finset.sum_le_sum fun y _ ↦ sq_gw_sub_le S y r

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
/-- **The change weight is at most the number of outcomes that change the event** for some cell
content. -/
theorem chw_le_card (r : R) :
    chw e τ S r ≤ (Finset.univ.filter fun y : Y ↦
      ∃ a, ind S (e.symm (a, τ (some y) r)) ≠ q0 e S r).card := by
  rw [chw, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  split_ifs with h
  · exact (dw_le_one S y r).trans (by norm_num)
  · simp only [not_exists, not_not] at h
    simp [dw, h]

end bounds

/-! ### The flip operator on the empty cells -/

variable (K) in
/-- The flip operator `F = ∑ᵢ Kᵢᴴ Q Kᵢ - Q` of the event `S`. -/
noncomputable def flipOp : Matrix n n ℂ := ∑ i, (K i)ᴴ * indProj S * K i - indProj S

omit [DecidableEq Y] [Fintype R] [DecidableEq R] [DecidableEq M0] in
theorem conjTranspose_flipOp : (flipOp K S)ᴴ = flipOp K S := by
  have hQ : (indProj S : Matrix n n ℂ)ᴴ = indProj S := by
    rw [indProj, diagonal_conjTranspose]
    congr 1
    funext s
    simp [Complex.conj_ofReal]
  simp only [flipOp, conjTranspose_sub, conjTranspose_sum, conjTranspose_mul,
    conjTranspose_conjTranspose, hQ, Matrix.mul_assoc]

omit [DecidableEq Y] [Fintype R] [DecidableEq R] [DecidableEq M0] in
theorem flipOp_symm (t s : n) : flipOp K S t s = star (flipOp K S s t) := by
  rw [← conjTranspose_apply, conjTranspose_flipOp]

theorem flipOp_apply (h : CellRead e act μ τ K) {s : n} (hs : act (e s).2) (t : n) :
    flipOp K S t s = (if (e t).2 = (e s).2 then
        ((∑ o, cr (e t).1 o * gw e τ S o (e s).2 * cr o (e s).1 : ℝ) : ℂ) else 0) -
      if t = s then ((ind S t : ℝ) : ℂ) else 0 := by
  rw [flipOp, Matrix.sub_apply, gram_apply S h hs, indProj, diagonal_apply]

theorem flipOp_eq_zero (h : CellRead e act μ τ K) {s t : n} (hs : act (e s).2)
    (ht : (e t).2 ≠ (e s).2) : flipOp K S t s = 0 := by
  have hts : t ≠ s := fun h' ↦ ht (h' ▸ rfl)
  rw [flipOp_apply S h hs, ite_eq_right ht, ite_eq_right hts, sub_zero]

omit [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y] [Fintype R] [DecidableEq R] in
theorem eq_of_rest {s t : n} (hr : (e t).2 = (e s).2) (hc : (e t).1 = (e s).1) : t = s :=
  e.injective (Prod.ext hc hr)

variable (gd : R → Prop) [DecidablePred gd]

variable (e) in
/-- The empty cells of the selected rests. -/
def pe (s : n) : ℂ := if gd (e s).2 ∧ (e s).1 = none then 1 else 0

variable (e) in
/-- The complement of `pe`. -/
def pp (s : n) : ℂ := if gd (e s).2 ∧ (e s).1 = none then 0 else 1

variable (e) in
/-- The projector on the empty cells of the selected rests. -/
noncomputable def projE : Matrix n n ℂ := diagonal (pe e gd)

variable (e) in
/-- **The projector `P` of the read**: the states whose cell is recorded or whose rest is not
selected. -/
noncomputable def readP : Matrix n n ℂ := diagonal (pp e gd)

omit [Fintype n] [Fintype Y] [DecidableEq Y] [Fintype R] [DecidableEq R] in
theorem one_sub_readP : 1 - readP e gd = projE e gd := by
  ext i j
  simp only [readP, projE, pe, pp, Matrix.sub_apply, Matrix.one_apply, diagonal_apply]
  split_ifs <;> simp

omit [Fintype Y] [DecidableEq Y] [Fintype R] [DecidableEq R] in
theorem readP_proj : (readP e gd)ᴴ = readP e gd ∧ readP e gd * readP e gd = readP e gd := by
  refine ⟨?_, ?_⟩
  · rw [readP, diagonal_conjTranspose]
    congr 1
    funext s
    simp only [pp, Pi.star_apply]
    split_ifs <;> simp
  · rw [readP, diagonal_mul_diagonal]
    congr 1
    funext s
    simp only [pp]
    split_ifs <;> simp

variable [Nonempty Y]

omit [DecidablePred gd] in
theorem flipOp_diag (h : CellRead e act μ τ K) (hgd : ∀ r, gd r → act r) {s : n}
    (hs : gd (e s).2 ∧ (e s).1 = none) :
    flipOp K S s s = (((∑ y, gw e τ S (some y) (e s).2) / Fintype.card Y - q0 e S (e s).2 : ℝ) :
      ℂ) := by
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.2 Fintype.card_pos
  rw [flipOp_apply S h (hgd _ hs.1), ite_eq_left rfl, ite_eq_left rfl, hs.2, Fintype.sum_option]
  have hq : ind S s = q0 e S (e s).2 := by
    rw [q0, ← hs.2, Prod.mk.eta, Equiv.symm_apply_apply]
  have hsum : ∑ y, cr none (some y) * gw e τ S (some y) (e s).2 * cr (some y) none =
      (∑ y, gw e τ S (some y) (e s).2) / Fintype.card Y := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [cr_comm (some y) none, div_eq_mul_inv, ← cr_none_some_sq y]
    ring
  rw [hq, hsum]
  simp only [cr, zero_mul, zero_add]
  push_cast
  ring

omit [DecidablePred gd] [Nonempty Y] in
theorem flipOp_some (h : CellRead e act μ τ K) (hgd : ∀ r, gd r → act r) {s t : n}
    (hs : gd (e s).2 ∧ (e s).1 = none) (ht : (e t).2 = (e s).2) {y : Y} (hy : (e t).1 = some y) :
    flipOp K S t s = (((gw e τ S (some y) (e s).2 -
      (∑ y', gw e τ S (some y') (e s).2) / Fintype.card Y) / Real.sqrt (Fintype.card Y) : ℝ) :
        ℂ) := by
  have hts : t ≠ s := fun h' ↦ by rw [h', hs.2] at hy; cases hy
  rw [flipOp_apply S h (hgd _ hs.1), ite_eq_left ht, ite_eq_right hts, sub_zero, hs.2, hy,
    Fintype.sum_option]
  congr 1
  simp only [cr, mul_zero, zero_add]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_mul, ← Finset.mul_sum, div_eq_mul_inv, div_eq_mul_inv]
  ring

omit [DecidableEq n] [Fintype R] [DecidableEq R] [DecidableEq M0] [Nonempty Y] in
theorem trace_mul_apply (A σ : Matrix n n ℂ) (s : n) :
    diag (A * σ) s = ∑ t, A s t * σ t s :=
  Matrix.mul_apply

/-- **The `ε` term of a cell read**: `re tr (P' F P' σ) ≤ ∑` over the empty cells of selected
rests of `Δ / N · σ_ss`. -/
theorem re_trace_eps_le (h : CellRead e act μ τ K) (hgd : ∀ r, gd r → act r) {σ : Matrix n n ℂ}
    (hσ : σ.PosSemidef) :
    ((1 - readP e gd) * flipOp K S * (1 - readP e gd) * σ).trace.re ≤
      ∑ s, if gd (e s).2 ∧ (e s).1 = none then
        chw e τ S (e s).2 / Fintype.card Y * (σ s s).re else 0 := by
  rw [one_sub_readP, Matrix.trace, Complex.re_sum]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [trace_mul_apply, Finset.sum_eq_single s]
  · rw [projE, mul_diagonal, diagonal_mul]
    by_cases hs : gd (e s).2 ∧ (e s).1 = none
    · rw [ite_eq_left hs, flipOp_diag S gd h hgd hs]
      simp only [pe, hs, and_self, ↓reduceIte, one_mul, mul_one, Complex.re_ofReal_mul]
      exact mul_le_mul_of_nonneg_right (diag_le S _) (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    · simp [pe, hs]
  · intro t _ hts
    rw [projE, mul_diagonal, diagonal_mul]
    by_cases hs : gd (e s).2 ∧ (e s).1 = none
    · by_cases ht : gd (e t).2 ∧ (e t).1 = none
      · have hr : (e s).2 ≠ (e t).2 := fun hr ↦ hts (eq_of_rest hr (hs.2.trans ht.2.symm)).symm
        rw [flipOp_eq_zero S h (hgd _ ht.1) hr]
        simp
      · simp [pe, ht]
    · simp [pe, hs]
  · simp

/-- **The `ε'` term of a cell read**: `re tr (P' F P F P' σ) ≤ ∑` over the empty cells of selected
rests of `Δ / N · σ_ss`. -/
theorem re_trace_eps'_le (h : CellRead e act μ τ K) (hgd : ∀ r, gd r → act r) {σ : Matrix n n ℂ}
    (hσ : σ.PosSemidef) :
    ((1 - readP e gd) * flipOp K S * readP e gd * flipOp K S * (1 - readP e gd) * σ).trace.re ≤
      ∑ s, if gd (e s).2 ∧ (e s).1 = none then
        chw e τ S (e s).2 / Fintype.card Y * (σ s s).re else 0 := by
  have hA : ∀ s s', (projE e gd * flipOp K S * readP e gd * flipOp K S * projE e gd) s s' =
      (∑ t, pe e gd s * flipOp K S s t * pp e gd t * flipOp K S t s') * pe e gd s' := by
    intro s s'
    rw [projE, mul_diagonal, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [readP, mul_diagonal, diagonal_mul]
  /- Entries vanish between distinct empty cells. -/
  have hzero : ∀ s s' t, gd (e s).2 ∧ (e s).1 = none → gd (e s').2 ∧ (e s').1 = none →
      s' ≠ s → flipOp K S s t * pp e gd t * flipOp K S t s' = 0 := by
    intro s s' t hs hs' hne
    by_cases ht : gd (e t).2 ∧ (e t).1 = none
    · simp [pp, ht]
    by_cases hr : (e t).2 = (e s').2
    · have hact : act (e t).2 := hr ▸ hgd _ hs'.1
      by_cases hr' : (e s).2 = (e t).2
      · exact absurd (eq_of_rest (hr'.trans hr) (hs.2.trans hs'.2.symm)) hne.symm
      · rw [flipOp_eq_zero S h hact hr']
        simp
    · rw [flipOp_eq_zero S h (hgd _ hs'.1) hr]
      simp
  /- The diagonal entry is the weight of the flips into recorded cells. -/
  have hdiag : ∀ s, gd (e s).2 ∧ (e s).1 = none →
      ∑ t, flipOp K S s t * pp e gd t * flipOp K S t s =
        ((∑ y, ((gw e τ S (some y) (e s).2 -
          (∑ y', gw e τ S (some y') (e s).2) / Fintype.card Y) /
            Real.sqrt (Fintype.card Y)) ^ 2 : ℝ) : ℂ) := by
    intro s hs
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_option]
    have hnone : ∑ r, flipOp K S s (e.symm (none, r)) * pp e gd (e.symm (none, r)) *
        flipOp K S (e.symm (none, r)) s = 0 := by
      refine Finset.sum_eq_zero fun r _ ↦ ?_
      by_cases hr : r = (e s).2
      · subst hr
        have : e.symm (none, (e s).2) = s := by rw [← hs.2, Prod.mk.eta, Equiv.symm_apply_apply]
        simp [this, pp, hs]
      · rw [flipOp_eq_zero S h (hgd _ hs.1) (by simpa using hr)]
        simp
    rw [hnone, zero_add]
    push_cast
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Finset.sum_eq_single (e s).2]
    · have ht2 : (e (e.symm (some y, (e s).2))).2 = (e s).2 := by simp
      have ht1 : (e (e.symm (some y, (e s).2))).1 = some y := by simp
      have hpp : pp e gd (e.symm (some y, (e s).2)) = 1 := by simp [pp]
      rw [flipOp_symm S s, flipOp_some S gd h hgd hs ht2 ht1, hpp, Complex.star_def,
        Complex.conj_ofReal]
      push_cast
      ring
    · intro r _ hr
      rw [flipOp_eq_zero S h (hgd _ hs.1) (by simpa using hr)]
      simp
    · simp
  rw [one_sub_readP, Matrix.trace, Complex.re_sum]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [trace_mul_apply, Finset.sum_eq_single s]
  · rw [hA]
    by_cases hs : gd (e s).2 ∧ (e s).1 = none
    · have hpe : pe e gd s = 1 := by simp [pe, hs]
      simp only [hpe, one_mul, mul_one]
      rw [hdiag s hs, Complex.re_ofReal_mul, ite_eq_left hs]
      exact mul_le_mul_of_nonneg_right (offdiag_le S _) (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    · simp [pe, hs]
  · intro s' _ hs's
    rw [hA]
    by_cases hs : gd (e s).2 ∧ (e s).1 = none
    · by_cases hs' : gd (e s').2 ∧ (e s').1 = none
      · rw [Finset.sum_eq_zero fun t _ ↦ ?_]
        · simp
        rw [mul_assoc (pe e gd s), mul_assoc (pe e gd s), hzero s s' t hs hs' hs's, mul_zero]
      · simp [pe, hs']
    · simp [pe, hs]
  · simp

end core

/-! ## One-cell operators -/

section cells

variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]

/-- An entry of a one-cell compression: the compression of the cell, if the other cells agree. -/
theorem compressAt_apply' (x : A) (D E : Database A Y) :
    compressAt Y x D E = if ∀ a, a ≠ x → D a = E a then cellCompress Y (D x) (E x) else 0 := by
  rw [compressAt, piKron_apply]
  by_cases hc : ∀ a, a ≠ x → D a = E a
  · rw [ite_eq_left hc, Finset.prod_eq_single x (fun a _ ha ↦ by
      rw [Pi.mulSingle_eq_of_ne ha, hc a ha, Matrix.one_apply_eq]) (by simp),
      Pi.mulSingle_eq_same]
  · rw [ite_eq_right hc]
    simp only [not_forall] at hc
    obtain ⟨a, ha, hne⟩ := hc
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by
      rw [Pi.mulSingle_eq_of_ne ha, Matrix.one_apply_ne hne])

/-- **An entry of a read of a cell that is not hardwired**: `C(D' a, o) C(o, D a)` if the other
cells agree. -/
theorem cellRead_apply_none [Nonempty Y] {w : Database A Y} {a : A} (hw : w a = none)
    (o : Option Y) (D' D : Database A Y) :
    cellRead w a o D' D = if ∀ b, b ≠ a → D' b = D b then
      ((cr (D' a) o * cr o (D a) : ℝ) : ℂ) else 0 := by
  rw [cellRead, hw]
  dsimp only
  rw [Matrix.mul_apply]
  simp only [mul_diagonal]
  rw [Finset.sum_eq_single (Function.update D' a o)]
  · have h1 : ∀ b, b ≠ a → D' b = Function.update D' a o b :=
      fun b hb ↦ (Function.update_of_ne hb o D').symm
    have h2 : (∀ b, b ≠ a → Function.update D' a o b = D b) ↔ ∀ b, b ≠ a → D' b = D b :=
      forall_congr' fun b ↦ imp_congr_right fun hb ↦ by rw [Function.update_of_ne hb]
    rw [compressAt_apply' a D', compressAt_apply' a (Function.update D' a o), ite_eq_left h1,
      Function.update_self, ite_eq_left (rfl : o = o), ite_cond_congr (propext h2)]
    split_ifs
    · rw [cellCompress_eq_cr, cellCompress_eq_cr]
      push_cast
      ring
    · simp
  · intro E _ hE
    by_cases ho : E a = o
    · rw [compressAt_apply' a D' E, ite_eq_right]
      · simp
      intro h
      refine hE (funext fun b ↦ ?_)
      by_cases hb : b = a
      · subst hb
        simp [ho]
      · rw [Function.update_of_ne hb, h b hb]
    · rw [ite_eq_right ho, mul_zero, zero_mul]
  · simp

end cells

/-! ## The read port of `h` as a cell read -/

section readH

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

omit [Fintype M] in
theorem readKrausH_apply [Nonempty X] (z : Z) (upd : M → Option X → M) (r : Option X × M)
    (s' s : HwReg X Z M) (hw : s.2.1.1 z = none) :
    readKrausH z upd r s' s = if s.2.2 = r.2 ∧ s'.2 = (s.2.1, upd r.2 r.1) ∧
      (∀ b, b ≠ z → s'.1.1 b = s.1.1 b) ∧ s'.1.2 = s.1.2 then
        ((cr (s'.1.1 z) r.1 * cr r.1 (s.1.1 z) : ℝ) : ℂ) else 0 := by
  rw [readKrausH, clsKraus_apply, kroneckerMap_apply, cellRead_apply_none hw, Matrix.one_apply]
  by_cases h1 : s.2.2 = r.2 ∧ s'.2 = (s.2.1, upd r.2 r.1)
  · rw [ite_eq_left h1]
    by_cases h2 : ∀ b, b ≠ z → s'.1.1 b = s.1.1 b
    · by_cases h3 : s'.1.2 = s.1.2
      · rw [ite_eq_left h2, ite_eq_left h3, ite_eq_left ⟨h1.1, h1.2, h2, h3⟩, mul_one]
      · rw [ite_eq_right h3, mul_zero]
        exact (ite_eq_right fun h ↦ h3 h.2.2.2).symm
    · rw [ite_eq_right h2, zero_mul]
      exact (ite_eq_right fun h ↦ h2 h.2.2.1).symm
  · rw [ite_eq_right h1]
    exact (ite_eq_right fun h ↦ h1 ⟨h.1, h.2.1⟩).symm

omit [Fintype M] in
theorem readKrausH_hw (z : Z) (upd : M → Option X → M) (r : Option X × M) {s' s : HwReg X Z M}
    (h : readKrausH z upd r s' s ≠ 0) : s'.2.1 = s.2.1 := by
  rw [readKrausH, clsKraus_apply] at h
  split_ifs at h with hc
  · rw [hc.2]
  · exact absurd rfl h

variable (z : Z)

variable (X M) in
/-- The rest of a state of the hardwired register beside the cell `z` of `h`: the other cells of
`h`, the databases of `k` and `k'`, the hardwired cells and the memory. -/
abbrev RestH := ({j // j ≠ z} → Option X) × Database X Z × Database X Z × Hw X Z × M

instance : DecidableEq ({j // j ≠ z} → Option X) := Fintype.decidablePiFintype

instance : DecidableEq (RestH X M z) :=
  @instDecidableEqProd _ _ inferInstance <| @instDecidableEqProd _ _ inferInstance <|
    @instDecidableEqProd _ _ inferInstance <| @instDecidableEqProd _ _ inferInstance inferInstance

instance : Fintype (RestH X M z) := by
  unfold RestH Hw DbReg Database
  infer_instance

/-- Splitting a state (with the trivial public register) into the cell `z` of `h` and the rest. -/
def splitH' : Unit × HwReg X Z M ≃ Option X × RestH X M z where
  toFun q := (q.2.1.1 z, (fun j ↦ q.2.1.1 j, q.2.1.2.1, q.2.1.2.2, q.2.2.1, q.2.2.2))
  invFun p := ((), ((fun x ↦ if h : x = z then p.1 else p.2.1 ⟨x, h⟩, p.2.2.1, p.2.2.2.1),
    p.2.2.2.2.1, p.2.2.2.2.2))
  left_inv q := by
    obtain ⟨⟨⟩, ⟨dh, dk, dk'⟩, W, m⟩ := q
    simp only [Prod.mk.injEq, and_true, true_and]
    funext x
    by_cases hx : x = z
    · subst hx
      simp
    · simp [hx]
  right_inv p := by
    obtain ⟨a, f, dk, dk', W, m⟩ := p
    simp only [↓reduceDIte, Prod.mk.injEq, true_and, and_true]
    funext j
    simp [j.2]

/-- The memory of a rest. -/
def memH (r : RestH X M z) : M := r.2.2.2.2

/-- A rest whose cell `z` is not hardwired. -/
def actH (r : RestH X M z) : Prop := r.2.2.2.1.1 z = none

/-- The move of a rest under a read with outcome `o`: the memory is updated. -/
def tauH (upd : M → Option X → M) (o : Option X) (r : RestH X M z) : RestH X M z :=
  (r.1, r.2.1, r.2.2.1, r.2.2.2.1, upd r.2.2.2.2 o)

omit [Fintype M] in
/-- **The read port of `h` at cell `z` is a cell read.** -/
theorem cellRead_readH [Nonempty X] (upd : M → Option X → M) :
    CellRead (splitH' z) (actH z) (memH z) (tauH z upd)
      (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r) where
  entry o m0 t s hs := by
    obtain ⟨⟨⟩, ⟨dh', dk', dk₂'⟩, W', m'⟩ := t
    obtain ⟨⟨⟩, ⟨dh, dk, dk₂⟩, W, m⟩ := s
    change W.1 z = none at hs
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z upd (o, m0)) _ _ = _
    rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, readKrausH_apply _ _ _ _ _ hs]
    simp only [splitH', Equiv.coe_fn_mk, memH, tauH]
    refine ite_cond_congr (propext ?_)
    have hf : ((fun j : {j // j ≠ z} ↦ dh' j) = fun j : {j // j ≠ z} ↦ dh j) ↔
        ∀ b, b ≠ z → dh' b = dh b :=
      ⟨fun h b hb ↦ congrFun h ⟨b, hb⟩, fun h ↦ funext fun j ↦ h j j.2⟩
    simp only [Prod.mk.injEq, hf]
    constructor
    · rintro ⟨rfl, ⟨rfl, rfl⟩, h3, rfl, rfl⟩
      exact ⟨rfl, h3, rfl, rfl, rfl, rfl⟩
    · rintro ⟨rfl, h3, rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, ⟨rfl, rfl⟩, h3, rfl, rfl⟩
  inj o r r' hμ hτ := by
    obtain ⟨f, dk, dk', W, m⟩ := r
    obtain ⟨f', dk₁, dk₁', W', m'⟩ := r'
    simp only [tauH, Prod.mk.injEq] at hτ
    simp only [memH] at hμ
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hτ
    rw [hμ]
  act_τ o r h := h
  off i t' t ht hK := by
    have h := readKrausH_hw z upd i (s' := t'.2) (s := t.2) fun h0 ↦ hK (by
      change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z upd i) _ _ = 0
      rw [kroneckerMap_apply, h0, mul_zero])
    change ¬ t'.2.2.1.1 z = none
    rw [h]
    exact ht

omit [Fintype X] [DecidableEq X] [Fintype Z] [Fintype M] [DecidableEq M] in
theorem splitH'_apply_fst (q : Unit × HwReg X Z M) : (splitH' z q).1 = q.2.1.1 z := rfl

omit [Fintype X] [DecidableEq X] [Fintype Z] [Fintype M] [DecidableEq M] in
/-- Rebuilding a state from its rest and a cell content after a read. -/
theorem splitH'_symm_tau (upd : M → Option X → M) (q : Unit × HwReg X Z M) (a o : Option X) :
    (splitH' z).symm (a, tauH z upd o (splitH' z q).2) =
      ((), ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2.1, upd q.2.2.2 o)) := by
  obtain ⟨⟨⟩, ⟨dh, dk, dk'⟩, W, m⟩ := q
  simp only [splitH', tauH, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Prod.mk.injEq, and_true,
    true_and]
  funext x
  by_cases hx : x = z
  · subst hx
    simp
  · simp [hx]

omit [Fintype X] [DecidableEq X] [Fintype Z] [Fintype M] [DecidableEq M] in
theorem splitH'_symm_none (q : Unit × HwReg X Z M) (hq : q.2.1.1 z = none) :
    (splitH' z).symm (none, (splitH' z q).2) = q := by
  rw [← hq, ← splitH'_apply_fst, Prod.mk.eta, Equiv.symm_apply_apply]

end readH

/-! ## Flip costs -/

section cost

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

/-- The projector on the states outside `SR`. -/
noncomputable def readPs (SR : HwReg X Z M → Prop) [DecidablePred SR] :
    Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ :=
  diagonal fun q ↦ if SR q.2 then 0 else 1

/-- `readPs SR` is a projector, as `potential_hwReadKraus_le` requires. -/
theorem readPs_proj (SR : HwReg X Z M → Prop) [DecidablePred SR] :
    (readPs SR)ᴴ = readPs SR ∧ readPs SR * readPs SR = readPs SR := by
  refine ⟨?_, ?_⟩
  · rw [readPs, diagonal_conjTranspose]
    congr 1
    funext q
    simp only [Pi.star_apply]
    split_ifs <;> simp
  · rw [readPs, diagonal_mul_diagonal]
    congr 1
    funext q
    split_ifs <;> simp

/-- An event of the hardwired register, on the register with the trivial public register. -/
def liftSet (S : Set (HwReg X Z M)) : Set (Unit × HwReg X Z M) := {q | q.2 ∈ S}

instance (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] : DecidablePred (· ∈ liftSet S) :=
  fun q ↦ inferInstanceAs (Decidable (q.2 ∈ S))

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M] in
theorem mem_liftSet (S : Set (HwReg X Z M)) (q : Unit × HwReg X Z M) : q ∈ liftSet S ↔ q.2 ∈ S :=
  Iff.rfl

omit [Fintype M] in
theorem one_kronecker_hwProjector (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] :
    (1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S = indProj (liftSet S) := by
  rw [hwProjector, one_kronecker_labelProjector, labelProjector, indProj]
  congr 1
  funext q
  simp only [ind, decide_eq_true_eq]
  split_ifs <;> simp_all [liftSet]

/-- **The flip cost from bounds on its terms.** -/
theorem flipCost_le_of (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] {ι : Type} [Fintype ι]
    (K : ι → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ)
    (P σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) {E : ℝ}
    (hε : ((1 - P) * (∑ r, (K r)ᴴ * indProj (liftSet S) * K r - indProj (liftSet S)) *
      (1 - P) * σ).trace.re ≤ E)
    (hε' : ((1 - P) * (∑ r, (K r)ᴴ * indProj (liftSet S) * K r - indProj (liftSet S)) * P *
      (∑ r, (K r)ᴴ * indProj (liftSet S) * K r - indProj (liftSet S)) * (1 - P) * σ).trace.re ≤
        E) :
    flipCost S K P σ ≤ ENNReal.ofReal E + ENNReal.ofReal (P * σ).trace.re +
      2 * (ENNReal.ofReal E * ENNReal.ofReal (P * σ).trace.re) ^ (2⁻¹ : ℝ) := by
  simp only [flipCost, one_kronecker_hwProjector]
  gcongr

/-- **The flip cost of a selecting read of `h`.** Let `SR` select the states whose cell `z` is
neither recorded nor hardwired (and any further condition on the rest). The read updates the
memory to `upd m o`, which for a value `v` is `m` or `sel m v`. Suppose a selected state outside
`S` stays outside when the cell is filled and the memory kept, at most `c s` values `v` put it in
`S` when the memory becomes `sel m v`, and a selected state in `S` stays in `S`. Then with
`P = readPs SR` (the states outside `SR`), `ε, ε' ≤ E = ∑_{SR, ∉ S} c / |X| · σ_ss`. -/
theorem flipCost_readH_le [Nonempty X] (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (upd : M → Option X → M) (sel : M → X → M) (SR : HwReg X Z M → Prop) [DecidablePred SR]
    (c : HwReg X Z M → ℕ) (hSR : ∀ s, SR s → s.1.1 z = none ∧ s.2.1.1 z = none)
    (hupd : ∀ m v, upd m (some v) = m ∨ upd m (some v) = sel m v)
    (hkeep : ∀ s u, SR s → s ∉ S → ((Function.update s.1.1 z u, s.1.2), s.2.1, s.2.2) ∉ S)
    (hcnt : ∀ s, SR s → s ∉ S → (Finset.univ.filter fun v : X ↦ ∃ u : Option X,
      ((Function.update s.1.1 z u, s.1.2), s.2.1, sel s.2.2 v) ∈ S).card ≤ c s)
    (hmono_keep : ∀ s u, SR s → s ∈ S → ((Function.update s.1.1 z u, s.1.2), s.2.1, s.2.2) ∈ S)
    (hmono_sel : ∀ s u v, SR s → s ∈ S →
      ((Function.update s.1.1 z u, s.1.2), s.2.1, sel s.2.2 v) ∈ S)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    flipCost S (hwReadKraus (.readH z upd)) (readPs SR) σ ≤
      ENNReal.ofReal (∑ q, if SR q.2 ∧ q.2 ∉ S then
          (c q.2 : ℝ) / Fintype.card X * (σ q q).re else 0) +
        ENNReal.ofReal (readPs SR * σ).trace.re +
      2 * (ENNReal.ofReal (∑ q, if SR q.2 ∧ q.2 ∉ S then
          (c q.2 : ℝ) / Fintype.card X * (σ q q).re else 0) *
        ENNReal.ofReal (readPs SR * σ).trace.re) ^ (2⁻¹ : ℝ) := by
  set gd : RestH X M z → Prop := fun r ↦ SR ((splitH' z).symm (none, r)).2
  have : DecidablePred gd := fun r ↦ inferInstanceAs (Decidable (SR _))
  have hgd_iff : ∀ q, (gd (splitH' z q).2 ∧ (splitH' z q).1 = none) ↔ SR q.2 := fun q ↦ by
    constructor
    · rintro ⟨h1, h2⟩
      have h0 : q.2.1.1 z = none := h2
      simpa only [gd, splitH'_symm_none z q h0] using h1
    · intro hq
      have h0 := (hSR _ hq).1
      exact ⟨by simpa only [gd, splitH'_symm_none z q h0] using hq, h0⟩
  have hP : readPs SR = readP (splitH' z) gd := by
    unfold readPs readP pp
    congr 1
    funext q
    exact ite_cond_congr (propext (hgd_iff q)).symm
  have hgdact : ∀ r, gd r → actH z r := fun r h ↦ (hSR _ h).2
  have hcell := cellRead_readH (M := M) z upd
  have hF : (∑ r : (HwRead.readH z upd : HwRead X Z M).Result,
      (hwReadKraus (.readH z upd) r)ᴴ * indProj (liftSet S) * hwReadKraus (.readH z upd) r -
        indProj (liftSet S)) =
      flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r) (liftSet S) := by
    rw [flipOp]
  have hN : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
  have hchw : ∀ q : Unit × HwReg X Z M, SR q.2 →
      chw (splitH' z) (tauH z upd) (liftSet S) (splitH' z q).2 ≤
        if q.2 ∈ S then 0 else (c q.2 : ℝ) := by
    intro q hq
    refine (chw_le_card (liftSet S) _).trans ?_
    have hq0 : q0 (splitH' z) (liftSet S) (splitH' z q).2 = if q.2 ∈ S then 1 else 0 := by
      rw [q0, splitH'_symm_none z q (hSR _ hq).1]
      rfl
    have hy : ∀ (y : X) (a : Option X),
        ind (liftSet S) ((splitH' z).symm (a, tauH z upd (some y) (splitH' z q).2)) =
        if ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2.1, upd q.2.2.2 (some y)) ∈ S
          then 1 else 0 := fun y a ↦ by
      rw [splitH'_symm_tau]
      rfl
    simp only [hq0, hy]
    by_cases hS : q.2 ∈ S
    · simp only [hS, ↓reduceIte]
      rw [Nat.cast_nonpos, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro y - ⟨a, ha⟩
      have hmem : ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2.1, upd q.2.2.2 (some y)) ∈ S := by
        rcases hupd q.2.2.2 y with hu | hu <;> rw [hu]
        · exact hmono_keep q.2 a hq hS
        · exact hmono_sel q.2 a y hq hS
      rw [ite_eq_left hmem] at ha
      exact ha rfl
    · simp only [hS, ↓reduceIte]
      rw [Nat.cast_le]
      refine (Finset.card_le_card fun y hy' ↦ ?_).trans (hcnt q.2 hq hS)
      obtain ⟨a, ha⟩ := (Finset.mem_filter.1 hy').2
      have hmem : ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2.1, upd q.2.2.2 (some y)) ∈ S := by
        by_contra hn
        exact ha (ite_eq_right hn)
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, a, ?_⟩
      rcases hupd q.2.2.2 y with hu | hu
      · rw [hu] at hmem
        exact absurd hmem (hkeep q.2 a hq hS)
      · rwa [hu] at hmem
  have hE : (∑ q, if gd (splitH' z q).2 ∧ (splitH' z q).1 = none then
        chw (splitH' z) (tauH z upd) (liftSet S) (splitH' z q).2 / Fintype.card X * (σ q q).re
          else 0) ≤
      ∑ q, if SR q.2 ∧ q.2 ∉ S then (c q.2 : ℝ) / Fintype.card X * (σ q q).re else 0 := by
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [ite_cond_congr (propext (hgd_iff q))]
    have hre : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    by_cases hq : SR q.2
    · have hc := hchw q hq
      by_cases hS : q.2 ∈ S
      · rw [ite_eq_left hS] at hc
        rw [ite_eq_left hq, ite_eq_right fun h ↦ h.2 hS]
        exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hc hN.le) hre
      · rw [ite_eq_right hS] at hc
        rw [ite_eq_left hq, ite_eq_left ⟨hq, hS⟩]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc hN.le) hre
    · rw [ite_eq_right hq, ite_eq_right fun h ↦ hq h.1]
  apply flipCost_le_of
  · rw [hF, hP]
    exact (re_trace_eps_le (liftSet S) gd hcell hgdact hσ).trans hE
  · rw [hF, hP]
    exact (re_trace_eps'_le (liftSet S) gd hcell hgdact hσ).trans hE

end cost

/-! ## Program ports -/

section prog

variable {n : Type} [Fintype n] [DecidableEq n] (S : Set n) [DecidablePred (· ∈ S)]

/-- **The Gram operator of a classical step**: Kraus operators `|f s⟩⟨s|` on the states of index
`i`, with `(idx, f)` injective, give the diagonal of the event at the image. -/
theorem gram_classical {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Matrix n n ℂ)
    (idx : n → ι) (f : n → n) (hK : ∀ i t s, K i t s = if i = idx s ∧ t = f s then 1 else 0)
    (hinj : ∀ s s', idx s = idx s' → f s = f s' → s = s') :
    ∑ i, (K i)ᴴ * indProj S * K i = diagonal fun s ↦ ((ind S (f s) : ℝ) : ℂ) := by
  ext t s
  rw [Matrix.sum_apply, Finset.sum_eq_single (idx s)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (f s)]
    · rw [indProj, mul_diagonal, conjTranspose_apply, hK (idx s) (f s) s,
        ite_eq_left ⟨rfl, rfl⟩, mul_one, hK (idx s) (f s) t, diagonal_apply]
      by_cases hts : t = s
      · subst hts
        simp
      · rw [ite_eq_right fun h ↦ hts (hinj t s h.1.symm h.2.symm), ite_eq_right hts]
        simp
    · intro u _ hu
      rw [hK (idx s) u s, ite_eq_right fun h ↦ hu h.2]
      simp
    · simp
  · intro i _ hi
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun u _ ↦ ?_
    rw [hK i u s, ite_eq_right fun h ↦ hi h.1]
    simp
  · simp

end prog

section progH

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

/-- The cell contents a program reads: the database content and the hardwired value. -/
def progIdx : (c : HwProg X Z) → HwReg X Z M → c.Result
  | .programH z _, s => (s.1.1 z, s.2.1.1 z)
  | .programK x _, s => (s.1.2.1 x, s.2.1.2.1 x)
  | .programK' x _, s => (s.1.2.2 x, s.2.1.2.2 x)

/-- The state after a program: the cell discarded from the databases and hardwired. -/
def progMap : HwProg X Z → HwReg X Z M → HwReg X Z M
  | .programH z v, s => ((Function.update s.1.1 z none, s.1.2),
      (Function.update s.2.1.1 z (some v), s.2.1.2), s.2.2)
  | .programK x v, s => ((s.1.1, Function.update s.1.2.1 x none, s.1.2.2),
      (s.2.1.1, Function.update s.2.1.2.1 x (some v), s.2.1.2.2), s.2.2)
  | .programK' x v, s => ((s.1.1, s.1.2.1, Function.update s.1.2.2 x none),
      (s.2.1.1, s.2.1.2.1, Function.update s.2.1.2.2 x (some v)), s.2.2)

omit [Fintype M] in
theorem programKrausH_apply (z : Z) (v : X) (r : Option X × Option X) (s' s : HwReg X Z M) :
    programKrausH z v r s' s =
      if r = progIdx (.programH z v) s ∧ s' = progMap (.programH z v) s then 1 else 0 := by
  obtain ⟨⟨dh', dk', dk₂'⟩, W', m'⟩ := s'
  obtain ⟨⟨dh, dk, dk₂⟩, W, m⟩ := s
  obtain ⟨o1, o2⟩ := r
  rw [programKrausH, clsKraus_apply, kroneckerMap_apply, Matrix.one_apply]
  simp only [cellDiscard, of_apply, progIdx, progMap, Prod.mk.injEq]
  split_ifs <;> simp_all

omit [Fintype M] in
theorem programKrausK_apply (x : X) (v : Z) (r : Option Z × Option Z) (s' s : HwReg X Z M) :
    programKrausK x v r s' s =
      if r = progIdx (.programK x v) s ∧ s' = progMap (.programK x v) s then 1 else 0 := by
  obtain ⟨⟨dh', dk', dk₂'⟩, W', m'⟩ := s'
  obtain ⟨⟨dh, dk, dk₂⟩, W, m⟩ := s
  obtain ⟨o1, o2⟩ := r
  rw [programKrausK, clsKraus_apply, kroneckerMap_apply, kroneckerMap_apply, Matrix.one_apply,
    Matrix.one_apply]
  simp only [cellDiscard, of_apply, progIdx, progMap, Prod.mk.injEq]
  split_ifs <;> simp_all

omit [Fintype M] in
theorem programKrausK'_apply (x : X) (v : Z) (r : Option Z × Option Z) (s' s : HwReg X Z M) :
    programKrausK' x v r s' s =
      if r = progIdx (.programK' x v) s ∧ s' = progMap (.programK' x v) s then 1 else 0 := by
  obtain ⟨⟨dh', dk', dk₂'⟩, W', m'⟩ := s'
  obtain ⟨⟨dh, dk, dk₂⟩, W, m⟩ := s
  obtain ⟨o1, o2⟩ := r
  rw [programKrausK', clsKraus_apply, kroneckerMap_apply, kroneckerMap_apply, Matrix.one_apply,
    Matrix.one_apply]
  simp only [cellDiscard, of_apply, progIdx, progMap, Prod.mk.injEq]
  split_ifs <;> simp_all

instance instDecidableEqHwProgResult (c : HwProg X Z) : DecidableEq c.Result := by
  cases c <;> exact inferInstanceAs (DecidableEq (Option _ × Option _))

omit [Fintype M] in
theorem hwProgKraus_apply (c : HwProg X Z) (r : c.Result) (q' q : Unit × HwReg X Z M) :
    hwProgKraus c r q' q = if r = progIdx c q.2 ∧ q' = ((), progMap c q.2) then 1 else 0 := by
  obtain ⟨⟨⟩, s'⟩ := q'
  obtain ⟨⟨⟩, s⟩ := q
  cases c with
  | programH z v =>
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ programKrausH z v r) _ _ = _
    rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, programKrausH_apply]
    simp
  | programK x v =>
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ programKrausK x v r) _ _ = _
    rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, programKrausK_apply]
    simp
  | programK' x v =>
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ programKrausK' x v r) _ _ = _
    rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, programKrausK'_apply]
    simp

omit [Fintype X] [Fintype Z] [Fintype M] [DecidableEq M] in
theorem progMap_inj (c : HwProg X Z) {s s' : HwReg X Z M} (hi : progIdx c s = progIdx c s')
    (hf : progMap c s = progMap c s') : s = s' := by
  obtain ⟨⟨dh, dk, dk₂⟩, ⟨w1, w2, w3⟩, m⟩ := s
  obtain ⟨⟨dh', dk', dk₂'⟩, ⟨w1', w2', w3'⟩, m'⟩ := s'
  cases c with
  | programH z v =>
    simp only [progIdx, progMap, Prod.mk.injEq] at hi hf
    obtain ⟨⟨h1, rfl, rfl⟩, ⟨h4, rfl, rfl⟩, rfl⟩ := hf
    obtain rfl := update_eq_update_iff hi.1 h1
    obtain rfl := update_eq_update_iff hi.2 h4
    rfl
  | programK x v =>
    simp only [progIdx, progMap, Prod.mk.injEq] at hi hf
    obtain ⟨⟨rfl, h2, rfl⟩, ⟨rfl, h5, rfl⟩, rfl⟩ := hf
    obtain rfl := update_eq_update_iff hi.1 h2
    obtain rfl := update_eq_update_iff hi.2 h5
    rfl
  | programK' x v =>
    simp only [progIdx, progMap, Prod.mk.injEq] at hi hf
    obtain ⟨⟨rfl, rfl, h3⟩, ⟨rfl, rfl, h7⟩, rfl⟩ := hf
    obtain rfl := update_eq_update_iff hi.1 h3
    obtain rfl := update_eq_update_iff hi.2 h7
    rfl

/-- **The flip cost of a program port**: with `P = 0` it is the weight of the states outside `S`
that the program moves into `S`. -/
theorem flipCost_prog_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    flipCost S (hwProgKraus c) 0 σ ≤
      ENNReal.ofReal (∑ q, if q.2 ∉ S ∧ progMap c q.2 ∈ S then (σ q q).re else 0) := by
  have hg := gram_classical (liftSet S) (hwProgKraus c) (fun q ↦ progIdx c q.2)
    (fun q ↦ ((), progMap c q.2)) (hwProgKraus_apply c)
    (fun q q' hi hf ↦ Prod.ext rfl (progMap_inj c hi (congrArg Prod.snd hf)))
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hE0 : 0 ≤ ∑ q, if q.2 ∉ S ∧ progMap c q.2 ∈ S then (σ q q).re else 0 :=
    Finset.sum_nonneg fun q _ ↦ by split_ifs <;> simp [hre q]
  refine (flipCost_le_of S (hwProgKraus c) 0 σ (E := ∑ q, if q.2 ∉ S ∧ progMap c q.2 ∈ S then
    (σ q q).re else 0) ?_ ?_).trans ?_
  · rw [hg, sub_zero, Matrix.one_mul, Matrix.mul_one, indProj, Matrix.sub_mul, Matrix.trace_sub,
      Complex.sub_re, Matrix.trace, Matrix.trace, Complex.re_sum, Complex.re_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [diag_apply, diag_apply, diagonal_mul, diagonal_mul, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul, ← sub_mul]
    simp only [ind, mem_liftSet]
    by_cases h1 : q.2 ∈ S
    · have h0 : (if q.2 ∉ S ∧ progMap c q.2 ∈ S then (σ q q).re else 0) = 0 :=
        ite_eq_right fun h ↦ h.1 h1
      rw [h0, ite_eq_left h1]
      split_ifs <;> nlinarith [hre q]
    · rw [ite_eq_right h1]
      by_cases h2 : progMap c q.2 ∈ S
      · rw [ite_eq_left h2, ite_eq_left ⟨h1, h2⟩]
        simp
      · rw [ite_eq_right h2, ite_eq_right fun h ↦ h2 h.2]
        simp
  · simp [hE0]
  · simp [ENNReal.zero_rpow_of_pos]

end progH


/-! ## Sums of flip costs -/

section sums

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

/-- **Program ports averaged over the programmed value**: the states outside `S`, weighted by the
number of values that move them into `S`. -/
theorem sum_flipCost_prog_le {V : Type} [Fintype V] (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (c : V → HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    ∑ v, flipCost S (hwProgKraus (c v)) 0 σ ≤ ENNReal.ofReal (∑ q, if q.2 ∉ S then
      ((Finset.univ.filter fun v ↦ progMap (c v) q.2 ∈ S).card : ℝ) * (σ q q).re else 0) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  refine (Finset.sum_le_sum fun v _ ↦ flipCost_prog_le S (c v) hσ).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun v _ ↦ Finset.sum_nonneg fun q _ ↦ by
    split_ifs <;> simp [hre q]]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases hq : q.2 ∈ S
  · rw [ite_eq_right (not_not.2 hq)]
    exact Finset.sum_eq_zero fun v _ ↦ ite_eq_right fun h ↦ h.1 hq
  · rw [ite_eq_left hq]
    simp only [hq, not_false_eq_true, true_and]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

/-- **Program ports averaged over the programmed value, uniformly**: if at most `C` values move a
state of the support outside `S` into `S`, the sum is at most `C tr σ`. -/
theorem sum_flipCost_prog_le_card {V : Type} [Fintype V] (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (c : V → HwProg X Z) (C : ℕ)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ q, q.2 ∉ S → σ q q ≠ 0 →
      (Finset.univ.filter fun v ↦ progMap (c v) q.2 ∈ S).card ≤ C) :
    ∑ v, flipCost S (hwProgKraus (c v)) 0 σ ≤ C * ENNReal.ofReal σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  refine (sum_flipCost_prog_le S c hσ).trans ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), Matrix.trace,
    Complex.re_sum, Finset.mul_sum]
  refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ ?_)
  by_cases hq : q.2 ∈ S
  · rw [ite_eq_right (not_not.2 hq)]
    exact mul_nonneg (Nat.cast_nonneg _) (hre q)
  · rw [ite_eq_left hq]
    by_cases hσq : σ q q = 0
    · simp [hσq]
    · exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (hC q hq hσq)) (hre q)

omit [DecidableEq M] in
/-- **The selecting-read sum, uniformly**: if `c ≤ C` on the support, the `E` of
`flipCost_readH_le` is at most `C / |X| · tr σ`. -/
theorem readE_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (SR : HwReg X Z M → Prop)
    [DecidablePred SR] (c : HwReg X Z M → ℕ) (C : ℕ)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ q, SR q.2 → q.2 ∉ S → σ q q ≠ 0 → c q.2 ≤ C) :
    (∑ q, if SR q.2 ∧ q.2 ∉ S then (c q.2 : ℝ) / Fintype.card X * (σ q q).re else 0) ≤
      C / Fintype.card X * σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hN : (0 : ℝ) ≤ Fintype.card X := Nat.cast_nonneg _
  rw [Matrix.trace, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  split_ifs with hq
  · by_cases hσq : σ q q = 0
    · simp [hσq]
    · exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (Nat.cast_le.2 (hC q hq.1 hq.2 hσq)) hN) (hre q)
  · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hN) (hre q)

omit [DecidableEq X] [Fintype M] [DecidableEq M] in
/-- Filling an empty cell of `h` keeps a target event, if the targets only grow. -/
theorem mem_hwTargetBad_fill [AddCommGroup X] [AddCommGroup Z] {Y : Type}
    {π : Equiv.Perm (X × Z)} {out : X → Y} {tgt : Hw X Z → M → List X → Option Y} {N : ℕ}
    {s : HwReg X Z M} (hs : s ∈ HwTargetBad π out tgt N) {z : Z} (hz : s.1.1 z = none)
    (u : Option X) (m' : M) (htgt : ∀ t y, tgt s.2.1 s.2.2 t = some y → tgt s.2.1 m' t = some y) :
    ((Function.update s.1.1 z u, s.1.2), s.2.1, m') ∈ HwTargetBad π out tgt N :=
  ⟨hs.1, targetBad_mono htgt (TargetBad.mono (extendsAll_union s.2.1 (D := s.1)
    (D' := (Function.update s.1.1 z u, s.1.2)) (fun _ _ h ↦ update_some_of_none hz h)
    (fun _ _ h ↦ h) fun _ _ h ↦ h) hs.2)⟩

end sums

end Quantum.Sponge

namespace Quantum.Xmss

open Quantum Quantum.Sponge HashSig LeanXmss
open scoped ENNReal

variable {L : HonestTable} {N : ℕ}

/-- **Recording a selection of an unselected key keeps every target.** -/
theorem xmssTgt_select_mono {Ex : Set Slot} {m : Selections} {l : Layer} {e : KeyIndex} {x : X}
    {y' : Digest} (hm : m l e = none) {t : List X} {y : Digest}
    (h : xmssTgt L Ex m.toMemory t = some y) :
    xmssTgt L Ex (m.select l e x y').toMemory t = some y := by
  unfold xmssTgt at h ⊢
  revert h
  cases hs : slotOf L.param t with
  | none => exact fun h ↦ absurd h (by simp)
  | some s =>
    simp only [Option.bind_some]
    intro h
    cases s with
    | msg l' e' =>
      by_cases hk : l' = l ∧ e' = e
      · obtain ⟨rfl, rfl⟩ := hk
        change (m.toMemory l' e').bind _ = some y at h
        rw [Selections.toMemory_eq_none hm] at h
        cases h
      · change ((m.select l e x y').toMemory l' e').bind _ = some y
        rw [Selections.toMemory_select_of_ne m x y' hk]
        exact h
    | chain => exact h
    | leaf => exact h
    | node => exact h
    | prf => exact h
    | rnd => exact h
    | param => exact h
    | seed => exact h

theorem two_pow_div_card_X : (2 : ℝ) ^ 960 / Fintype.card X = (2 ^ 128)⁻¹ := by
  rw [card_X, Nat.cast_pow, Nat.cast_ofNat, show (1088 : ℕ) = 960 + 128 from rfl, pow_add,
    div_mul_cancel_left₀ (pow_ne_zero _ two_ne_zero)]

open scoped Classical in
/-- **The flip cost of a selecting read** of the final `h` cell `z` of the message-digest trial of
key `(l, e)` with block `x` and rate `xi`. The read updates the memory with `upd`, which for a value
`v` keeps it or records the selection `(x, trunc128 (xi + v))`. With `P` the projector on the
states that are not selection reads (`SelectRead`: the cell recorded or hardwired, the key already
selected, or the trial's tail not the head-tail of the cell), the flip cost is
`E + p + 2 √(E p)` with `E = ∑_{SelectRead, ∉ Bad} msgCount · 2^960 / |X| · σ_ss` and
`p = tr (P σ)`. -/
theorem flipCost_selectRead_le (z : Z) (l : Layer) (e : KeyIndex) (x xi : X)
    (upd : Selections → Option X → Selections)
    (hupd : ∀ m v, upd m (some v) = m ∨ upd m (some v) = m.select l e x (trunc128 (xi + v)))
    {σ : Matrix (Unit × HwReg X Z Selections) (Unit × HwReg X Z Selections) ℂ}
    (hσ : σ.PosSemidef) :
    flipCost (Bad L N) (hwReadKraus (.readH z upd))
        (readPs fun s ↦ SelectRead L s.1 s.2.1 s.2.2 z l e x xi) σ ≤
      ENNReal.ofReal (∑ q, if SelectRead L q.2.1 q.2.2.1 q.2.2.2 z l e x xi ∧ q.2 ∉ Bad L N then
          ((msgCount L (union q.2.2.1 q.2.1) l e * 2 ^ 960 : ℕ) : ℝ) / Fintype.card X *
            (σ q q).re else 0) +
        ENNReal.ofReal ((readPs fun s ↦ SelectRead L s.1 s.2.1 s.2.2 z l e x xi) * σ).trace.re +
      2 * (ENNReal.ofReal (∑ q, if SelectRead L q.2.1 q.2.2.1 q.2.2.2 z l e x xi ∧
          q.2 ∉ Bad L N then ((msgCount L (union q.2.2.1 q.2.1) l e * 2 ^ 960 : ℕ) : ℝ) /
            Fintype.card X * (σ q q).re else 0) *
        ENNReal.ofReal ((readPs fun s ↦ SelectRead L s.1 s.2.1 s.2.2 z l e x xi) * σ).trace.re) ^
          (2⁻¹ : ℝ) := by
  refine flipCost_readH_le (Bad L N) z upd (fun m v ↦ m.select l e x (trunc128 (xi + v)))
    (fun s ↦ SelectRead L s.1 s.2.1 s.2.2 z l e x xi)
    (fun s ↦ msgCount L (union s.2.1 s.1) l e * 2 ^ 960) ?_ hupd ?_ ?_ ?_ ?_ hσ
  · exact fun _ hs ↦ ⟨hs.hd, hs.hw⟩
  · exact fun _ u hs hS ↦ not_mem_bad_read_keep hS hs u
  · -- The filter's decidability instances differ syntactically from `card_flip_read_le`'s.
    intro s hs hS
    convert card_flip_read_le hS hs using 3
  · exact fun s u hs hS ↦ mem_hwTargetBad_fill hS hs.hd u s.2.2 fun _ _ ht ↦ ht
  · exact fun s u v hs hS ↦
      mem_hwTargetBad_fill hS hs.hd u _ fun _ _ ht ↦ xmssTgt_select_mono hs.hm ht

open scoped Classical in
/-- **The selecting-read term, crudely**: on states with at most `N` hardwired and `t` database
entries per function, `msgCount ≤ |union.h| ≤ N + t`, so `E ≤ (N + t) 2^-128 tr σ`. -/
theorem selectReadE_le (z : Z) (l : Layer) (e : KeyIndex) (x xi : X) (t : ℕ)
    {σ : Matrix (Unit × HwReg X Z Selections) (Unit × HwReg X Z Selections) ℂ}
    (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → dbGrade q.2.2.1 ≤ N ∧ dbGrade q.2.1 ≤ t) :
    (∑ q, if SelectRead L q.2.1 q.2.2.1 q.2.2.2 z l e x xi ∧ q.2 ∉ Bad L N then
        ((msgCount L (union q.2.2.1 q.2.1) l e * 2 ^ 960 : ℕ) : ℝ) / Fintype.card X *
          (σ q q).re else 0) ≤ (N + t) * (2 ^ 128)⁻¹ * σ.trace.re := by
  refine (readE_le (Bad L N) (fun s ↦ SelectRead L s.1 s.2.1 s.2.2 z l e x xi)
    (fun s ↦ msgCount L (union s.2.1 s.1) l e * 2 ^ 960) ((N + t) * 2 ^ 960) hσ
    fun q _ _ hσq ↦ Nat.mul_le_mul_right _ ?_).trans_eq ?_
  · obtain ⟨hN, ht⟩ := hsupp q hσq
    exact (msgCount_le_size L _ l e).trans ((size_unionH_le _ _).trans (by omega))
  · rw [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc,
      two_pow_div_card_X]

open scoped Classical in
/-- **Programming `h` cells, averaged over the value**: `2^-128 tr σ`, on states whose cell is
not hardwired. -/
theorem flipCost_programH_avg_le (z : Z)
    {σ : Matrix (Unit × HwReg X Z Selections) (Unit × HwReg X Z Selections) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → q.2.2.1.1 z = none) :
    (Fintype.card X : ℝ≥0∞)⁻¹ * ∑ v : X, flipCost (Bad L N) (hwProgKraus (.programH z v)) 0 σ ≤
      (2 ^ 128)⁻¹ * ENNReal.ofReal σ.trace.re := by
  have h := sum_flipCost_prog_le_card (Bad L N) (fun v : X ↦ HwProg.programH z v) (2 ^ 960) hσ
    fun q hq hσq ↦ card_flip_programH_bad_le (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hq
      (hsupp q hσq)
  calc (Fintype.card X : ℝ≥0∞)⁻¹ * ∑ v : X, flipCost (Bad L N) (hwProgKraus (.programH z v)) 0 σ
      ≤ (Fintype.card X : ℝ≥0∞)⁻¹ * (((2 ^ 960 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) :=
        mul_le_mul_right h _
    _ = ((2 ^ 960 : ℕ) : ℝ≥0∞) / Fintype.card X * ENNReal.ofReal σ.trace.re := by
        rw [ENNReal.div_eq_inv_mul, mul_assoc]
    _ = _ := by rw [fiber_div_card_X]

open scoped Classical in
/-- **Programming intermediate `h` cells of multi-block honest paths flips nothing**: on states
whose cell is not hardwired and whose head-tail is a non-message tail of a length other than its
slot's honest tail. -/
theorem flipCost_programH_short (z : Z)
    {σ : Matrix (Unit × HwReg X Z Selections) (Unit × HwReg X Z Selections) ℂ}
    (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → q.2.2.1.1 z = none ∧ ∃ s t₀ xi₀, slotOf L.param t₀ = some s ∧
      (∀ l e, s ≠ .msg l e) ∧ (L.honestTail s).map List.length ≠ some t₀.length ∧
        IsHeadTail L.perm (union q.2.2.1 q.2.1) t₀ z xi₀) :
    ∑ v : X, flipCost (Bad L N) (hwProgKraus (.programH z v)) 0 σ = 0 := by
  refine le_antisymm ((sum_flipCost_prog_le_card (Bad L N) (fun v : X ↦ HwProg.programH z v) 0 hσ
    fun q hq hσq ↦ ?_).trans (by simp)) (by simp)
  obtain ⟨hW, s, t₀, xi₀, h1, h2, h3, h4⟩ := hsupp q hσq
  exact (card_flip_programH_bad_le_short (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hq hW h1 h2
    h3 h4).le

open scoped Classical in
/-- **Programming `k` cells, averaged over the value**: the capacity-scale count of
`preimageRateBound` over `|Z|`, on states whose cell is not hardwired, with at most `T - N`
database entries per function. -/
theorem flipCost_programK_avg_le {G T : ℕ} (hπ : PermGood L.perm G) (x : X)
    {σ : Matrix (Unit × HwReg X Z Selections) (Unit × HwReg X Z Selections) ℂ}
    (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → q.2.2.1.2.1 x = none ∧ N + dbGrade q.2.1 ≤ T) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ v : Z, flipCost (Bad L N) (hwProgKraus (.programK x v)) 0 σ ≤
      (((T + 1) * ((T + 1) * T + 2 * T) * G : ℕ) : ℝ≥0∞) / Fintype.card Z *
        ENNReal.ofReal σ.trace.re := by
  have h := sum_flipCost_prog_le_card (Bad L N) (fun v : Z ↦ HwProg.programK x v)
    ((T + 1) * ((T + 1) * T + 2 * T) * G) hσ fun q hq hσq ↦
      card_flip_programK_bad_le (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hπ hq
        (hsupp q hσq).2 (hsupp q hσq).1
  rw [ENNReal.div_eq_inv_mul, mul_assoc]
  exact mul_le_mul_right h _

open scoped Classical in
/-- **Programming `k'` cells, averaged over the value**: the capacity-scale count of
`preimageRateBound` over `|Z|`, on states whose cell is not hardwired, with at most `T - N`
database entries per function. -/
theorem flipCost_programK'_avg_le {G T : ℕ} (hπ : PermGood L.perm G) (x : X)
    {σ : Matrix (Unit × HwReg X Z Selections) (Unit × HwReg X Z Selections) ℂ}
    (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → q.2.2.1.2.2 x = none ∧ N + dbGrade q.2.1 ≤ T) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ v : Z, flipCost (Bad L N) (hwProgKraus (.programK' x v)) 0 σ ≤
      (((T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T : ℕ) : ℝ≥0∞) /
        Fintype.card Z * ENNReal.ofReal σ.trace.re := by
  have h := sum_flipCost_prog_le_card (Bad L N) (fun v : Z ↦ HwProg.programK' x v)
    ((T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T) hσ fun q hq hσq ↦
      card_flip_programK'_bad_le (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hπ hq
        (hsupp q hσq).2 (hsupp q hσq).1
  rw [ENNReal.div_eq_inv_mul, mul_assoc]
  exact mul_le_mul_right h _

end Quantum.Xmss

end
