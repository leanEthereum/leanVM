module

public import Quantum.Xmss.Assembly.CostLift
public import Quantum.Xmss.Assembly.EndReads

@[expose] public section

/-!
# The refined read cost: recorded cells cost `2/|Y|`, hardwired cells their classical move

`potential_hwReadKraus_le` charges a read port `ε + p + 2 √(ε' p)` with `p` the whole weight of the
states whose read cell is recorded or hardwired. This file removes `p` for states with no
decompressed `⊥` at the read cell (`CellNoBot`: on every rest whose cell is not hardwired, the
recorded amplitudes of every column add up to zero). Without that hypothesis the refinement is
false: the uniform superposition of the recorded values outside the event, half of `Y`, has
event weight `0` and recorded weight `1`, but its decompressed `⊥` amplitude `√½` makes the read
output `⊥` with probability `½` and leave the uniform superposition of all values, half in the
event.

* **The corrected flip operator** (`flipOp_eq_fcor`, `trace_corr1_mul`, `trace_corr2_mul`): the
  flip operator of a cell read is `diag fd + X + Xᴴ` plus terms constant along the recorded rows
  or columns of a rest, invisible to `CellNoBot` states. `X` maps the empty cell of a rest to its
  recorded cells with amplitudes `(g y - κ) / √|Y|` (`g y` the weight of outcome `y`, `κ` a
  reference weight). Hence (`re_trace_flipOp_le`) the flip is at most `A + 2 √(E p)` with
  `A = ∑ fd σ_ss`, `E = ∑ ew σ_ss` and `p` the weight of the recorded cells whose value is in a set
  `D` off which `g = κ`.
* **The diagonal costs** (`fd_none_le`, `fd_some_le`, `fd_off`): an empty cell costs its mean flip
  `≤ Δ / |Y|` (as `ε`), a recorded cell `≤ 2/|Y|` plus its classical move (the event at the
  recorded value with the memory updated by it), a hardwired cell its classical move.
* **The reference weight and the flip values** (`kap`, `Flip`, `gw_eq_kap`, `ew_kap_le`): with
  `κ = kap`, `g = κ` off the values whose recording flips the event or whose memory update changes
  it (`Flip`), so `E ≤` the number of flip values over `|Y|`, and `p` is the recorded mass on flip
  values. For an event up-closed in the read cell, `p ≤ w + m` (`costP_le`) with `w` the event
  weight and `m` the recorded mass whose memory update changes the event (`Moves`).
* **The ports** (`potential_cellRead_le`, `potential_hwReadKraus_le_refined`, `readCost`,
  `potential_hwReadKraus_le_refinedT`): the drop-in alternative to `potential_hwReadKraus_le`, with
  the hardwired columns of the reads of `h`, `k`, `k'` classical (`ClsOff`, `clsOff_readH`,
  `clsOff_readK`, `clsOff_readK'`).
* **`CellNoBot` along the runs** (`readNoBot_of_noBot`): it follows from EndReads' invariant
  (`noBot_runtimeR`: the decompressed databases have no empty cell).
* **The square-root form** (`potential_cellRead_le_sqrt`, `potential_hwReadKraus_le_sqrt`): for an
  event up-closed in the read cell (`UpCell`), the weight after a read is at most
  `(√w + √E)² + A + 2 √(E m)`. For reads that keep the memory (`KeepUpd`,
  `potential_readKeep_le_sqrt`) `m = 0`, `E ≤ keepE` (flip values over `|Y|` on the empty cells)
  and `A ≤ keepE + recW` (`recW = 2/|Y|` times the recorded mass): a read costs like a sponge
  call. For reads of `h` that update the memory, `read_readH_le` bounds `E`, `A`, `m` in
  FlipCost's terms.
-/

open Matrix
open scoped Kronecker ENNReal ComplexOrder

namespace Quantum.Sponge

open Quantum

/-! ## Sums of the one-cell compression -/

section crsum

variable {Y : Type} [Fintype Y] [DecidableEq Y]

omit [DecidableEq Y] in
theorem inv_sqrt_mul_inv_sqrt_card :
    (Real.sqrt (Fintype.card Y))⁻¹ * (Real.sqrt (Fintype.card Y))⁻¹ =
      ((Fintype.card Y : ℝ))⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]

theorem sum_cr_none_none (g : Option Y → ℝ) :
    ∑ o, cr none o * g o * cr o none = (∑ y, g (some y)) / Fintype.card Y := by
  rw [Fintype.sum_option, Finset.sum_div]
  simp only [cr, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [div_eq_mul_inv, ← inv_sqrt_mul_inv_sqrt_card]
  ring

theorem sum_cr_some_none (g : Option Y → ℝ) (y' : Y) :
    ∑ o, cr (some y') o * g o * cr o none =
      (g (some y') - (∑ y, g (some y)) / Fintype.card Y) / Real.sqrt (Fintype.card Y) := by
  rw [Fintype.sum_option]
  simp only [cr, mul_zero, zero_add]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_mul, ← Finset.mul_sum, div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem sum_cr_none_some (g : Option Y → ℝ) (y : Y) :
    ∑ o, cr none o * g o * cr o (some y) =
      (g (some y) - (∑ y, g (some y)) / Fintype.card Y) / Real.sqrt (Fintype.card Y) := by
  rw [Fintype.sum_option]
  simp only [cr, zero_mul, zero_add]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_mul, ← Finset.mul_sum, div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem sum_cr_some_some (g : Option Y → ℝ) (y' y : Y) :
    ∑ o, cr (some y') o * g o * cr o (some y) =
      g none / Fintype.card Y + (if y' = y then g (some y) else 0) -
        g (some y') / Fintype.card Y - g (some y) / Fintype.card Y +
          (∑ x, g (some x)) / (Fintype.card Y : ℝ) ^ 2 := by
  rw [Fintype.sum_option]
  simp only [cr]
  set N := (Fintype.card Y : ℝ)
  have hterm : ∀ x : Y, ((if y' = x then (1 : ℝ) else 0) - N⁻¹) * g (some x) *
      ((if x = y then (1 : ℝ) else 0) - N⁻¹) =
      (if y' = x then (if x = y then g (some x) else 0) else 0) -
        (if y' = x then g (some x) else 0) * N⁻¹ - N⁻¹ * (if x = y then g (some x) else 0) +
          N⁻¹ * N⁻¹ * g (some x) := fun x ↦ by
    split_ifs <;> ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hs : (Real.sqrt N)⁻¹ * g none * (Real.sqrt N)⁻¹ = g none / N := by
    rw [div_eq_mul_inv, ← inv_sqrt_mul_inv_sqrt_card]
    ring
  rw [hs]
  by_cases h : y' = y
  · subst h
    simp only [↓reduceIte]
    ring
  · simp only [h, ↓reduceIte]
    ring

end crsum

/-! ## The corrected flip operator of a cell read -/

section core

variable {n Y R M0 : Type} [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y]
  [Fintype R] [DecidableEq R] [Fintype M0] [DecidableEq M0]

/-- **The hardwired columns of a read are classical**: off the active rests, the Kraus operator of
outcome `i` moves the basis state `s` to `φ s` if `i = idx s`, injectively. -/
structure ClsOff (e : n ≃ Option Y × R) (act : R → Prop) (K : Option Y × M0 → Matrix n n ℂ)
    (idx : n → Option Y × M0) (φ : n → n) : Prop where
  entry : ∀ i t s, ¬ act (e s).2 → K i t s = if i = idx s ∧ t = φ s then 1 else 0
  inj : ∀ s s', ¬ act (e s).2 → ¬ act (e s').2 → idx s = idx s' → φ s = φ s' → s = s'

/-- **No decompressed empty cell at the read cell**, in the compressed basis: on every active rest
the recorded amplitudes of every column add up to zero (the compressed state is orthogonal to the
uniform superposition of the recorded values, the image of the decompressed `⊥`). -/
def CellNoBot (e : n ≃ Option Y × R) (act : R → Prop) (σ : Matrix n n ℂ) : Prop :=
  ∀ r, act r → ∀ t, ∑ y, σ (e.symm (some y, r)) t = 0

variable {e : n ≃ Option Y × R} {act : R → Prop} [DecidablePred act] {μ : R → M0}
  {τ : Option Y → R → R} {K : Option Y × M0 → Matrix n n ℂ} {idx : n → Option Y × M0}
  {φ : n → n} (S : Set n) [DecidablePred (· ∈ S)]

omit [Fintype R] [DecidablePred act] in
/-- The Gram operator of a read on a hardwired column: the event at the classical move. -/
theorem gram_off (h : CellRead e act μ τ K) (hc : ClsOff e act K idx φ) {s : n}
    (hs : ¬ act (e s).2) (t : n) :
    (∑ i, (K i)ᴴ * indProj S * K i) t s = if t = s then ((ind S (φ s) : ℝ) : ℂ) else 0 := by
  have hterm : ∀ i, ((K i)ᴴ * indProj S * K i) t s =
      ∑ u, star (K i u t) * ((ind S u : ℝ) : ℂ) * K i u s := fun i ↦ by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [indProj, mul_diagonal, conjTranspose_apply]
  simp only [Matrix.sum_apply, hterm]
  rw [Finset.sum_eq_single (idx s)]
  · rw [Finset.sum_eq_single (φ s)]
    · have hφ : ¬ act (e (φ s)).2 := h.off (idx s) (φ s) s hs (by rw [hc.entry _ _ _ hs]; simp)
      rw [hc.entry _ _ _ hs, ite_eq_left ⟨rfl, rfl⟩, mul_one]
      by_cases ht : act (e t).2
      · have h0 : K (idx s) (φ s) t = 0 := by
          by_contra h0
          exact hφ ((cellRead_ne_zero h ht h0).2 ▸ h.act_τ _ _ ht)
        rw [h0, star_zero, zero_mul, ite_eq_right]
        rintro rfl
        exact hs ht
      · rw [hc.entry _ _ _ ht]
        by_cases hts : t = s
        · subst hts
          simp
        · rw [ite_eq_right, ite_eq_right hts]
          · simp
          · rintro ⟨h1, h2⟩
            exact hts (hc.inj t s ht hs h1.symm h2.symm)
    · intro u _ hu
      rw [hc.entry _ _ _ hs, ite_eq_right fun h' ↦ hu h'.2, mul_zero]
    · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun u _ ↦ ?_
    rw [hc.entry _ _ _ hs, ite_eq_right fun h' ↦ hi h'.1, mul_zero]
  · simp

variable (e τ) in
/-- The mean weight of the recorded outcomes. -/
noncomputable def gbar (r : R) : ℝ := (∑ y, gw e τ S (some y) r) / Fintype.card Y

variable (e τ) in
/-- The diagonal of the corrected flip operator on an active rest, before the event. -/
noncomputable def gdiag : Option Y → R → ℝ
  | none, r => gbar e τ S r
  | some y, r => gw e τ S (some y) r

variable (e act τ) in
/-- **The diagonal cost of a basis state**: on an active rest `gdiag - 1_S` (the mean flip of an
empty cell, the recorded outcome's weight on a recorded one), on a hardwired one the classical
move `1_S (φ s) - 1_S s`. -/
noncomputable def fd (φ : n → n) (s : n) : ℝ :=
  if act (e s).2 then gdiag e τ S (e s).1 (e s).2 - ind S s else ind S (φ s) - ind S s

variable (e τ) in
/-- The amplitude between an empty cell and a recorded one in the corrected flip operator,
relative to the reference weight `κ`. -/
noncomputable def xv (κ : R → ℝ) : Option Y → R → ℝ
  | none, _ => 0
  | some y, r => (gw e τ S (some y) r - κ r) / Real.sqrt (Fintype.card Y)

variable (e act τ) in
/-- The off-diagonal part of the corrected flip operator: from the empty cell of an active rest to
its recorded cells. -/
noncomputable def xm (κ : R → ℝ) : Matrix n n ℂ :=
  Matrix.of fun t s ↦ if act (e s).2 ∧ (e s).1 = none ∧ (e t).2 = (e s).2 then
    ((xv e τ S κ (e t).1 (e s).2 : ℝ) : ℂ) else 0

variable (e τ) in
/-- The correction on the recorded rows, by the column's cell. -/
noncomputable def ca (κ : R → ℝ) : Option Y → R → ℝ
  | none, r => (κ r - gbar e τ S r) / Real.sqrt (Fintype.card Y)
  | some y, r => gw e τ S none r / Fintype.card Y +
      (∑ x, gw e τ S (some x) r) / (Fintype.card Y : ℝ) ^ 2 - gw e τ S (some y) r / Fintype.card Y

variable (e τ) in
/-- The correction on the recorded columns, by the row's cell. -/
noncomputable def cb (κ : R → ℝ) : Option Y → R → ℝ
  | none, r => (κ r - gbar e τ S r) / Real.sqrt (Fintype.card Y)
  | some y, r => -(gw e τ S (some y) r / Fintype.card Y)

variable (e act τ) in
/-- The correction constant along the recorded rows of an active rest. -/
noncomputable def corr1 (κ : R → ℝ) : Matrix n n ℂ :=
  Matrix.of fun t s ↦ if act (e t).2 ∧ (e t).1 ≠ none ∧ (e s).2 = (e t).2 then
    ((ca e τ S κ (e s).1 (e s).2 : ℝ) : ℂ) else 0

variable (e act τ) in
/-- The correction constant along the recorded columns of an active rest. -/
noncomputable def corr2 (κ : R → ℝ) : Matrix n n ℂ :=
  Matrix.of fun t s ↦ if act (e s).2 ∧ (e s).1 ≠ none ∧ (e t).2 = (e s).2 then
    ((cb e τ S κ (e t).1 (e t).2 : ℝ) : ℂ) else 0

/-- **The flip operator of a cell read, split**: the corrected flip operator (diagonal `fd` plus
the empty-to-recorded amplitudes `xm`) plus corrections constant along recorded rows or columns. -/
theorem flipOp_eq_fcor (h : CellRead e act μ τ K) (hc : ClsOff e act K idx φ) (κ : R → ℝ) :
    flipOp K S = diagonal (fun s ↦ ((fd e act τ S φ s : ℝ) : ℂ)) + xm e act τ S κ +
      (xm e act τ S κ)ᴴ + corr1 e act τ S κ + corr2 e act τ S κ := by
  ext t s
  simp only [Matrix.add_apply, diagonal_apply, conjTranspose_apply, xm, corr1, corr2, of_apply]
  by_cases hs : act (e s).2
  swap
  · have hF : flipOp K S t s = if t = s then ((ind S (φ s) - ind S s : ℝ) : ℂ) else 0 := by
      rw [flipOp, Matrix.sub_apply, gram_off S h hc hs, indProj, diagonal_apply]
      split_ifs with hts
      · subst hts
        push_cast
        ring
      · simp
    rw [hF]
    have h1 : ¬ (act (e t).2 ∧ (e t).1 = none ∧ (e s).2 = (e t).2) := fun h' ↦ hs (h'.2.2 ▸ h'.1)
    have h2 : ¬ (act (e t).2 ∧ (e t).1 ≠ none ∧ (e s).2 = (e t).2) := fun h' ↦ hs (h'.2.2 ▸ h'.1)
    have h3 : ¬ (act (e s).2 ∧ (e s).1 = none ∧ (e t).2 = (e s).2) := fun h' ↦ hs h'.1
    have h4 : ¬ (act (e s).2 ∧ (e s).1 ≠ none ∧ (e t).2 = (e s).2) := fun h' ↦ hs h'.1
    rw [ite_eq_right h3, ite_eq_right h1, ite_eq_right h2, ite_eq_right h4, star_zero]
    simp only [add_zero]
    by_cases hts : t = s
    · subst hts
      rw [ite_eq_left rfl, ite_eq_left rfl, fd, ite_eq_right hs]
    · rw [ite_eq_right hts, ite_eq_right hts]
  by_cases hr : (e t).2 = (e s).2
  swap
  · have hts : t ≠ s := fun h' ↦ hr (h' ▸ rfl)
    have hr' : (e s).2 ≠ (e t).2 := Ne.symm hr
    rw [flipOp_eq_zero S h hs hr]
    simp only [hts, ↓reduceIte, hr, and_false, hr', star_zero, add_zero]
  have ht : act (e t).2 := hr ▸ hs
  rw [flipOp_apply S h hs, ite_eq_left hr]
  rcases ht1 : (e t).1 with _ | y' <;> rcases hs1 : (e s).1 with _ | y
  · have hts : t = s := eq_of_rest hr (by rw [ht1, hs1])
    subst hts
    simp only [↓reduceIte, ht1, hs, and_self, ne_eq, not_true_eq_false, and_false, false_and,
      add_zero, xv, fd, gdiag, Complex.ofReal_zero, star_zero]
    rw [sum_cr_none_none]
    simp only [gbar]
    push_cast
    ring
  · have hts : t ≠ s := fun h' ↦ by rw [h', hs1] at ht1; cases ht1
    rw [sum_cr_none_some]
    simp only [hts, ↓reduceIte, hs, hr, ne_eq, reduceCtorEq, not_true_eq_false,
      not_false_eq_true, and_true, and_false, zero_add, add_zero, xv, cb, gbar,
      Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  · have hts : t ≠ s := fun h' ↦ by rw [h', hs1] at ht1; cases ht1
    rw [sum_cr_some_none]
    simp only [hts, ↓reduceIte, hs, hr, ne_eq, reduceCtorEq, not_true_eq_false,
      not_false_eq_true, and_true, and_false, zero_add, add_zero, xv, ca, gbar,
      Complex.star_def, map_zero]
    push_cast
    ring
  · rw [sum_cr_some_some]
    by_cases hyy : y' = y
    · subst hyy
      have hts : t = s := eq_of_rest hr (by rw [ht1, hs1])
      subst hts
      simp only [↓reduceIte, hs, hs1, ne_eq, reduceCtorEq, not_false_eq_true, and_true,
        and_false, add_zero, fd, gdiag, ca, cb, star_zero]
      push_cast
      ring
    · have hts : t ≠ s := fun h' ↦ by rw [h', hs1] at ht1; exact hyy (Option.some.inj ht1).symm
      simp only [hts, hyy, ↓reduceIte, hs, hr, ne_eq, reduceCtorEq,
        not_false_eq_true, and_true, and_false, add_zero,
        ca, cb, star_zero]
      push_cast
      ring

omit [DecidableEq n] [DecidableEq Y] [DecidableEq R] [DecidablePred act] in
/-- Sums over the basis states vanishing off a rest, through the split. -/
theorem sum_rest_eq {f : n → ℂ} (r : R) (hf : ∀ t, (e t).2 ≠ r → f t = 0) :
    ∑ t, f t = ∑ a, f (e.symm (a, r)) := by
  rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single r]
  · intro r' _ hr'
    exact Finset.sum_eq_zero fun a _ ↦ hf _ (by simpa using hr')
  · simp

omit [Fintype n] [DecidableEq n] [DecidableEq Y] [Fintype R] [DecidableEq R]
  [DecidablePred act] in
/-- `CellNoBot`, along the columns. -/
theorem cellNoBot_col {σ : Matrix n n ℂ} (hσ : σ.IsHermitian) (hnb : CellNoBot e act σ) {r : R}
    (hr : act r) (s : n) : ∑ y, σ s (e.symm (some y, r)) = 0 := by
  have h : ∑ y, σ s (e.symm (some y, r)) = star (∑ y, σ (e.symm (some y, r)) s) := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun y _ ↦ (hσ.apply _ _).symm
  rw [h, hnb r hr s, star_zero]

omit [DecidableEq n] in
/-- The correction along recorded rows is invisible to a state with no decompressed `⊥`. -/
theorem trace_corr1_mul (κ : R → ℝ) {σ : Matrix n n ℂ} (hσ : σ.IsHermitian)
    (hnb : CellNoBot e act σ) : (corr1 e act τ S κ * σ).trace = 0 := by
  rw [Matrix.trace]
  simp only [diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun s _ ↦ ?_
  rw [sum_rest_eq (e := e) (e s).2 fun t ht ↦ by
    simp only [corr1, of_apply]
    rw [ite_eq_right fun h' ↦ ht h'.2.2.symm, zero_mul]]
  rw [Fintype.sum_option]
  by_cases ha : act (e s).2
  · simp only [corr1, of_apply, Equiv.apply_symm_apply, ne_eq, not_true_eq_false, and_false,
      ↓reduceIte, zero_mul, zero_add, reduceCtorEq, not_false_eq_true, and_true, ha]
    rw [← Finset.mul_sum, cellNoBot_col hσ hnb ha, mul_zero]
  · simp only [corr1, of_apply, Equiv.apply_symm_apply, ha, false_and, ↓reduceIte, zero_mul,
      Finset.sum_const_zero, add_zero]

omit [DecidableEq n] in
/-- The correction along recorded columns is invisible to a state with no decompressed `⊥`. -/
theorem trace_corr2_mul (κ : R → ℝ) {σ : Matrix n n ℂ} (hnb : CellNoBot e act σ) :
    (corr2 e act τ S κ * σ).trace = 0 := by
  rw [Matrix.trace]
  refine Finset.sum_eq_zero fun t _ ↦ ?_
  rw [diag_apply, Matrix.mul_apply, sum_rest_eq (e := e) (e t).2 fun s hs ↦ by
    simp only [corr2, of_apply]
    rw [ite_eq_right fun h' ↦ hs h'.2.2.symm, zero_mul]]
  rw [Fintype.sum_option]
  by_cases ha : act (e t).2
  · simp only [corr2, of_apply, Equiv.apply_symm_apply, ne_eq, not_true_eq_false, and_false,
      ↓reduceIte, zero_mul, zero_add, reduceCtorEq, not_false_eq_true, and_true, ha]
    rw [← Finset.mul_sum, hnb _ ha t, mul_zero]
  · simp only [corr2, of_apply, Equiv.apply_symm_apply, ha, false_and, ↓reduceIte, zero_mul,
      Finset.sum_const_zero, add_zero]

variable (e act) in
/-- The recorded cells of active rests whose value is in `D`: the support of the cross term. -/
noncomputable def pd (D : Y → R → Prop) [∀ y r, Decidable (D y r)] (t : n) : ℝ :=
  if act (e t).2 then (e t).1.elim 0 (fun y ↦ if D y (e t).2 then 1 else 0) else 0

variable (e act τ) in
/-- The weight of the empty-to-recorded amplitudes of an empty cell of an active rest. -/
noncomputable def ew (κ : R → ℝ) (t : n) : ℝ :=
  if act (e t).2 ∧ (e t).1 = none then ∑ y, xv e τ S κ (some y) (e t).2 ^ 2 else 0

omit [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y] [Fintype R] [DecidableEq R] in
theorem pd_mem (D : Y → R → Prop) [∀ y r, Decidable (D y r)] (t : n) :
    pd e act D t = 0 ∨ pd e act D t = 1 := by
  unfold pd
  split_ifs
  · rcases (e t).1 with _ | y
    · simp
    · simp only [Option.elim_some]
      split_ifs <;> simp
  · simp

omit [Fintype R] in
theorem pd_mul_xm (κ : R → ℝ) (D : Y → R → Prop) [∀ y r, Decidable (D y r)]
    (hD : ∀ r, act r → ∀ y, ¬ D y r → gw e τ S (some y) r = κ r) :
    diagonal (fun t ↦ ((pd e act D t : ℝ) : ℂ)) * xm e act τ S κ = xm e act τ S κ := by
  ext t s
  rw [diagonal_mul]
  simp only [xm, of_apply]
  split_ifs with hc
  · obtain ⟨hs, -, hr⟩ := hc
    rcases ht1 : (e t).1 with _ | y
    · simp [xv]
    · by_cases hy : D y (e s).2
      · simp [pd, hr, hs, ht1, hy]
      · simp [xv, hD _ hs y hy]
  · simp

theorem xm_gram (κ : R → ℝ) :
    (xm e act τ S κ)ᴴ * xm e act τ S κ = diagonal (fun t ↦ ((ew e act τ S κ t : ℝ) : ℂ)) := by
  ext s' s
  rw [Matrix.mul_apply, diagonal_apply]
  simp only [conjTranspose_apply, xm, of_apply]
  by_cases hs : act (e s).2 ∧ (e s).1 = none
  · by_cases hss : s' = s
    · subst hss
      rw [ite_eq_left rfl, sum_rest_eq (e s').2 fun t ht ↦ by
        rw [ite_eq_right fun h' ↦ ht h'.2.2, mul_zero]]
      rw [Fintype.sum_option]
      simp only [Equiv.apply_symm_apply, hs, and_self, ↓reduceIte, ew, xv, Complex.star_def,
        Complex.conj_ofReal]
      push_cast
      simp only [mul_zero, zero_add, sq]
    · rw [ite_eq_right hss]
      refine Finset.sum_eq_zero fun t _ ↦ ?_
      by_cases h1 : act (e s').2 ∧ (e s').1 = none ∧ (e t).2 = (e s').2
      · by_cases h2 : act (e s).2 ∧ (e s).1 = none ∧ (e t).2 = (e s).2
        · exact absurd (eq_of_rest (e := e) (h1.2.2.symm.trans h2.2.2)
            (h1.2.1.trans h2.2.1.symm)) hss
        · rw [ite_eq_right h2, mul_zero]
      · rw [ite_eq_right h1, star_zero, zero_mul]
  · have h0 : ∀ t, ¬ (act (e s).2 ∧ (e s).1 = none ∧ (e t).2 = (e s).2) :=
      fun t h' ↦ hs ⟨h'.1, h'.2.1⟩
    simp only [h0, ↓reduceIte, mul_zero, Finset.sum_const_zero, ew]
    split_ifs with hss hin
    · exact absurd (hss ▸ hin) hs
    · simp
    · rfl

theorem re_trace_diagonal_mul (f : n → ℝ) (σ : Matrix n n ℂ) :
    ((diagonal fun s ↦ ((f s : ℝ) : ℂ)) * σ).trace.re = ∑ s, f s * (σ s s).re := by
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [diag_apply, diagonal_mul, Complex.re_ofReal_mul]

/-- **The refined read cost of a cell read.** For a state with no decompressed `⊥` at the cell,
the flip of the event is at most `∑ fd σ_ss + 2 √(E p)`: `fd` on empty cells the mean flip, on
recorded cells the recorded outcome's weight minus the event (at most `2/|Y|` plus the classical
move), on hardwired cells the classical move; `E = ∑ ew σ_ss` the empty-to-recorded amplitudes,
`p = ∑ pd σ_ss` the recorded cells whose value is in `D` (outside `D` the outcome's weight is the
reference `κ`). -/
theorem re_trace_flipOp_le (h : CellRead e act μ τ K) (hc : ClsOff e act K idx φ) (κ : R → ℝ)
    (D : Y → R → Prop) [∀ y r, Decidable (D y r)]
    (hD : ∀ r, act r → ∀ y, ¬ D y r → gw e τ S (some y) r = κ r) {σ : Matrix n n ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot e act σ) :
    (flipOp K S * σ).trace.re ≤ ∑ s, fd e act τ S φ s * (σ s s).re +
      2 * (√(∑ s, ew e act τ S κ s * (σ s s).re) * √(∑ s, pd e act D s * (σ s s).re)) := by
  set A := ∑ s, fd e act τ S φ s * (σ s s).re
  set E := ∑ s, ew e act τ S κ s * (σ s s).re
  set p := ∑ s, pd e act D s * (σ s s).re
  set M := xm e act τ S κ
  set P : Matrix n n ℂ := diagonal fun t ↦ ((pd e act D t : ℝ) : ℂ)
  have hre : ∀ s, 0 ≤ (σ s s).re := fun s ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hE : 0 ≤ E := Finset.sum_nonneg fun s _ ↦ mul_nonneg (by
    unfold ew
    split_ifs
    · exact Finset.sum_nonneg fun y _ ↦ sq_nonneg _
    · exact le_rfl) (hre s)
  have hp : 0 ≤ p := Finset.sum_nonneg fun s _ ↦ mul_nonneg (by
    rcases pd_mem (e := e) (act := act) D s with h0 | h0 <;> rw [h0]; norm_num) (hre s)
  have hPh : Pᴴ = P := by
    rw [diagonal_conjTranspose]
    congr 1
    funext t
    simp [Complex.conj_ofReal]
  have hPP : P * P = P := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext t
    rcases pd_mem (e := e) (act := act) D t with h0 | h0 <;> rw [h0] <;> norm_num
  have hPM : P * M = M := pd_mul_xm S κ D hD
  have hMP : Mᴴ * P = Mᴴ := by
    rw [← hPh, ← conjTranspose_mul, hPM]
  have hF : (flipOp K S * σ).trace.re = A + (M * σ).trace.re + (Mᴴ * σ).trace.re := by
    rw [flipOp_eq_fcor S h hc κ, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul,
      Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
      trace_corr1_mul S κ hσ.isHermitian hnb, trace_corr2_mul S κ hnb, add_zero, add_zero,
      Complex.add_re, Complex.add_re, re_trace_diagonal_mul]
  have hle : ∀ s : ℝ, 0 < s → (flipOp K S * σ).trace.re - A + p + E ≤
      (1 + s) * p + (1 + s⁻¹) * E := by
    intro s hs
    have hsq : (Mᴴ - s • P) * (Mᴴ - s • P)ᴴ = Mᴴ * M - s • Mᴴ - s • M + (s * s) • P := by
      simp only [conjTranspose_sub, conjTranspose_smul, hPh, conjTranspose_conjTranspose,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hMP, hPM, hPP,
        star_trivial]
      rw [smul_sub, smul_smul]
      abel
    have h0 := ((posSemidef_self_mul_conjTranspose (Mᴴ - s • P)).smul
      (inv_nonneg.mpr hs.le)).trace_mul_re_nonneg hσ
    have hEσ : ((diagonal fun t ↦ ((ew e act τ S κ t : ℝ) : ℂ)) * σ).trace.re = E :=
      re_trace_diagonal_mul _ _
    have hPσ : (P * σ).trace.re = p := re_trace_diagonal_mul _ _
    rw [hsq, xm_gram] at h0
    simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add,
      Matrix.trace_sub, Matrix.trace_smul, Complex.add_re, Complex.sub_re, Complex.smul_re,
      smul_eq_mul, hEσ, hPσ] at h0
    have hx : s⁻¹ * (E - s * (Mᴴ * σ).trace.re - s * (M * σ).trace.re + s * s * p) =
        s⁻¹ * E - (Mᴴ * σ).trace.re - (M * σ).trace.re + s * p := by
      field_simp
    rw [hF]
    nlinarith [hx, h0]
  have hopt := Real.le_sq_sqrt_add_sqrt_of_forall hp hE hle
  rw [add_sq, Real.sq_sqrt hp, Real.sq_sqrt hE] at hopt
  nlinarith [Real.sqrt_nonneg p, Real.sqrt_nonneg E]

/-! ### The reference weight and the flip values -/

variable (e) in
/-- **The reference weight** of a rest: the weight of a recorded outcome whose value neither flips
the event when recorded nor changes it through the move of the rest. -/
noncomputable def kap (r : R) : ℝ :=
  (1 - (Fintype.card Y : ℝ)⁻¹) * q0 e S r +
    (∑ y, ind S (e.symm (some y, r))) / (Fintype.card Y : ℝ) ^ 2

variable (e τ) in
/-- The values whose read moves the rest so that the event changes for some cell content. -/
def Moves (y : Y) (r : R) : Prop :=
  ∃ a, ind S (e.symm (a, τ (some y) r)) ≠ ind S (e.symm (a, r))

variable (e τ) in
/-- **The flip values** of a rest: recording the value flips the event, or reading it moves the
rest so that the event changes for some cell content. -/
def Flip (y : Y) (r : R) : Prop :=
  ind S (e.symm (some y, r)) ≠ q0 e S r ∨ Moves e τ S y r

/-- Flip values, decided classically. -/
noncomputable instance flipDec (y : Y) (r : R) : Decidable (Flip e τ S y r) :=
  Classical.propDecidable _

/-- Moving values, decided classically. -/
noncomputable instance movesDec (y : Y) (r : R) : Decidable (Moves e τ S y r) :=
  Classical.propDecidable _

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
/-- Off the flip values a recorded outcome weighs the reference weight. -/
theorem gw_eq_kap [Nonempty Y] {y : Y} {r : R} (hy : ¬ Flip e τ S y r) :
    gw e τ S (some y) r = kap e S r := by
  simp only [Flip, Moves, not_or, not_exists, not_not] at hy
  obtain ⟨h1, h2⟩ := hy
  rw [gw]
  simp only [h2]
  rw [Fintype.sum_option, cr_none_some_sq]
  have hterm : ∀ x : Y, cr (some x) (some y) ^ 2 * ind S (e.symm (some x, r)) =
      (if x = y then (1 - 2 * (Fintype.card Y : ℝ)⁻¹) * ind S (e.symm (some y, r)) else 0) +
        (Fintype.card Y : ℝ)⁻¹ * (Fintype.card Y : ℝ)⁻¹ * ind S (e.symm (some x, r)) :=
    fun x ↦ by
      simp only [cr]
      split_ifs with hx
      · subst hx
        ring
      · ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    ← Finset.mul_sum]
  rw [h1, kap, q0]
  ring

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
theorem gw_nonneg (o : Option Y) (r : R) : 0 ≤ gw e τ S o r :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (sq_nonneg _) (ind_nonneg S _)

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
theorem gw_some_le_one [Nonempty Y] (y : Y) (r : R) : gw e τ S (some y) r ≤ 1 := by
  rw [gw, ← sum_cr_sq y]
  exact Finset.sum_le_sum fun _ _ ↦ mul_le_of_le_one_right (sq_nonneg _) (ind_le_one S _)

omit [Fintype n] [DecidableEq n] [DecidableEq Y] [Fintype R] [DecidableEq R] in
theorem kap_nonneg [Nonempty Y] (r : R) : 0 ≤ kap e S r := by
  have hN : (1 : ℝ) ≤ Fintype.card Y := Nat.one_le_cast.mpr Fintype.card_pos
  have h1 : 0 ≤ 1 - (Fintype.card Y : ℝ)⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hN)
  exact add_nonneg (mul_nonneg h1 (ind_nonneg S _))
    (div_nonneg (Finset.sum_nonneg fun _ _ ↦ ind_nonneg S _) (sq_nonneg _))

omit [Fintype n] [DecidableEq n] [DecidableEq Y] [Fintype R] [DecidableEq R] in
theorem kap_le_one [Nonempty Y] (r : R) : kap e S r ≤ 1 := by
  have hN : (1 : ℝ) ≤ Fintype.card Y := Nat.one_le_cast.mpr Fintype.card_pos
  have h1 : 0 ≤ 1 - (Fintype.card Y : ℝ)⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hN)
  have hs : ∑ y, ind S (e.symm (some y, r)) ≤ Fintype.card Y :=
    (Finset.sum_le_sum fun _ _ ↦ ind_le_one S _).trans (by simp)
  calc kap e S r ≤ (1 - (Fintype.card Y : ℝ)⁻¹) * 1 +
        (Fintype.card Y : ℝ) / (Fintype.card Y : ℝ) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left (ind_le_one S _) h1)
          (div_le_div_of_nonneg_right hs (sq_nonneg _))
    _ = 1 := by
        field_simp
        ring

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
/-- **The empty-to-recorded weight** of an empty cell is at most its number of flip values over
`|Y|`. -/
theorem ew_kap_le [Nonempty Y] (s : n) : ew e act τ S (kap e S) s ≤
    if act (e s).2 ∧ (e s).1 = none then
      ((Finset.univ.filter fun y ↦ Flip e τ S y (e s).2).card : ℝ) / Fintype.card Y else 0 := by
  unfold ew
  split_ifs with hs
  · rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, Finset.sum_div]
    refine Finset.sum_le_sum fun y _ ↦ ?_
    simp only [xv, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    split_ifs with hy
    · rw [Nat.cast_one]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      have := gw_nonneg (e := e) (τ := τ) S (some y) (e s).2
      have := gw_some_le_one (e := e) (τ := τ) S y (e s).2
      have := kap_nonneg (e := e) S (e s).2
      have := kap_le_one (e := e) S (e s).2
      nlinarith
    · rw [gw_eq_kap S hy, sub_self]
      simp
  · exact le_rfl

omit [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y] [Fintype R] [DecidableEq R] in
/-- **For an event up-closed in the read cell, the flip-recorded cells are in the event or move
the rest**: if an empty cell's state is in the event, so is every recorded one. -/
theorem pd_flip_le (hup : ∀ r, act r → q0 e S r = 1 → ∀ y, ind S (e.symm (some y, r)) = 1)
    (s : n) : pd e act (Flip e τ S) s ≤ ind S s + pd e act (Moves e τ S) s := by
  unfold pd
  split_ifs with ha
  · rcases hs1 : (e s).1 with _ | y
    · simp only [Option.elim_none, add_zero]
      exact ind_nonneg S s
    · have hs : s = e.symm (some y, (e s).2) := by rw [← hs1, Prod.mk.eta, Equiv.symm_apply_apply]
      simp only [Option.elim_some]
      by_cases hf : Flip e τ S y (e s).2
      · rw [ite_eq_left hf]
        rcases hf with hf | hf
        · have h1 : ind S s = 1 := by
            rw [hs]
            rcases ind_mem S (e.symm (some y, (e s).2)) with h0 | h0
            · rcases ind_mem S (e.symm (none, (e s).2)) with h2 | h2
              · exact absurd (h0.trans h2.symm) hf
              · exact absurd (h0.symm.trans (hup _ ha h2 y)) zero_ne_one
            · exact h0
          rw [h1]
          split_ifs <;> norm_num
        · rw [ite_eq_left hf]
          linarith [ind_nonneg S s]
      · rw [ite_eq_right hf]
        split_ifs <;> linarith [ind_nonneg S s]
  · simpa using ind_nonneg S s

omit [DecidableEq Y] [Fintype R] [DecidableEq R] [DecidablePred act] in
/-- **`CellNoBot` from a support condition in a conjugated basis.** If `U` is an involution, the
conjugated state `U σ U` is supported on rows satisfying `G`, and for every active rest and every
row `a` satisfying `G` the column sums `∑_y U (some y, r) a` vanish, then `σ` has no
decompressed `⊥` at the cell. -/
theorem cellNoBot_of_conj {G : n → Prop} (U : Matrix n n ℂ) (hU : U * U = 1)
    {σ : Matrix n n ℂ} (hsupp : ∀ a b, (U * σ * U) a b ≠ 0 → G a)
    (hcell : ∀ r, act r → ∀ a, G a → ∑ y, U (e.symm (some y, r)) a = 0) :
    CellNoBot e act σ := by
  intro r hr t
  set X := U * σ * U with hX
  have hσ : σ = U * (X * U) := by
    calc σ = (U * U) * σ * (U * U) := by rw [hU, Matrix.one_mul, Matrix.mul_one]
      _ = U * (X * U) := by simp only [hX, Matrix.mul_assoc]
  rw [hσ]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  rw [← Finset.sum_mul]
  by_cases hG : G a
  · rw [hcell r hr a hG, zero_mul]
  · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b _ ↦ ?_)
    by_contra hb
    exact hG (hsupp a b (left_ne_zero_of_mul hb))

variable (e act τ) in
/-- The diagonal term `A = ∑ fd σ_ss` of the refined read cost. -/
noncomputable def costA (φ : n → n) (σ : Matrix n n ℂ) : ℝ := ∑ s, fd e act τ S φ s * (σ s s).re

variable (e act τ) in
/-- The empty-to-recorded term `E = ∑ ew σ_ss` of the refined read cost (reference `kap`). -/
noncomputable def costE (σ : Matrix n n ℂ) : ℝ := ∑ s, ew e act τ S (kap e S) s * (σ s s).re

variable (e act τ) in
/-- The flip-recorded mass `p = ∑ pd σ_ss` of the refined read cost. -/
noncomputable def costP (σ : Matrix n n ℂ) : ℝ := ∑ s, pd e act (Flip e τ S) s * (σ s s).re

variable (e act τ) in
/-- The mass of the recorded cells whose value moves the rest so that the event changes. -/
noncomputable def costM (σ : Matrix n n ℂ) : ℝ := ∑ s, pd e act (Moves e τ S) s * (σ s s).re

variable (e act τ) in
/-- **The refined read cost** `A + 2 √(E p)`. -/
noncomputable def cellCost (φ : n → n) (σ : Matrix n n ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (costA e act τ S φ σ) +
    2 * (ENNReal.ofReal (costE e act τ S σ) * ENNReal.ofReal (costP e act τ S σ)) ^ (2⁻¹ : ℝ)

omit [DecidableEq n] [Fintype R] [DecidableEq R] in
theorem costE_nonneg {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) : 0 ≤ costE e act τ S σ :=
  Finset.sum_nonneg fun s _ ↦ mul_nonneg (by
    unfold ew
    split_ifs
    · exact Finset.sum_nonneg fun y _ ↦ sq_nonneg _
    · exact le_rfl) (Complex.nonneg_iff.1 hσ.diag_nonneg).1

omit [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y] [Fintype R] [DecidableEq R] in
theorem pd_nonneg (D : Y → R → Prop) [∀ y r, Decidable (D y r)] (s : n) : 0 ≤ pd e act D s := by
  rcases pd_mem (e := e) (act := act) D s with h0 | h0 <;> rw [h0]
  norm_num

omit [DecidableEq n] [Fintype Y] [DecidableEq Y] [Fintype R] [DecidableEq R] in
theorem costP_nonneg {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) : 0 ≤ costP e act τ S σ :=
  Finset.sum_nonneg fun s _ ↦ mul_nonneg (pd_nonneg _ s) (Complex.nonneg_iff.1 hσ.diag_nonneg).1

omit [DecidableEq n] [Fintype Y] [DecidableEq Y] [Fintype R] [DecidableEq R] in
theorem costM_nonneg {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) : 0 ≤ costM e act τ S σ :=
  Finset.sum_nonneg fun s _ ↦ mul_nonneg (pd_nonneg _ s) (Complex.nonneg_iff.1 hσ.diag_nonneg).1

omit [DecidableEq n] [Fintype Y] [DecidableEq Y] [Fintype R] [DecidableEq R] in
/-- For an event up-closed in the read cell, `p ≤ w + m`: the flip-recorded mass is at most the
event weight plus the moving mass. -/
theorem costP_le (hup : ∀ r, act r → q0 e S r = 1 → ∀ y, ind S (e.symm (some y, r)) = 1)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    costP e act τ S σ ≤ ∑ s, ind S s * (σ s s).re + costM e act τ S σ := by
  rw [costP, costM, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (pd_flip_le S hup s) (Complex.nonneg_iff.1 hσ.diag_nonneg).1

/-! ### Per-state bounds of the diagonal term -/

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
/-- **An empty cell costs its mean flip**, at most `Δ / |Y|` (`diag_le`). -/
theorem fd_none_le [Nonempty Y] {s : n} (ha : act (e s).2) (h0 : (e s).1 = none) :
    fd e act τ S φ s ≤ chw e τ S (e s).2 / Fintype.card Y := by
  have hq : ind S s = q0 e S (e s).2 := by rw [q0, ← h0, Prod.mk.eta, Equiv.symm_apply_apply]
  rw [fd, ite_eq_left ha, h0, gdiag, gbar, hq]
  exact diag_le S _

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
/-- **A recorded cell costs at most `2/|Y|` plus its classical move**: the event at the recorded
value with the moved rest, minus the event. -/
theorem fd_some_le [Nonempty Y] {s : n} {y : Y} (ha : act (e s).2) (h1 : (e s).1 = some y) :
    fd e act τ S φ s ≤
      ind S (e.symm (some y, τ (some y) (e s).2)) - ind S s + 2 / Fintype.card Y := by
  rw [fd, ite_eq_left ha, h1, gdiag]
  have hN : (1 : ℝ) ≤ Fintype.card Y := Nat.one_le_cast.mpr Fintype.card_pos
  set q' : Option Y → ℝ := fun a ↦ ind S (e.symm (a, τ (some y) (e s).2))
  have hg : gw e τ S (some y) (e s).2 - q' (some y) =
      ∑ a, cr a (some y) ^ 2 * (q' a - q' (some y)) := by
    rw [gw]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_cr_sq, one_mul]
    rfl
  have hle : ∑ a, cr a (some y) ^ 2 * (q' a - q' (some y)) ≤
      ∑ a, cr a (some y) ^ 2 - cr (some y) (some y) ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (some y)),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ (some y)), sub_self, mul_zero, add_zero,
      add_sub_cancel_right]
    refine Finset.sum_le_sum fun a _ ↦ ?_
    have h1 := ind_le_one S (e.symm (a, τ (some y) (e s).2))
    have h2 := ind_nonneg S (e.symm (some y, τ (some y) (e s).2))
    have h3 := sq_nonneg (cr a (some y))
    change cr a (some y) ^ 2 * (ind S (e.symm (a, τ (some y) (e s).2)) -
      ind S (e.symm (some y, τ (some y) (e s).2))) ≤ cr a (some y) ^ 2
    nlinarith
  have hc : ∑ a, cr a (some y) ^ 2 - cr (some y) (some y) ^ 2 ≤ 2 / Fintype.card Y := by
    rw [sum_cr_sq]
    simp only [cr, ↓reduceIte]
    have : 0 < (Fintype.card Y : ℝ)⁻¹ := inv_pos.mpr (by linarith)
    rw [div_eq_mul_inv]
    nlinarith
  change gw e τ S (some y) (e s).2 - ind S s ≤ q' (some y) - ind S s + 2 / Fintype.card Y
  linarith

omit [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R] in
/-- **A hardwired cell costs its classical move**: `1_S (φ s) - 1_S s`. -/
theorem fd_off {s : n} (ha : ¬ act (e s).2) : fd e act τ S φ s = ind S (φ s) - ind S s := by
  rw [fd, ite_eq_right ha]

/-! ### Reads that keep the rest -/

variable (e) in
/-- The number of values whose recording flips the event at the cell of `s`. -/
noncomputable def cntK (s : n) : ℕ :=
  (Finset.univ.filter fun b : Y ↦ ind S (e.symm (some b, (e s).2)) ≠ ind S s).card

omit [DecidableEq n] [Fintype Y] [DecidableEq Y] [Fintype R] [DecidableEq R] in
/-- A read that keeps the rest moves no recorded mass. -/
theorem costM_keep (hτ : ∀ y r, τ (some y) r = r) (σ : Matrix n n ℂ) :
    costM e act τ S σ = 0 := by
  unfold costM
  refine Finset.sum_eq_zero fun s _ ↦ ?_
  have h0 : pd e act (Moves e τ S) s = 0 := by
    unfold pd
    split_ifs
    · rcases (e s).1 with _ | y
      · rfl
      · simp only [Option.elim_some]
        refine ite_eq_right fun hm ↦ ?_
        obtain ⟨a, ha⟩ := hm
        refine ha ?_
        rw [hτ]
    · rfl
  rw [h0, zero_mul]

omit [DecidableEq n] [Fintype R] [DecidableEq R] in
/-- **The empty-to-recorded term of a read that keeps the rest**: at most the number of values
whose recording flips the event, over `|Y|`, on the empty cells. -/
theorem costE_keep_le [Nonempty Y] (hτ : ∀ y r, τ (some y) r = r) {σ : Matrix n n ℂ}
    (hσ : σ.PosSemidef) :
    costE e act τ S σ ≤ ∑ s, (if act (e s).2 ∧ (e s).1 = none then
      (cntK e S s : ℝ) / Fintype.card Y else 0) * (σ s s).re := by
  unfold costE
  refine Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_right ((ew_kap_le S s).trans ?_)
    (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  split_ifs with hs
  · refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card fun y hy ↦ ?_))
      (Nat.cast_nonneg _)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rcases hy with hy | ⟨a, ha⟩
    · have hq : ind S s = q0 e S (e s).2 := by
        rw [q0, ← hs.2, Prod.mk.eta, Equiv.symm_apply_apply]
      rwa [hq]
    · exact absurd (by rw [hτ]) ha
  · exact le_rfl

omit [DecidableEq n] [Fintype R] [DecidableEq R] in
/-- **The diagonal term of a read that keeps the rest and the hardwired states**: the flip counts
over `|Y|` on the empty cells, `2/|Y|` on the recorded cells, `0` on the hardwired cells. -/
theorem costA_keep_le [Nonempty Y] (hτ : ∀ y r, τ (some y) r = r)
    (hφ : ∀ s, ¬ act (e s).2 → φ s = s) {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    costA e act τ S φ σ ≤ ∑ s, ((if act (e s).2 ∧ (e s).1 = none then
      (cntK e S s : ℝ) / Fintype.card Y else 0) +
        (if act (e s).2 ∧ (e s).1 ≠ none then (2 : ℝ) / Fintype.card Y else 0)) * (σ s s).re := by
  unfold costA
  refine Finset.sum_le_sum fun s _ ↦
    mul_le_mul_of_nonneg_right ?_ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  by_cases ha : act (e s).2
  · rcases h1 : (e s).1 with _ | y
    · rw [ite_eq_left ⟨ha, rfl⟩, ite_eq_right fun h' ↦ h'.2 rfl, add_zero]
      have hq : ind S s = q0 e S (e s).2 := by
        rw [q0, ← h1, Prod.mk.eta, Equiv.symm_apply_apply]
      refine (fd_none_le S ha h1).trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
      refine (Xmss.Assembly.chw_le_card_of_keep S _ fun y ↦ hτ y _).trans
        (Nat.cast_le.mpr (Finset.card_le_card fun b hb ↦ ?_))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      rwa [hq]
    · rw [ite_eq_right fun h' ↦ Option.some_ne_none y h'.2, ite_eq_left ⟨ha, by simp⟩, zero_add]
      have h := fd_some_le S (τ := τ) (φ := φ) ha h1
      rwa [hτ, ← h1, Prod.mk.eta, Equiv.symm_apply_apply, sub_self, zero_add] at h
  · rw [ite_eq_right fun h' ↦ ha h'.1, ite_eq_right fun h' ↦ ha h'.1, add_zero, fd_off S ha,
      hφ s ha, sub_self]

end core

/-! ## The read ports of the hardwired register -/

section hw

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

/-- `ofReal (w + (A + 2 √E √p)) ≤ ofReal w + ofReal A + 2 √(E p)`. -/
theorem ofReal_add_two_sqrt_le {w A E p : ℝ} (hE : 0 ≤ E) :
    ENNReal.ofReal (w + (A + 2 * (√E * √p))) ≤ ENNReal.ofReal w +
      (ENNReal.ofReal A + 2 * (ENNReal.ofReal E * ENNReal.ofReal p) ^ (2⁻¹ : ℝ)) := by
  refine ENNReal.ofReal_add_le.trans (add_le_add le_rfl
    (ENNReal.ofReal_add_le.trans (add_le_add le_rfl (le_of_eq ?_))))
  rw [← Real.sqrt_mul hE, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul hE, ENNReal.ofReal_rpow_inv_two]
  norm_num

/-- The event weight of the hardwired register as a diagonal sum. -/
theorem potential_eq_sum (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (τ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    QuantumRuntime.potential (hwProjector S) τ =
      ENNReal.ofReal (∑ q, ind (liftSet S) q * (τ q q).re) := by
  obtain ⟨hQ, hQQ⟩ := one_kronecker_hwProjector_proj S
  rw [QuantumRuntime.potential, MatrixMap.amplifyLeft_conj, MatrixMap.trace_conj_apply, hQ, hQQ,
    one_kronecker_hwProjector, indProj, re_trace_diagonal_mul]

/-- The event weights after a classical step, summed over the outcomes. -/
theorem tsum_potential_conj (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] {ι : Type}
    [Fintype ι] (K : ι → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    ∑' r, QuantumRuntime.potential (hwProjector S) (MatrixMap.conj (K r) σ) =
      ENNReal.ofReal (((∑ r, (K r)ᴴ * indProj (liftSet S) * K r) * σ).trace.re) := by
  obtain ⟨hQ, hQQ⟩ := one_kronecker_hwProjector_proj S
  rw [one_kronecker_hwProjector] at hQ hQQ
  have hpot : ∀ τ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ,
      QuantumRuntime.potential (hwProjector S) τ =
        ENNReal.ofReal (MatrixMap.conj (indProj (liftSet S)) τ).trace.re := fun τ ↦ by
    rw [QuantumRuntime.potential, MatrixMap.amplifyLeft_conj, one_kronecker_hwProjector]
  simp only [hpot, ← LinearMap.comp_apply, ← MatrixMap.conj_mul]
  have hterm : ∀ r, (MatrixMap.conj (indProj (liftSet S) * K r) σ).trace =
      ((K r)ᴴ * indProj (liftSet S) * K r * σ).trace := fun r ↦ by
    rw [MatrixMap.trace_conj_apply, conjTranspose_mul, hQ, Matrix.mul_assoc (K r)ᴴ,
      ← Matrix.mul_assoc (indProj (liftSet S)) (indProj (liftSet S)), hQQ]
    simp only [Matrix.mul_assoc]
  have hnn : ∀ r, 0 ≤ (MatrixMap.conj (indProj (liftSet S) * K r) σ).trace.re := fun r ↦
    (hσ.mul_mul_conjTranspose_same _).trace_re_nonneg
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hnn r]
  congr 1
  simp only [hterm, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]

variable {Y R : Type} [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype R] [DecidableEq R]
  {e : Unit × HwReg X Z M ≃ Option Y × R} {act : R → Prop} [DecidablePred act] {μ : R → M}
  {τ : Option Y → R → R} {K : Option Y × M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
  {idx : Unit × HwReg X Z M → Option Y × M} {φ : Unit × HwReg X Z M → Unit × HwReg X Z M}

omit [DecidableEq Y] [Nonempty Y] in
theorem re_trace_gram_eq (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    ((∑ r, (K r)ᴴ * indProj (liftSet S) * K r) * σ).trace.re =
      ∑ q, ind (liftSet S) q * (σ q q).re + (flipOp K (liftSet S) * σ).trace.re := by
  rw [flipOp, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, indProj, re_trace_diagonal_mul]
  ring

/-- **The refined read cost, for a cell read of the hardwired register**: on a state with no
decompressed `⊥` at the read cell, the event weight rises by at most `cellCost`. -/
theorem potential_cellRead_le (h : CellRead e act μ τ K) (hc : ClsOff e act K idx φ)
    (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot e act σ) :
    ∑' r, QuantumRuntime.potential (hwProjector S) (MatrixMap.conj (K r) σ) ≤
      QuantumRuntime.potential (hwProjector S) σ + cellCost e act τ (liftSet S) φ σ := by
  have hF : (flipOp K (liftSet S) * σ).trace.re ≤ costA e act τ (liftSet S) φ σ +
      2 * (√(costE e act τ (liftSet S) σ) * √(costP e act τ (liftSet S) σ)) :=
    re_trace_flipOp_le (liftSet S) h hc (kap e (liftSet S)) (Flip e τ (liftSet S))
      (fun _ _ _ hy ↦ gw_eq_kap _ hy) hσ hnb
  rw [tsum_potential_conj S K hσ, potential_eq_sum, re_trace_gram_eq]
  exact (ENNReal.ofReal_le_ofReal (add_le_add le_rfl hF)).trans
    (ofReal_add_two_sqrt_le (costE_nonneg (e := e) (act := act) (τ := τ) (liftSet S) hσ))

/-- **The square-root form, for an event up-closed in the read cell**: if an empty cell's state
is in the event, so is every recorded one. Then the flip-recorded mass is at most the event weight
plus the moving mass `m`, and the event weight after the read is at most
`(√w + √E)² + A + 2 √(E m)`. For a read that does not move the rest across the event, `m = 0`:
the read costs like a sponge call with error `E`, plus `A`. -/
theorem potential_cellRead_le_sqrt (h : CellRead e act μ τ K) (hc : ClsOff e act K idx φ)
    (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (hup : ∀ r, act r → q0 e (liftSet S) r = 1 → ∀ y, ind (liftSet S) (e.symm (some y, r)) = 1)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot e act σ) :
    ∑' r, QuantumRuntime.potential (hwProjector S) (MatrixMap.conj (K r) σ) ≤
      (QuantumRuntime.potential (hwProjector S) σ ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (costE e act τ (liftSet S) σ) ^ (2⁻¹ : ℝ)) ^ 2 +
      (ENNReal.ofReal (costA e act τ (liftSet S) φ σ) +
        2 * (ENNReal.ofReal (costE e act τ (liftSet S) σ) *
          ENNReal.ofReal (costM e act τ (liftSet S) σ)) ^ (2⁻¹ : ℝ)) := by
  set w := ∑ q, ind (liftSet S) q * (σ q q).re
  set A := costA e act τ (liftSet S) φ σ
  set E := costE e act τ (liftSet S) σ
  set p := costP e act τ (liftSet S) σ
  set m := costM e act τ (liftSet S) σ
  have hw : 0 ≤ w := Finset.sum_nonneg fun q _ ↦
    mul_nonneg (ind_nonneg _ q) (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hE : 0 ≤ E := costE_nonneg (liftSet S) hσ
  have hm : 0 ≤ m := costM_nonneg (liftSet S) hσ
  have hF : (flipOp K (liftSet S) * σ).trace.re ≤ A + 2 * (√E * √p) :=
    re_trace_flipOp_le (liftSet S) h hc (kap e (liftSet S)) (Flip e τ (liftSet S))
      (fun _ _ _ hy ↦ gw_eq_kap _ hy) hσ hnb
  have hp : p ≤ w + m := costP_le (liftSet S) hup hσ
  have hsp : √p ≤ √w + √m := by
    refine (Real.sqrt_le_sqrt hp).trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hw, Real.sq_sqrt hm, Real.sqrt_nonneg w, Real.sqrt_nonneg m]
  have hreal : w + (flipOp K (liftSet S) * σ).trace.re ≤
      (√w + √E) ^ 2 + (A + 2 * (√E * √m)) := by
    have h1 : 2 * (√E * √p) ≤ 2 * (√E * √w) + 2 * (√E * √m) := by
      nlinarith [Real.sqrt_nonneg E]
    nlinarith [Real.sq_sqrt hw, Real.sq_sqrt hE, Real.sqrt_nonneg w, Real.sqrt_nonneg E]
  rw [tsum_potential_conj S K hσ, potential_eq_sum, re_trace_gram_eq, ENNReal.ofReal_rpow_inv_two,
    ENNReal.ofReal_rpow_inv_two, ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_pow (by positivity)]
  exact (ENNReal.ofReal_le_ofReal hreal).trans (ofReal_add_two_sqrt_le hE)

end hw

/-! ## The read ports of `h`, `k`, `k'` -/

section ports

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

/-- The classical move of a read of `h` at a hardwired cell: the memory reads the hardwired
value. -/
def phiH (z : Z) (upd : M → Option X → M) (q : Unit × HwReg X Z M) : Unit × HwReg X Z M :=
  ((), (q.2.1, q.2.2.1, upd q.2.2.2 (q.2.2.1.1 z)))

/-- The outcome of a read of `h` at a hardwired cell. -/
def idxH (z : Z) (q : Unit × HwReg X Z M) : Option X × M := (q.2.2.1.1 z, q.2.2.2)

/-- The classical move of a read of `k` at a hardwired cell. -/
def phiK (x : X) (upd : M → Option Z → M) (q : Unit × HwReg X Z M) : Unit × HwReg X Z M :=
  ((), (q.2.1, q.2.2.1, upd q.2.2.2 (q.2.2.1.2.1 x)))

/-- The outcome of a read of `k` at a hardwired cell. -/
def idxK (x : X) (q : Unit × HwReg X Z M) : Option Z × M := (q.2.2.1.2.1 x, q.2.2.2)

/-- The classical move of a read of `k'` at a hardwired cell. -/
def phiK' (x : X) (upd : M → Option Z → M) (q : Unit × HwReg X Z M) : Unit × HwReg X Z M :=
  ((), (q.2.1, q.2.2.1, upd q.2.2.2 (q.2.2.1.2.2 x)))

/-- The outcome of a read of `k'` at a hardwired cell. -/
def idxK' (x : X) (q : Unit × HwReg X Z M) : Option Z × M := (q.2.2.1.2.2 x, q.2.2.2)

/-- Activity of a rest of a read of `h`, decided. -/
instance actHDec (z : Z) : DecidablePred (actH (X := X) (M := M) z) :=
  fun r ↦ inferInstanceAs (Decidable (r.2.2.2.1.1 z = none))

/-- Activity of a rest of a read of `k`, decided. -/
instance actKDec (x : X) : DecidablePred (Xmss.Assembly.actK (Z₁ := Z) (M := M) x) :=
  fun r ↦ inferInstanceAs (Decidable (r.2.2.2.1.2.1 x = none))

/-- Activity of a rest of a read of `k'`, decided. -/
instance actK'Dec (x : X) : DecidablePred (Xmss.Assembly.actK' (Z₁ := Z) (M := M) x) :=
  fun r ↦ inferInstanceAs (Decidable (r.2.2.2.1.2.2 x = none))

omit [Fintype M] in
/-- **The hardwired columns of a read of `h` are classical.** -/
theorem clsOff_readH [Nonempty X] (z : Z) (upd : M → Option X → M) :
    ClsOff (splitH' z) (actH z) (fun r : Option X × M ↦ hwReadKraus (.readH z upd) r) (idxH z)
      (phiH z upd) where
  entry i t s hs := by
    obtain ⟨⟨⟩, D', W', m'⟩ := t
    obtain ⟨⟨⟩, D, W, m⟩ := s
    obtain ⟨o, m0⟩ := i
    change ¬ W.1 z = none at hs
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hs
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z upd (o, m0)) ((), D', W', m')
      ((), D, W, m) = _
    rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, readKrausH, clsKraus_apply]
    have hr : cellRead W.1 z o ⊗ₖ
        (1 : Matrix (Database X Z × Database X Z) (Database X Z × Database X Z) ℂ) =
        if o = some v then 1 else 0 := by
      rw [show cellRead W.1 z o = if o = some v then 1 else 0 by simp [cellRead, hv]]
      split_ifs <;> simp
    dsimp only
    rw [hr]
    simp only [idxH, phiH, hv]
    split_ifs <;> simp_all [Matrix.one_apply]
  inj s s' _ _ h1 h2 := by
    obtain ⟨⟨⟩, D, W, m⟩ := s
    obtain ⟨⟨⟩, D', W', m'⟩ := s'
    simp only [idxH, phiH, Prod.mk.injEq] at h1 h2
    obtain ⟨-, rfl⟩ := h1
    obtain ⟨-, rfl, rfl, -⟩ := h2
    rfl

omit [Fintype M] in
/-- **The hardwired columns of a read of `k` are classical.** -/
theorem clsOff_readK [Nonempty Z] (x : X) (upd : M → Option Z → M) :
    ClsOff (Xmss.Assembly.splitK x) (Xmss.Assembly.actK x)
      (fun r : Option Z × M ↦ hwReadKraus (.readK x upd) r) (idxK x) (phiK x upd) where
  entry i t s hs := by
    obtain ⟨⟨⟩, D', W', m'⟩ := t
    obtain ⟨⟨⟩, D, W, m⟩ := s
    obtain ⟨o, m0⟩ := i
    change ¬ W.2.1 x = none at hs
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hs
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK x upd (o, m0)) ((), D', W', m')
      ((), D, W, m) = _
    rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, readKrausK, clsKraus_apply]
    have hr : (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ (cellRead W.2.1 x o ⊗ₖ
        (1 : Matrix (Database X Z) (Database X Z) ℂ)) = if o = some v then 1 else 0 := by
      rw [show cellRead W.2.1 x o = if o = some v then 1 else 0 by simp [cellRead, hv]]
      split_ifs <;> simp
    dsimp only
    rw [hr]
    simp only [idxK, phiK, hv]
    split_ifs <;> simp_all [Matrix.one_apply]
  inj s s' _ _ h1 h2 := by
    obtain ⟨⟨⟩, D, W, m⟩ := s
    obtain ⟨⟨⟩, D', W', m'⟩ := s'
    simp only [idxK, phiK, Prod.mk.injEq] at h1 h2
    obtain ⟨-, rfl⟩ := h1
    obtain ⟨-, rfl, rfl, -⟩ := h2
    rfl

omit [Fintype M] in
/-- **The hardwired columns of a read of `k'` are classical.** -/
theorem clsOff_readK' [Nonempty Z] (x : X) (upd : M → Option Z → M) :
    ClsOff (Xmss.Assembly.splitK' x) (Xmss.Assembly.actK' x)
      (fun r : Option Z × M ↦ hwReadKraus (.readK' x upd) r) (idxK' x) (phiK' x upd) where
  entry i t s hs := by
    obtain ⟨⟨⟩, D', W', m'⟩ := t
    obtain ⟨⟨⟩, D, W, m⟩ := s
    obtain ⟨o, m0⟩ := i
    change ¬ W.2.2 x = none at hs
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hs
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK' x upd (o, m0)) ((), D', W', m')
      ((), D, W, m) = _
    rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, readKrausK', clsKraus_apply]
    have hr : (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
        ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellRead W.2.2 x o) =
        if o = some v then 1 else 0 := by
      rw [show cellRead W.2.2 x o = if o = some v then 1 else 0 by simp [cellRead, hv]]
      split_ifs <;> simp
    dsimp only
    rw [hr]
    simp only [idxK', phiK', hv]
    split_ifs <;> simp_all [Matrix.one_apply]
  inj s s' _ _ h1 h2 := by
    obtain ⟨⟨⟩, D, W, m⟩ := s
    obtain ⟨⟨⟩, D', W', m'⟩ := s'
    simp only [idxK', phiK', Prod.mk.injEq] at h1 h2
    obtain ⟨-, rfl⟩ := h1
    obtain ⟨-, rfl, rfl, -⟩ := h2
    rfl

/-- **The refined cost of a read port** (`cellCost` of its cell read, for the event `S`). -/
noncomputable def readCost (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] :
    HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞
  | .readH z upd, σ => cellCost (splitH' z) (actH z) (tauH z upd) (liftSet S) (phiH z upd) σ
  | .readK x upd, σ => cellCost (Xmss.Assembly.splitK x) (Xmss.Assembly.actK x)
      (Xmss.Assembly.tauK x upd) (liftSet S) (phiK x upd) σ
  | .readK' x upd, σ => cellCost (Xmss.Assembly.splitK' x) (Xmss.Assembly.actK' x)
      (Xmss.Assembly.tauK x upd) (liftSet S) (phiK' x upd) σ

/-- **No decompressed `⊥` at the cell of a read port.** -/
def ReadNoBot : HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → Prop
  | .readH z _, σ => CellNoBot (splitH' z) (actH z) σ
  | .readK x _, σ => CellNoBot (Xmss.Assembly.splitK x) (Xmss.Assembly.actK x) σ
  | .readK' x _, σ => CellNoBot (Xmss.Assembly.splitK' x) (Xmss.Assembly.actK' x) σ

/-- **The refined read-port bound** (alternative to `potential_hwReadKraus_le`): on a state with
no decompressed `⊥` at the read cell, a read port raises the event weight by at most
`readCost S c σ`. -/
theorem potential_hwReadKraus_le_refined [Nonempty X] [Nonempty Z] (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (c : HwRead X Z M)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : ReadNoBot c σ) :
    ∑' r, QuantumRuntime.potential (hwProjector S) (MatrixMap.conj (hwReadKraus c r) σ) ≤
      QuantumRuntime.potential (hwProjector S) σ + readCost S c σ := by
  cases c with
  | readH z upd => exact potential_cellRead_le (cellRead_readH z upd) (clsOff_readH z upd) S hσ hnb
  | readK x upd =>
    exact potential_cellRead_le (Xmss.Assembly.cellRead_readK x upd) (clsOff_readK x upd) S hσ
      hnb
  | readK' x upd =>
    exact potential_cellRead_le (Xmss.Assembly.cellRead_readK' x upd) (clsOff_readK' x upd) S hσ
      hnb

open scoped Classical in
/-- The refined cost, total: `⊤` off `ReadNoBot`. -/
noncomputable def readCostT (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if ReadNoBot c σ then readCost S c σ else ⊤

/-- **The refined read-port bound, for every state** (the drop-in form of
`potential_hwReadKraus_le`, with the cost `readCostT`). -/
theorem potential_hwReadKraus_le_refinedT [Nonempty X] [Nonempty Z] (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) (hσ : σ.PosSemidef) :
    ∑' r, QuantumRuntime.potential (hwProjector S) (MatrixMap.conj (hwReadKraus c r) σ) ≤
      QuantumRuntime.potential (hwProjector S) σ + readCostT S c σ := by
  unfold readCostT
  split_ifs with hnb
  · exact potential_hwReadKraus_le_refined S c hσ hnb
  · rw [add_top]
    exact le_top

/-! ### No decompressed `⊥` along the runs of runtime 2 -/

section bridge

variable [AddCommGroup X] [AddCommGroup Z]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M]
  [AddCommGroup X] [AddCommGroup Z] in
/-- The recorded values of a cell sum to zero against a recorded cell in the compression. -/
theorem sum_compressAll_update {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [Nonempty Y] (D E : Database A Y) (a : A) (hE : E a ≠ none) :
    ∑ y, compressAll A Y (Function.update D a (some y)) E = 0 := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hE
  have h : ∀ y, compressAll A Y (Function.update D a (some y)) E =
      cellCompress Y (some y) (some v) *
        ∏ x ∈ ({a}ᶜ : Finset A), cellCompress Y (D x) (E x) := fun y ↦ by
    rw [compressAll, piKron_apply, Fintype.prod_eq_mul_prod_compl a, Function.update_self, hv]
    congr 1
    exact Finset.prod_congr rfl fun x hx ↦ by rw [Function.update_of_ne (by simpa using hx)]
  simp only [h, ← Finset.sum_mul]
  refine mul_eq_zero_of_left ?_ _
  simp only [cellCompress_some_some, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), sub_self]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M]
  [AddCommGroup X] [AddCommGroup Z] in
theorem sum_mul_mul_eq_zero {ι : Type} [Fintype ι] (f : ι → ℂ) (B C : ℂ) (hf : ∑ i, f i = 0) :
    ∑ i, f i * B * C = 0 := by
  rw [← Finset.sum_mul, ← Finset.sum_mul, hf, zero_mul, zero_mul]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M]
  [AddCommGroup X] [AddCommGroup Z] in
theorem sum_mul_mid_eq_zero {ι : Type} [Fintype ι] (f : ι → ℂ) (A B C : ℂ)
    (hf : ∑ i, f i = 0) : ∑ i, A * (f i * B) * C = 0 := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, hf, zero_mul, mul_zero, zero_mul]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M]
  [AddCommGroup X] [AddCommGroup Z] in
theorem sum_mul_right_eq_zero {ι : Type} [Fintype ι] (f : ι → ℂ) (A B C : ℂ)
    (hf : ∑ i, f i = 0) : ∑ i, A * (B * f i) * C = 0 := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, hf, mul_zero, mul_zero, zero_mul]

omit [Fintype M] [AddCommGroup X] [AddCommGroup Z] in
theorem one_kron_compressReg_apply (q a : Unit × HwReg X Z M) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M) q a =
      compressAll Z X q.2.1.1 a.2.1.1 *
        (compressAll X Z q.2.1.2.1 a.2.1.2.1 * compressAll X Z q.2.1.2.2 a.2.1.2.2) *
        (1 : Matrix (Hw X Z × M) (Hw X Z × M) ℂ) q.2.2 a.2.2 := by
  obtain ⟨⟨⟩, q2⟩ := q
  obtain ⟨⟨⟩, a2⟩ := a
  rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, compressReg, kroneckerMap_apply,
    compressDbs, kroneckerMap_apply, kroneckerMap_apply]

/-- **No decompressed `⊥` at the read cell, from EndReads' invariant**: a state whose
decompressed form is supported on databases with no empty cell (`noBot_runtimeR`: every branch of
every run of runtime 2) satisfies `ReadNoBot` at every read port. -/
theorem readNoBot_of_noBot [Nonempty X] [Nonempty Z] (c : HwRead X Z M)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (h : QuerySupportedOn (fun m : Unit × HwReg X Z M ↦ m.2) {s | Xmss.Assembly.NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M) σ)) :
    ReadNoBot c σ := by
  have hU : ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M) *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M) = 1 := by
    rw [← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self, one_kronecker_one]
  have hUh : ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M)ᴴ =
      (1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M := by
    rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_compressReg]
  have hsupp : ∀ a b, (((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M) * σ *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M)) a b ≠ 0 →
      ((∀ z, (a.2.1.1 z).isSome) ∧ (∀ x, (a.2.1.2.1 x).isSome) ∧ ∀ x, (a.2.1.2.2 x).isSome) :=
    fun a b hab ↦ (h a b (by rwa [MatrixMap.conj_apply, hUh])).1
  cases c with
  | readH z upd =>
    refine cellNoBot_of_conj _ hU hsupp fun r _ a ha ↦ ?_
    have hq : ∀ y : X, (splitH' z).symm (some y, r) =
        ((), ((Function.update ((splitH' z).symm (none, r)).2.1.1 z (some y),
          ((splitH' z).symm (none, r)).2.1.2), ((splitH' z).symm (none, r)).2.2.1,
          ((splitH' z).symm (none, r)).2.2.2)) := fun y ↦ by
      have := splitH'_symm_tau z (fun m _ ↦ m) ((splitH' z).symm (none, r)) (some y) (some y)
      rwa [Equiv.apply_symm_apply] at this
    simp only [hq, one_kron_compressReg_apply]
    set q0 := (splitH' z).symm (none, r)
    exact sum_mul_mul_eq_zero
      (fun y ↦ compressAll Z X (Function.update q0.2.1.1 z (some y)) a.2.1.1)
      (compressAll X Z q0.2.1.2.1 a.2.1.2.1 * compressAll X Z q0.2.1.2.2 a.2.1.2.2)
      ((1 : Matrix (Hw X Z × M) (Hw X Z × M) ℂ) q0.2.2 a.2.2)
      (sum_compressAll_update _ _ _ (Option.ne_none_iff_isSome.mpr (ha.1 z)))
  | readK x upd =>
    refine cellNoBot_of_conj _ hU hsupp fun r _ a ha ↦ ?_
    have hq : ∀ y : Z, (Xmss.Assembly.splitK x).symm (some y, r) =
        ((), ((((Xmss.Assembly.splitK x).symm (none, r)).2.1.1,
          Function.update ((Xmss.Assembly.splitK x).symm (none, r)).2.1.2.1 x (some y),
          ((Xmss.Assembly.splitK x).symm (none, r)).2.1.2.2),
          ((Xmss.Assembly.splitK x).symm (none, r)).2.2.1,
          ((Xmss.Assembly.splitK x).symm (none, r)).2.2.2)) := fun y ↦ by
      have := Xmss.Assembly.splitK_symm_fill x ((Xmss.Assembly.splitK x).symm (none, r)) (some y)
      rwa [Equiv.apply_symm_apply] at this
    simp only [hq, one_kron_compressReg_apply]
    set q0 := (Xmss.Assembly.splitK x).symm (none, r)
    exact sum_mul_mid_eq_zero
      (fun y ↦ compressAll X Z (Function.update q0.2.1.2.1 x (some y)) a.2.1.2.1)
      (compressAll Z X q0.2.1.1 a.2.1.1) (compressAll X Z q0.2.1.2.2 a.2.1.2.2)
      ((1 : Matrix (Hw X Z × M) (Hw X Z × M) ℂ) q0.2.2 a.2.2)
      (sum_compressAll_update _ _ _ (Option.ne_none_iff_isSome.mpr (ha.2.1 x)))
  | readK' x upd =>
    refine cellNoBot_of_conj _ hU hsupp fun r _ a ha ↦ ?_
    have hq : ∀ y : Z, (Xmss.Assembly.splitK' x).symm (some y, r) =
        ((), ((((Xmss.Assembly.splitK' x).symm (none, r)).2.1.1,
          ((Xmss.Assembly.splitK' x).symm (none, r)).2.1.2.1,
          Function.update ((Xmss.Assembly.splitK' x).symm (none, r)).2.1.2.2 x (some y)),
          ((Xmss.Assembly.splitK' x).symm (none, r)).2.2.1,
          ((Xmss.Assembly.splitK' x).symm (none, r)).2.2.2)) := fun y ↦ by
      have := Xmss.Assembly.splitK'_symm_fill x ((Xmss.Assembly.splitK' x).symm (none, r))
        (some y)
      rwa [Equiv.apply_symm_apply] at this
    simp only [hq, one_kron_compressReg_apply]
    set q0 := (Xmss.Assembly.splitK' x).symm (none, r)
    exact sum_mul_right_eq_zero
      (fun y ↦ compressAll X Z (Function.update q0.2.1.2.2 x (some y)) a.2.1.2.2)
      (compressAll Z X q0.2.1.1 a.2.1.1) (compressAll X Z q0.2.1.2.1 a.2.1.2.1)
      ((1 : Matrix (Hw X Z × M) (Hw X Z × M) ℂ) q0.2.2 a.2.2)
      (sum_compressAll_update _ _ _ (Option.ne_none_iff_isSome.mpr (ha.2.2 x)))

end bridge

/-! ### The square-root form at the read ports -/

/-- The diagonal term `A` of a read port. -/
noncomputable def readA (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] :
    HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ
  | .readH z upd, σ => costA (splitH' z) (actH z) (tauH z upd) (liftSet S) (phiH z upd) σ
  | .readK x upd, σ => costA (Xmss.Assembly.splitK x) (Xmss.Assembly.actK x)
      (Xmss.Assembly.tauK x upd) (liftSet S) (phiK x upd) σ
  | .readK' x upd, σ => costA (Xmss.Assembly.splitK' x) (Xmss.Assembly.actK' x)
      (Xmss.Assembly.tauK x upd) (liftSet S) (phiK' x upd) σ

/-- The empty-to-recorded term `E` of a read port. -/
noncomputable def readE (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] :
    HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ
  | .readH z upd, σ => costE (splitH' z) (actH z) (tauH z upd) (liftSet S) σ
  | .readK x upd, σ => costE (Xmss.Assembly.splitK x) (Xmss.Assembly.actK x)
      (Xmss.Assembly.tauK x upd) (liftSet S) σ
  | .readK' x upd, σ => costE (Xmss.Assembly.splitK' x) (Xmss.Assembly.actK' x)
      (Xmss.Assembly.tauK x upd) (liftSet S) σ

/-- The moving mass `m` of a read port. -/
noncomputable def readM (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] :
    HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ
  | .readH z upd, σ => costM (splitH' z) (actH z) (tauH z upd) (liftSet S) σ
  | .readK x upd, σ => costM (Xmss.Assembly.splitK x) (Xmss.Assembly.actK x)
      (Xmss.Assembly.tauK x upd) (liftSet S) σ
  | .readK' x upd, σ => costM (Xmss.Assembly.splitK' x) (Xmss.Assembly.actK' x)
      (Xmss.Assembly.tauK x upd) (liftSet S) σ

/-- **The event is up-closed in the read cell**: recording any value in the empty read cell of a
state in the event keeps it in the event (as `Bad`, `BadR`: `upClosed_slice_bad`). -/
def UpCell (S : Set (HwReg X Z M)) : HwRead X Z M → Prop
  | .readH z _ => ∀ s : HwReg X Z M, s.1.1 z = none → s ∈ S → ∀ y,
      ((Function.update s.1.1 z (some y), s.1.2), s.2) ∈ S
  | .readK x _ => ∀ s : HwReg X Z M, s.1.2.1 x = none → s ∈ S → ∀ y,
      ((s.1.1, Function.update s.1.2.1 x (some y), s.1.2.2), s.2) ∈ S
  | .readK' x _ => ∀ s : HwReg X Z M, s.1.2.2 x = none → s ∈ S → ∀ y,
      ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some y)), s.2) ∈ S

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M] in
theorem mem_of_ind_eq_one {S : Set (HwReg X Z M)} [DecidablePred (· ∈ S)]
    {q : Unit × HwReg X Z M} (h : ind (liftSet S) q = 1) : q.2 ∈ S := by
  unfold ind at h
  split_ifs at h with hq
  · exact hq
  · norm_num at h

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M] in
theorem ind_eq_one_of_mem {S : Set (HwReg X Z M)} [DecidablePred (· ∈ S)]
    {q : Unit × HwReg X Z M} (h : q.2 ∈ S) : ind (liftSet S) q = 1 := by
  unfold ind
  rw [ite_eq_left ((mem_liftSet S q).2 h)]

/-- **The square-root form of the refined read cost** (for the graded event bound): for an event
up-closed in the read cell and a state with no decompressed `⊥` there, the event weight after a
read port is at most `(√w + √E)² + A + 2 √(E m)`, with `w` the weight before, `E = readE`,
`A = readA` and `m = readM` (the recorded cells whose read moves the memory across the event; `0`
for reads that keep the memory). -/
theorem potential_hwReadKraus_le_sqrt [Nonempty X] [Nonempty Z] (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (c : HwRead X Z M) (hup : UpCell S c)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : ReadNoBot c σ) :
    ∑' r, QuantumRuntime.potential (hwProjector S) (MatrixMap.conj (hwReadKraus c r) σ) ≤
      (QuantumRuntime.potential (hwProjector S) σ ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (readE S c σ) ^ (2⁻¹ : ℝ)) ^ 2 +
      (ENNReal.ofReal (readA S c σ) +
        2 * (ENNReal.ofReal (readE S c σ) * ENNReal.ofReal (readM S c σ)) ^ (2⁻¹ : ℝ)) := by
  cases c with
  | readH z upd =>
    refine potential_cellRead_le_sqrt (cellRead_readH z upd) (clsOff_readH z upd) S
      (fun r _ h0 y ↦ ?_) hσ hnb
    have hq := splitH'_symm_tau z (fun m _ ↦ m) ((splitH' z).symm (none, r)) (some y) (some y)
    rw [Equiv.apply_symm_apply] at hq
    have hc : ((splitH' z).symm (none, r)).2.1.1 z = none := by
      rw [← splitH'_apply_fst, Equiv.apply_symm_apply]
    change (splitH' z).symm (some y, r) = _ at hq
    rw [hq]
    exact ind_eq_one_of_mem (hup _ hc (mem_of_ind_eq_one h0) y)
  | readK x upd =>
    refine potential_cellRead_le_sqrt (Xmss.Assembly.cellRead_readK x upd) (clsOff_readK x upd) S
      (fun r _ h0 y ↦ ?_) hσ hnb
    have hq := Xmss.Assembly.splitK_symm_fill x ((Xmss.Assembly.splitK x).symm (none, r))
      (some y)
    rw [Equiv.apply_symm_apply] at hq
    have hc : ((Xmss.Assembly.splitK x).symm (none, r)).2.1.2.1 x = none := by
      change ((Xmss.Assembly.splitK x) ((Xmss.Assembly.splitK x).symm (none, r))).1 = none
      rw [Equiv.apply_symm_apply]
    rw [hq]
    exact ind_eq_one_of_mem (hup _ hc (mem_of_ind_eq_one h0) y)
  | readK' x upd =>
    refine potential_cellRead_le_sqrt (Xmss.Assembly.cellRead_readK' x upd) (clsOff_readK' x upd)
      S (fun r _ h0 y ↦ ?_) hσ hnb
    have hq := Xmss.Assembly.splitK'_symm_fill x ((Xmss.Assembly.splitK' x).symm (none, r))
      (some y)
    rw [Equiv.apply_symm_apply] at hq
    have hc : ((Xmss.Assembly.splitK' x).symm (none, r)).2.1.2.2 x = none := by
      change ((Xmss.Assembly.splitK' x) ((Xmss.Assembly.splitK' x).symm (none, r))).1 = none
      rw [Equiv.apply_symm_apply]
    rw [hq]
    exact ind_eq_one_of_mem (hup _ hc (mem_of_ind_eq_one h0) y)

/-! ### Reads that keep the memory, in FlipCost's terms -/

/-- The read keeps the memory (verification reads, reads of `k`, `k'` in the trials). -/
def KeepUpd : HwRead X Z M → Prop
  | .readH _ upd => ∀ m o, upd m o = m
  | .readK _ upd => ∀ m o, upd m o = m
  | .readK' _ upd => ∀ m o, upd m o = m

/-- The number of values whose recording in the read cell flips the event at `q`. -/
noncomputable def flipCnt (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] :
    HwRead X Z M → Unit × HwReg X Z M → ℕ
  | .readH z _, q => (Finset.univ.filter fun b : X ↦
      ¬ ((((Function.update q.2.1.1 z (some b), q.2.1.2), q.2.2) ∈ S) ↔ q.2 ∈ S)).card
  | .readK x _, q => (Finset.univ.filter fun b : Z ↦
      ¬ ((((q.2.1.1, Function.update q.2.1.2.1 x (some b), q.2.1.2.2), q.2.2) ∈ S) ↔ q.2 ∈ S)).card
  | .readK' x _, q => (Finset.univ.filter fun b : Z ↦
      ¬ ((((q.2.1.1, q.2.1.2.1, Function.update q.2.1.2.2 x (some b)), q.2.2) ∈ S) ↔
        q.2 ∈ S)).card

/-- **The empty-cell term of a read that keeps the memory**: on the states whose read cell is
neither hardwired nor recorded, the number of flipping values over the value count. -/
noncomputable def keepE (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] :
    HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ
  | .readH z upd, σ => ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z = none then
      (flipCnt S (.readH z upd) q : ℝ) / Fintype.card X else 0) * (σ q q).re
  | .readK x upd, σ => ∑ q, (if q.2.2.1.2.1 x = none ∧ q.2.1.2.1 x = none then
      (flipCnt S (.readK x upd) q : ℝ) / Fintype.card Z else 0) * (σ q q).re
  | .readK' x upd, σ => ∑ q, (if q.2.2.1.2.2 x = none ∧ q.2.1.2.2 x = none then
      (flipCnt S (.readK' x upd) q : ℝ) / Fintype.card Z else 0) * (σ q q).re

/-- **The recorded-cell term**: `2/|Y|` times the weight of the states whose read cell is recorded
and not hardwired. -/
noncomputable def recW : HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ
  | .readH z _, σ => ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none then
      (2 : ℝ) / Fintype.card X else 0) * (σ q q).re
  | .readK x _, σ => ∑ q, (if q.2.2.1.2.1 x = none ∧ q.2.1.2.1 x ≠ none then
      (2 : ℝ) / Fintype.card Z else 0) * (σ q q).re
  | .readK' x _, σ => ∑ q, (if q.2.2.1.2.2 x = none ∧ q.2.1.2.2 x ≠ none then
      (2 : ℝ) / Fintype.card Z else 0) * (σ q q).re

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M] in
theorem ind_ne_iff {S : Set (HwReg X Z M)} [DecidablePred (· ∈ S)] (a b : Unit × HwReg X Z M) :
    ind (liftSet S) a ≠ ind (liftSet S) b ↔ ¬ (a.2 ∈ S ↔ b.2 ∈ S) := by
  unfold ind
  by_cases ha : a.2 ∈ S <;> by_cases hb : b.2 ∈ S <;>
    simp [ha, hb, mem_liftSet]

omit [Fintype M] [DecidableEq M] in
theorem cntK_readH (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (upd : M → Option X → M) (q : Unit × HwReg X Z M) :
    cntK (splitH' z) (liftSet S) q = flipCnt S (.readH z upd) q := by
  unfold cntK flipCnt
  congr 1
  refine Finset.filter_congr fun b _ ↦ ?_
  have h := splitH'_symm_tau z (fun m _ ↦ m) q (some b) (some b)
  change (splitH' z).symm (some b, (splitH' z q).2) = _ at h
  rw [h, ind_ne_iff]

omit [Fintype M] [DecidableEq M] in
theorem cntK_readK (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (x : X)
    (upd : M → Option Z → M) (q : Unit × HwReg X Z M) :
    cntK (Xmss.Assembly.splitK x) (liftSet S) q = flipCnt S (.readK x upd) q := by
  unfold cntK flipCnt
  congr 1
  refine Finset.filter_congr fun b _ ↦ ?_
  rw [Xmss.Assembly.splitK_symm_fill, ind_ne_iff]

omit [Fintype M] [DecidableEq M] in
theorem cntK_readK' (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (x : X)
    (upd : M → Option Z → M) (q : Unit × HwReg X Z M) :
    cntK (Xmss.Assembly.splitK' x) (liftSet S) q = flipCnt S (.readK' x upd) q := by
  unfold cntK flipCnt
  congr 1
  refine Finset.filter_congr fun b _ ↦ ?_
  rw [Xmss.Assembly.splitK'_symm_fill, ind_ne_iff]

omit [DecidableEq M] in
/-- **The terms of a read that keeps the memory**: `E ≤ keepE`, `A ≤ keepE + recW`, `m = 0`. -/
theorem read_keep_le [Nonempty X] [Nonempty Z] (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (c : HwRead X Z M) (hk : KeepUpd c)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    readE S c σ ≤ keepE S c σ ∧ readA S c σ ≤ keepE S c σ + recW c σ ∧ readM S c σ = 0 := by
  cases c with
  | readH z upd =>
    have hk' : ∀ m o, upd m o = m := hk
    have hτ : ∀ (y : X) r, tauH z upd (some y) r = r := fun y r ↦ by simp [tauH, hk']
    have hφ : ∀ q : Unit × HwReg X Z M, ¬ actH z (splitH' z q).2 → phiH z upd q = q :=
      fun q _ ↦ by
        obtain ⟨⟨⟩, D, W, m⟩ := q
        simp [phiH, hk']
    refine ⟨(costE_keep_le (liftSet S) hτ hσ).trans_eq ?_,
      (costA_keep_le (liftSet S) hτ hφ hσ).trans_eq ?_, costM_keep (liftSet S) hτ σ⟩
    · exact Finset.sum_congr rfl fun q _ ↦ by rw [cntK_readH S z upd]; rfl
    · simp only [keepE, recW, add_mul, Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun q _ ↦ by rw [cntK_readH S z upd]; rfl
  | readK x upd =>
    have hk' : ∀ m o, upd m o = m := hk
    have hτ : ∀ (y : Z) r, Xmss.Assembly.tauK x upd (some y) r = r := fun y r ↦ by
      simp [Xmss.Assembly.tauK, hk']
    have hφ : ∀ q : Unit × HwReg X Z M, ¬ Xmss.Assembly.actK x (Xmss.Assembly.splitK x q).2 →
        phiK x upd q = q := fun q _ ↦ by
      obtain ⟨⟨⟩, D, W, m⟩ := q
      simp [phiK, hk']
    refine ⟨(costE_keep_le (liftSet S) hτ hσ).trans_eq ?_,
      (costA_keep_le (liftSet S) hτ hφ hσ).trans_eq ?_, costM_keep (liftSet S) hτ σ⟩
    · exact Finset.sum_congr rfl fun q _ ↦ by rw [cntK_readK S x upd]; rfl
    · simp only [keepE, recW, add_mul, Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun q _ ↦ by rw [cntK_readK S x upd]; rfl
  | readK' x upd =>
    have hk' : ∀ m o, upd m o = m := hk
    have hτ : ∀ (y : Z) r, Xmss.Assembly.tauK x upd (some y) r = r := fun y r ↦ by
      simp [Xmss.Assembly.tauK, hk']
    have hφ : ∀ q : Unit × HwReg X Z M, ¬ Xmss.Assembly.actK' x (Xmss.Assembly.splitK' x q).2 →
        phiK' x upd q = q := fun q _ ↦ by
      obtain ⟨⟨⟩, D, W, m⟩ := q
      simp [phiK', hk']
    refine ⟨(costE_keep_le (liftSet S) hτ hσ).trans_eq ?_,
      (costA_keep_le (liftSet S) hτ hφ hσ).trans_eq ?_, costM_keep (liftSet S) hτ σ⟩
    · exact Finset.sum_congr rfl fun q _ ↦ by rw [cntK_readK' S x upd]; rfl
    · simp only [keepE, recW, add_mul, Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun q _ ↦ by rw [cntK_readK' S x upd]; rfl

/-- **A read that keeps the memory costs like a sponge call** (the square-root form): for an
event up-closed in the read cell and a state with no decompressed `⊥` there, the event weight
after the read is at most `(√w + √E)² + E + R`, with `E = keepE` (the flipping values over the
value count, on the empty cells) and `R = recW` (`2/|Y|` times the recorded mass); hardwired
cells cost nothing. -/
theorem potential_readKeep_le_sqrt [Nonempty X] [Nonempty Z] (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (c : HwRead X Z M) (hk : KeepUpd c) (hup : UpCell S c)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : ReadNoBot c σ) :
    ∑' r, QuantumRuntime.potential (hwProjector S) (MatrixMap.conj (hwReadKraus c r) σ) ≤
      (QuantumRuntime.potential (hwProjector S) σ ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (keepE S c σ) ^ (2⁻¹ : ℝ)) ^ 2 +
      ENNReal.ofReal (keepE S c σ + recW c σ) := by
  obtain ⟨hE, hA, hM⟩ := read_keep_le S c hk hσ
  refine (potential_hwReadKraus_le_sqrt S c hup hσ hnb).trans (add_le_add
    (pow_le_pow_left₀ zero_le (add_le_add le_rfl
      (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hE) (by norm_num))) 2) ?_)
  rw [hM, ENNReal.ofReal_zero, mul_zero, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero,
    add_zero]
  exact ENNReal.ofReal_le_ofReal hA

/-! ### Reads of `h` that update the memory, in FlipCost's terms -/

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M] in
theorem ind_sub_ind_le {S : Set (HwReg X Z M)} [DecidablePred (· ∈ S)]
    (a b : Unit × HwReg X Z M) :
    ind (liftSet S) a - ind (liftSet S) b ≤ if b.2 ∉ S ∧ a.2 ∈ S then 1 else 0 := by
  unfold ind
  by_cases ha : a.2 ∈ S <;> by_cases hb : b.2 ∈ S <;> simp [ha, hb, mem_liftSet]

/-- The values `v` that can flip the event when read at the empty cell `z` of `q`: recording
`v` flips it, or the memory update with `v` changes it for some content `u` of the cell. -/
def hFlip (S : Set (HwReg X Z M)) (z : Z) (upd : M → Option X → M) (q : Unit × HwReg X Z M)
    (v : X) : Prop :=
  ¬ ((((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2) ∈ S) ↔ q.2 ∈ S) ∨
    ∃ u : Option X, ¬ ((((Function.update q.2.1.1 z u, q.2.1.2), q.2.2.1, upd q.2.2.2 (some v)) ∈
      S) ↔ (((Function.update q.2.1.1 z u, q.2.1.2), q.2.2) ∈ S))

/-- The values `v` whose read at the empty cell `z` of `q` (with the memory update) leaves the
event for some content of the cell: the count of `flipCost_readH_le`. -/
def hChg (S : Set (HwReg X Z M)) (z : Z) (upd : M → Option X → M) (q : Unit × HwReg X Z M)
    (v : X) : Prop :=
  ∃ u : Option X, ¬ ((((Function.update q.2.1.1 z u, q.2.1.2), q.2.2.1, upd q.2.2.2 (some v)) ∈
    S) ↔ q.2 ∈ S)

/-- The read of the recorded value of cell `z` moves the memory across the event for some content
of the cell. -/
def hMove (S : Set (HwReg X Z M)) (z : Z) (upd : M → Option X → M) (q : Unit × HwReg X Z M) :
    Prop :=
  ∃ u : Option X, ¬ ((((Function.update q.2.1.1 z u, q.2.1.2), q.2.2.1, upd q.2.2.2 (q.2.1.1 z)) ∈
    S) ↔ (((Function.update q.2.1.1 z u, q.2.1.2), q.2.2) ∈ S))

/-- The classical move with the read value `o` puts `q` into the event. -/
def hCls (S : Set (HwReg X Z M)) (upd : M → Option X → M) (o : Option X)
    (q : Unit × HwReg X Z M) : Prop :=
  q.2 ∉ S ∧ (q.2.1, q.2.2.1, upd q.2.2.2 o) ∈ S

/-- `hFlip`, decided. -/
instance hFlipDec (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (upd : M → Option X → M) (q : Unit × HwReg X Z M) : DecidablePred (hFlip S z upd q) :=
  fun _ ↦ by unfold hFlip; infer_instance

/-- `hChg`, decided. -/
instance hChgDec (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (upd : M → Option X → M) (q : Unit × HwReg X Z M) : DecidablePred (hChg S z upd q) :=
  fun _ ↦ by unfold hChg; infer_instance

/-- `hMove`, decided. -/
instance hMoveDec (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (upd : M → Option X → M) (q : Unit × HwReg X Z M) : Decidable (hMove S z upd q) := by
  unfold hMove
  infer_instance

/-- `hCls`, decided. -/
instance hClsDec (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (upd : M → Option X → M)
    (o : Option X) (q : Unit × HwReg X Z M) : Decidable (hCls S upd o q) := by
  unfold hCls
  infer_instance

omit [DecidableEq M] in
/-- **The terms of a read of `h`, in FlipCost's terms.** With `N = |X|`: `E` is at most the
number of flipping values over `N` on the empty cells; `A` is at most `hChg` over `N` on the
empty cells, `2/N` plus the classical move with the recorded value on the recorded cells, and the
classical move with the hardwired value on the hardwired cells; `m` is at most the recorded mass
whose read moves the memory across the event. -/
theorem read_readH_le [Nonempty X] (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (upd : M → Option X → M) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) :
    readE S (.readH z upd) σ ≤ ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z = none then
        ((Finset.univ.filter (hFlip S z upd q)).card : ℝ) / Fintype.card X else 0) *
        (σ q q).re ∧
      readA S (.readH z upd) σ ≤ ∑ q, (if q.2.2.1.1 z = none then
        (if q.2.1.1 z = none then
          ((Finset.univ.filter (hChg S z upd q)).card : ℝ) / Fintype.card X else
          2 / Fintype.card X + if hCls S upd (q.2.1.1 z) q then 1 else 0) else
        if hCls S upd (q.2.2.1.1 z) q then 1 else 0) * (σ q q).re ∧
      readM S (.readH z upd) σ ≤ ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧
        hMove S z upd q then 1 else 0) * (σ q q).re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hsym := splitH'_symm_tau (M := M) z upd
  have hsym0 : ∀ (q : Unit × HwReg X Z M) (a : Option X), (splitH' z).symm (a, (splitH' z q).2) =
      ((), ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2.1, q.2.2.2)) := fun q a ↦
    splitH'_symm_tau z (fun m _ ↦ m) q a a
  refine ⟨?_, ?_, ?_⟩
  · unfold readE costE
    refine (Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right
      (ew_kap_le (liftSet S) q) (hre q)).trans
      (Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right ?_ (hre q))
    by_cases hq : q.2.2.1.1 z = none ∧ q.2.1.1 z = none
    · rw [ite_eq_left (show actH z (splitH' z q).2 ∧ (splitH' z q).1 = none from hq),
        ite_eq_left hq]
      refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card fun v hv ↦ ?_))
        (Nat.cast_nonneg _)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      have h0 : q0 (splitH' z) (liftSet S) (splitH' z q).2 = ind (liftSet S) q := by
        rw [q0, splitH'_symm_none z q hq.2]
      unfold Flip Moves at hv
      unfold hFlip
      rcases hv with hv | ⟨a, ha⟩
      · rw [h0, hsym0, ind_ne_iff] at hv
        exact Or.inl hv
      · rw [hsym, hsym0, ind_ne_iff] at ha
        exact Or.inr ⟨a, ha⟩
    · rw [ite_eq_right (show ¬ (actH z (splitH' z q).2 ∧ (splitH' z q).1 = none) from hq),
        ite_eq_right hq]
  · unfold readA costA
    refine Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right ?_ (hre q)
    by_cases ha : q.2.2.1.1 z = none
    · rw [ite_eq_left ha]
      have ha' : actH z (splitH' z q).2 := ha
      rcases h1 : q.2.1.1 z with _ | y
      · rw [ite_eq_left rfl]
        refine (fd_none_le (liftSet S) ha' h1).trans
          (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
        refine (chw_le_card (liftSet S) _).trans
          (Nat.cast_le.mpr (Finset.card_le_card fun v hv ↦ ?_))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        obtain ⟨a, hav⟩ := hv
        have h0 : q0 (splitH' z) (liftSet S) (splitH' z q).2 = ind (liftSet S) q := by
          rw [q0, splitH'_symm_none z q h1]
        rw [hsym, h0, ind_ne_iff] at hav
        exact ⟨a, hav⟩
      · rw [ite_eq_right (Option.some_ne_none y)]
        refine (fd_some_le (liftSet S) (τ := tauH z upd) (φ := phiH z upd) ha' h1).trans ?_
        rw [hsym]
        have hup : Function.update q.2.1.1 z (some y) = q.2.1.1 := by
          rw [← h1, Function.update_eq_self]
        rw [hup, add_comm]
        exact add_le_add le_rfl (ind_sub_ind_le _ q)
    · rw [ite_eq_right ha, fd_off (liftSet S) (show ¬ actH z (splitH' z q).2 from ha)]
      exact ind_sub_ind_le _ q
  · unfold readM costM
    refine Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right ?_ (hre q)
    unfold pd
    by_cases ha : q.2.2.1.1 z = none
    · rw [ite_eq_left (show actH z (splitH' z q).2 from ha)]
      have h1' : q.2.1.1 z = (splitH' z q).1 := rfl
      rw [h1']
      rcases h1 : (splitH' z q).1 with _ | y
      · simp
      · simp only [Option.elim_some]
        by_cases hm : Moves (splitH' z) (tauH z upd) (liftSet S) y (splitH' z q).2
        · rw [ite_eq_left hm]
          obtain ⟨a, hav⟩ := hm
          rw [hsym, hsym0, ind_ne_iff] at hav
          have hmv : hMove S z upd q := ⟨a, by rw [h1', h1]; exact hav⟩
          rw [ite_eq_left ⟨ha, Option.some_ne_none y, hmv⟩]
        · rw [ite_eq_right hm]
          split_ifs <;> norm_num
    · rw [ite_eq_right (show ¬ actH z (splitH' z q).2 from ha), ite_eq_right fun h' ↦ ha h'.1]

end ports

end Quantum.Sponge

end
