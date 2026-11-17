module

public import Quantum.Qrom.TableLaw

@[expose] public section

/-!
# The lazy table law on a good set of tables

`Quantum.Qrom.TableLaw` needs the cells of every table to be pairwise distinct. With several users
two tables may share a cell (two users drawing the same public parameter), so here injectivity is
asked only on a good set: `LazyTableOn` has the fields of `LazyTable` and a predicate `good` with
`inj : ∀ v, good v → Injective (cell · v)`. The table `tab H` is still defined for every `H`.

* `tableEquivOn`: the single-user bijection `(v, H) ↦ (fill v v H, H ∘ cell · v)` restricted to
  `{v // good v} × (D → Y) ≃ {H // good (tab H)} × (Pos → Y)`; it uses injectivity only at the
  table it acts on.
* `card_good_mul`: `#{v | good v} · |D → Y| = #{H | good (tab H)} · |Pos → Y|`, and
  `prob_not_good_tab`: the bad fraction of functions (by their table) is the bad fraction of tables.
* **The law on the good set** (`tableAvg_good`): averaging over uniform `H` the run observed through
  `tab H`, restricted to good tables, is averaging over uniform good values `v` the lifted run
  against runtime 1 with the cells of `v` hardwired. `qromEvalDistMap_apply_le_tableAvg_good`: the
  QROM law of any event is at most the bad fraction of tables plus that average.
-/

open MeasureTheory
open scoped ENNReal

universe u v w

namespace Quantum.Qrom

open Quantum Quantum.Sponge

/-- **A lazy table with injective cells on a good set**: as `LazyTable`, with distinct cells
required only for good values. -/
structure LazyTableOn (Pos D Y : Type) where
  /-- The input hashed at position `s`, given the values `v`. -/
  cell : Pos → (Pos → Y) → D
  /-- `pre s' s`: position `s'` precedes `s`. -/
  pre : Pos → Pos → Prop
  wf : WellFounded pre
  /-- The cell of `s` reads only the values at the predecessors of `s`. -/
  dep : ∀ s v v', (∀ s', pre s' s → v s' = v' s') → cell s v = cell s v'
  /-- The good tables. -/
  good : (Pos → Y) → Prop
  /-- On a good table, distinct positions hash distinct inputs. -/
  inj : ∀ v, good v → Function.Injective fun s ↦ cell s v

namespace LazyTableOn

section table

variable {Pos D Y : Type} (T : LazyTableOn Pos D Y)

/-- The cells of `v`, holding the values `w`: cell `cell s v` holds `w s` (a chosen `s`). -/
noncomputable def tableDb (v w : Pos → Y) : Database D Y := fun z ↦
  @dite _ (∃ s, T.cell s v = z) (Classical.propDecidable _) (fun h ↦ some (w h.choose))
    fun _ ↦ none

theorem tableDb_cell {v : Pos → Y} (hv : T.good v) (w : Pos → Y) (s : Pos) :
    T.tableDb v w (T.cell s v) = some (w s) := by
  have h : ∃ s', T.cell s' v = T.cell s v := ⟨s, rfl⟩
  unfold tableDb
  rw [dite_eq_left h, T.inj v hv h.choose_spec]

theorem tableDb_of_forall_ne {v w : Pos → Y} {z : D} (hz : ∀ s, T.cell s v ≠ z) :
    T.tableDb v w z = none := by
  unfold tableDb
  rw [dite_eq_right]
  rintro ⟨s, hs⟩
  exact hz s hs

/-- Values read off a function at the cells are recovered at every cell, injective or not. -/
theorem tableDb_restore (v : Pos → Y) (H : D → Y) (s : Pos) :
    T.tableDb v (fun s ↦ H (T.cell s v)) (T.cell s v) = some (H (T.cell s v)) := by
  have h : ∃ s', T.cell s' v = T.cell s v := ⟨s, rfl⟩
  unfold tableDb
  rw [dite_eq_left h]
  exact congrArg (fun z ↦ some (H z)) h.choose_spec

/-- `H` with the cells of `v` overwritten by the values `w`. -/
noncomputable def fill (v w : Pos → Y) (H : D → Y) : D → Y :=
  fun z ↦ (T.tableDb v w z).getD (H z)

theorem fill_cell {v : Pos → Y} (hv : T.good v) (w : Pos → Y) (H : D → Y) (s : Pos) :
    T.fill v w H (T.cell s v) = w s := by
  unfold fill
  rw [T.tableDb_cell hv]
  rfl

theorem fill_of_forall_ne {v w : Pos → Y} {H : D → Y} {z : D} (hz : ∀ s, T.cell s v ≠ z) :
    T.fill v w H z = H z := by
  unfold fill
  rw [T.tableDb_of_forall_ne hz]
  rfl

/-- Overwriting twice at the same cells keeps the last values. -/
theorem fill_fill (v w w' : Pos → Y) (H : D → Y) :
    T.fill v w (T.fill v w' H) = T.fill v w H := by
  funext z
  by_cases hz : ∃ s, T.cell s v = z
  · unfold fill tableDb
    rw [dite_eq_left hz, dite_eq_left hz]
    rfl
  · push Not at hz
    rw [T.fill_of_forall_ne hz, T.fill_of_forall_ne hz, T.fill_of_forall_ne hz]

/-- Overwriting the cells by the values they hold changes nothing. -/
theorem fill_of_cell {v w : Pos → Y} {H : D → Y} (hH : ∀ s, H (T.cell s v) = w s) :
    T.fill v w H = H := by
  funext z
  by_cases hz : ∃ s, T.cell s v = z
  · unfold fill tableDb
    rw [dite_eq_left hz, ← hH, hz.choose_spec]
    rfl
  · push Not at hz
    rw [T.fill_of_forall_ne hz]

/-- Restoring the overwritten values gives back the function. -/
theorem fill_restore (v w : Pos → Y) (H : D → Y) :
    T.fill v (fun s ↦ H (T.cell s v)) (T.fill v w H) = H := by
  funext z
  by_cases hz : ∃ s, T.cell s v = z
  · obtain ⟨s, rfl⟩ := hz
    unfold fill
    rw [T.tableDb_restore]
    rfl
  · push Not at hz
    rw [T.fill_of_forall_ne hz, T.fill_of_forall_ne hz]

variable [Zero Y]

/-- **The table of `H`**: the honest values `v s = H (cell s v)`, by well-founded recursion. -/
noncomputable def tab (H : D → Y) : Pos → Y :=
  T.wf.fix fun s ih ↦ H (T.cell s fun s' ↦
    @dite _ (T.pre s' s) (Classical.propDecidable _) (fun h ↦ ih s' h) fun _ ↦ 0)

theorem tab_eq (H : D → Y) (s : Pos) : T.tab H s = H (T.cell s (T.tab H)) :=
  (WellFounded.fix_eq T.wf _ s).trans
    (congrArg H (T.dep s _ _ fun _ hs' ↦ dite_eq_left hs'))

/-- **The table is the only consistent assignment.** -/
theorem tab_unique {H : D → Y} {v : Pos → Y} (hv : ∀ s, H (T.cell s v) = v s) : T.tab H = v :=
  funext fun s ↦ T.wf.induction (C := fun s ↦ T.tab H s = v s) s fun s ih ↦ by
    rw [tab_eq, ← hv s]
    exact congrArg H (T.dep s _ _ ih)

theorem tab_eq_iff {H : D → Y} {v : Pos → Y} : T.tab H = v ↔ ∀ s, H (T.cell s v) = v s :=
  ⟨fun h s ↦ h ▸ (T.tab_eq H s).symm, T.tab_unique⟩

theorem tab_fill_of_inj {v : Pos → Y} (hv : T.good v) (H : D → Y) : T.tab (T.fill v v H) = v :=
  T.tab_unique (T.fill_cell hv v H)

/-- **Overwriting the cells of a good `v` and reading them**, a bijection
`{v // good v} × (D → Y) ≃ {H // good (tab H)} × (Pos → Y)`, with inverse
`(H', u) ↦ (tab H', fill (tab H') u H')`. -/
noncomputable def tableEquivOn :
    {v : Pos → Y // T.good v} × (D → Y) ≃ {H : D → Y // T.good (T.tab H)} × (Pos → Y) where
  toFun p := (⟨T.fill p.1.1 p.1.1 p.2, (T.tab_fill_of_inj p.1.2 p.2).symm ▸ p.1.2⟩,
    fun s ↦ p.2 (T.cell s p.1.1))
  invFun q := (⟨T.tab q.1.1, q.1.2⟩, T.fill (T.tab q.1.1) q.2 q.1.1)
  left_inv p := by
    obtain ⟨⟨v, hv⟩, H⟩ := p
    refine Prod.ext (Subtype.ext (T.tab_fill_of_inj hv H)) ?_
    change T.fill (T.tab (T.fill v v H)) (fun s ↦ H (T.cell s v)) (T.fill v v H) = H
    rw [T.tab_fill_of_inj hv]
    exact T.fill_restore v v H
  right_inv q := by
    obtain ⟨⟨H, hH⟩, u⟩ := q
    refine Prod.ext (Subtype.ext ?_) (funext fun s ↦ T.fill_cell hH u H s)
    change T.fill (T.tab H) (T.tab H) (T.fill (T.tab H) u H) = H
    rw [fill_fill]
    exact T.fill_of_cell fun s ↦ (T.tab_eq H s).symm

variable [Fintype Pos] [DecidableEq Pos] [Fintype D] [DecidableEq D] [Fintype Y]
  [DecidablePred T.good]

/-- A sum restricted to a predicate is the sum over its subtype. -/
theorem sum_ite_eq_sum_subtype {α β : Type*} [Fintype α] [AddCommMonoid β] (p : α → Prop)
    [DecidablePred p] (f : α → β) :
    ∑ a, (if p a then f a else 0) = ∑ a : {a // p a}, f a := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun a ↦ by simp) f

/-- **Summing over good values and functions the overwritten functions** counts every function
with a good table `|Y|^|Pos|` times, with its table as values. -/
theorem sum_sum_fill_good {β : Type*} [AddCommMonoid β] (F : (Pos → Y) → (D → Y) → β) :
    ∑ v, (if T.good v then ∑ H, F v (T.fill v v H) else 0) =
      Fintype.card (Pos → Y) • ∑ H, (if T.good (T.tab H) then F (T.tab H) H else 0) := by
  rw [sum_ite_eq_sum_subtype, sum_ite_eq_sum_subtype (fun H ↦ T.good (T.tab H))]
  calc ∑ v : {v // T.good v}, ∑ H, F v.1 (T.fill v.1 v.1 H)
      = ∑ p : {v // T.good v} × (D → Y),
          (fun q : {H // T.good (T.tab H)} × (Pos → Y) ↦ F (T.tab q.1.1) q.1.1)
            (T.tableEquivOn p) := by
        rw [← Fintype.sum_prod_type']
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        change F p.1.1 (T.fill p.1.1 p.1.1 p.2) =
          F (T.tab (T.fill p.1.1 p.1.1 p.2)) (T.fill p.1.1 p.1.1 p.2)
        rw [T.tab_fill_of_inj p.1.2]
    _ = ∑ q : {H // T.good (T.tab H)} × (Pos → Y), F (T.tab q.1.1) q.1.1 :=
        T.tableEquivOn.sum_comp fun q ↦ F (T.tab q.1.1) q.1.1
    _ = Fintype.card (Pos → Y) • ∑ H : {H // T.good (T.tab H)}, F (T.tab H.1) H.1 := by
        rw [Fintype.sum_prod_type, Finset.smul_sum]
        refine Finset.sum_congr rfl fun H _ ↦ ?_
        change ∑ _u : Pos → Y, F (T.tab H.1) H.1 = _
        rw [Finset.sum_const, Finset.card_univ]

/-- **Counting good tables**: `#{v | good v} · |D → Y| = #{H | good (tab H)} · |Pos → Y|`. -/
theorem card_good_mul :
    (Finset.univ.filter T.good).card * Fintype.card (D → Y) =
      (Finset.univ.filter fun H ↦ T.good (T.tab H)).card * Fintype.card (Pos → Y) := by
  have h := T.sum_sum_fill_good (β := ℕ) fun _ _ ↦ 1
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  rw [Finset.card_filter, Finset.card_filter]
  calc (∑ v, if T.good v then 1 else 0) * Fintype.card (D → Y)
      = ∑ v, (if T.good v then Fintype.card (D → Y) else 0) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun v _ ↦ by split_ifs <;> simp
    _ = Fintype.card (Pos → Y) * ∑ H, (if T.good (T.tab H) then 1 else 0) := h
    _ = _ := mul_comm _ _

/-- **The bad fraction of functions, by their table, is the bad fraction of tables.** -/
theorem prob_not_good_tab :
    (Fintype.card (D → Y) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun H ↦ ¬T.good (T.tab H)).card =
      (Fintype.card (Pos → Y) : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun v ↦ ¬T.good v).card := by
  have hc := T.card_good_mul
  have hg := Finset.card_filter_add_card_filter_not (s := Finset.univ) T.good
  have hh := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    fun H : D → Y ↦ T.good (T.tab H)
  have ha0 : Fintype.card (Pos → Y) ≠ 0 := Fintype.card_ne_zero
  have hb0 : Fintype.card (D → Y) ≠ 0 := Fintype.card_ne_zero
  rw [Finset.card_univ] at hg hh
  generalize (Finset.univ.filter T.good).card = g at hc hg
  generalize (Finset.univ.filter fun H ↦ T.good (T.tab H)).card = h at hc hh
  generalize (Finset.univ.filter fun v ↦ ¬T.good v).card = x at hg ⊢
  generalize (Finset.univ.filter fun H ↦ ¬T.good (T.tab H)).card = y at hh ⊢
  generalize Fintype.card (Pos → Y) = a at hc hg ha0 ⊢
  generalize Fintype.card (D → Y) = b at hc hh hb0 ⊢
  have key : a * y = b * x := by
    rw [show x = a - g by omega, show y = b - h by omega, Nat.mul_sub, Nat.mul_sub,
      mul_comm a h, ← hc, mul_comm b g, mul_comm a b]
  rw [← ENNReal.div_eq_inv_mul, ← ENNReal.div_eq_inv_mul,
    ENNReal.div_eq_div_iff (Nat.cast_ne_zero.mpr ha0) (ENNReal.natCast_ne_top _)
      (Nat.cast_ne_zero.mpr hb0) (ENNReal.natCast_ne_top _)]
  exact_mod_cast key

end table

/-- The hardwired cells of the values `v`: the cells of `v`, holding `v`. -/
noncomputable def hwOf {Pos D Y : Type} (T : LazyTableOn Pos D Y) (v : Pos → Y) : Hw Y D :=
  hwCells (T.tableDb v v)

end LazyTableOn

variable {Pos D Y : Type} [Fintype Pos] [DecidableEq Pos] [Fintype D] [DecidableEq D]
  [Fintype Y] [DecidableEq Y] [AddCommGroup D] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **The lazy table law on the good set.** Averaging over uniform `H` the run observed through
`tab H`, restricted to functions with a good table, is averaging over uniform good values `v` the
lifted run against runtime 1 started with the cells of `v` hardwired to `v`. -/
theorem tableAvg_good (T : LazyTableOn Pos D Y) [DecidablePred T.good] {M : Type} [Fintype M]
    [DecidableEq M] (m₀ : M) {β : Type*} [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp L (qromSpec D Y) W A) (ρ : SubState A)
    (g : (Pos → Y) → (Σ u, W u) → β) :
    ∑ H : D → Y, (Fintype.card (D → Y) : ℝ≥0∞)⁻¹ •
        (if T.good (T.tab H) then (additiveOracleRuntime H).evalDistMap I x ρ (g (T.tab H))
          else 0) =
      ∑ v : Pos → Y, (Fintype.card (Pos → Y) : ℝ≥0∞)⁻¹ •
        (if T.good v then
          (spongeHardwiredReadRuntime Y D (T.hwOf v) m₀).evalDistMap I (liftH x).liftOrdinary ρ
            (g v)
          else 0) := by
  have hrun : ∀ v : Pos → Y,
      (spongeHardwiredReadRuntime Y D (T.hwOf v) m₀).evalDistMap I (liftH x).liftOrdinary ρ
          (g v) =
        (Fintype.card (D → Y) : ℝ≥0∞)⁻¹ • ∑ H : D → Y,
          (additiveOracleRuntime (T.fill v v H)).evalDistMap I x ρ (g v) :=
    fun v ↦ evalDistMap_hardwired_liftH (T.hwOf v) m₀ I x ρ (g v)
  have key := T.sum_sum_fill_good fun v H ↦ (additiveOracleRuntime H).evalDistMap I x ρ (g v)
  have hP : (Fintype.card (Pos → Y) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hite : ∀ v : Pos → Y, (if T.good v then
      (spongeHardwiredReadRuntime Y D (T.hwOf v) m₀).evalDistMap I (liftH x).liftOrdinary ρ (g v)
      else 0) = (Fintype.card (D → Y) : ℝ≥0∞)⁻¹ • (if T.good v then ∑ H : D → Y,
          (additiveOracleRuntime (T.fill v v H)).evalDistMap I x ρ (g v) else 0) := fun v ↦ by
    split_ifs
    · exact hrun v
    · rw [smul_zero]
  simp only [hite, smul_smul, ← Finset.smul_sum]
  rw [key, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul, mul_right_comm,
    ENNReal.inv_mul_cancel hP (ENNReal.natCast_ne_top _), one_mul]

/-- **The QROM law of an event, split by good tables**: at most the bad fraction of tables plus
the average over good values of runtime 1 with the cells hardwired. -/
theorem qromEvalDistMap_apply_le_tableAvg_good (T : LazyTableOn Pos D Y) [DecidablePred T.good]
    {M : Type} [Fintype M] [DecidableEq M] (m₀ : M) {β : Type*} [MeasurableSpace β]
    (I : L.Interp) (x : QuantumComp L (qromSpec D Y) W A) (ρ : SubState A)
    (g : (Pos → Y) → (Σ u, W u) → β) (s : Set β) :
    qromEvalDistMap I x ρ (fun H ↦ g (T.tab H)) s ≤
      (Fintype.card (Pos → Y) : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun v ↦ ¬T.good v).card +
        ∑ v : Pos → Y, (Fintype.card (Pos → Y) : ℝ≥0∞)⁻¹ *
          (if T.good v then
            (spongeHardwiredReadRuntime Y D (T.hwOf v) m₀).evalDistMap I (liftH x).liftOrdinary ρ
              (g v) s
            else 0) := by
  have hle : ∀ H : D → Y, (additiveOracleRuntime H).evalDistMap I x ρ (g (T.tab H)) s ≤ 1 :=
    fun H ↦ by
      let : MeasurableSpace (Σ u, W u) := ⊤
      calc _ ≤ (additiveOracleRuntime H).evalDistMap I x ρ (g (T.tab H)) Set.univ :=
            measure_mono (Set.subset_univ s)
        _ = (additiveOracleRuntime H).evalDistMap I x ρ (fun p ↦ p) Set.univ := by
            rw [QuantumRuntime.evalDistMap_apply_univ, QuantumRuntime.evalDistMap_apply_univ]
        _ ≤ 1 := DSubInstrument.outcomeMeasure_apply_univ_le_one _ _
  have hlaw := congrArg (fun μ : Measure β ↦ μ s) (tableAvg_good T m₀ I x ρ g)
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul] at hlaw
  have hsplit : ∀ H : D → Y, (additiveOracleRuntime H).evalDistMap I x ρ (g (T.tab H)) s ≤
      (if T.good (T.tab H) then 0 else 1) +
        (if T.good (T.tab H) then (additiveOracleRuntime H).evalDistMap I x ρ (g (T.tab H))
          else 0) s := fun H ↦ by
    by_cases h : T.good (T.tab H)
    · simp only [h, ite_true, zero_add, le_refl]
    · simp only [h, ite_false, Measure.coe_zero, Pi.zero_apply, add_zero]
      exact hle H
  rw [qromEvalDistMap, sampledEvalDistMap_eq_sum, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, smul_eq_mul]
  calc (Fintype.card (D → Y) : ℝ≥0∞)⁻¹ *
        ∑ H, (additiveOracleRuntime H).evalDistMap I x ρ (g (T.tab H)) s
      ≤ (Fintype.card (D → Y) : ℝ≥0∞)⁻¹ * ∑ H, ((if T.good (T.tab H) then 0 else 1) +
          (if T.good (T.tab H) then (additiveOracleRuntime H).evalDistMap I x ρ (g (T.tab H))
            else 0) s) := by
        gcongr with H
        exact hsplit H
    _ = (Fintype.card (D → Y) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun H ↦ ¬T.good (T.tab H)).card +
        ∑ H, (Fintype.card (D → Y) : ℝ≥0∞)⁻¹ *
          (if T.good (T.tab H) then (additiveOracleRuntime H).evalDistMap I x ρ (g (T.tab H))
            else 0) s := by
        have hcard : (∑ H : D → Y, if T.good (T.tab H) then (0 : ℝ≥0∞) else 1) =
            (Finset.univ.filter fun H ↦ ¬T.good (T.tab H)).card := by
          rw [Finset.card_filter, Nat.cast_sum]
          exact Finset.sum_congr rfl fun H _ ↦ by by_cases h : T.good (T.tab H) <;> simp [h]
        rw [Finset.sum_add_distrib, mul_add, hcard, Finset.mul_sum]
    _ = _ := by
        rw [T.prob_not_good_tab, hlaw]
        refine congrArg _ (Finset.sum_congr rfl fun v _ ↦ ?_)
        by_cases h : T.good v <;> simp [h]

end Quantum.Qrom

end
