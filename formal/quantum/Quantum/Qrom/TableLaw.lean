module

public import Quantum.Qrom.Embed

@[expose] public section

/-!
# The lazy table law

A scheme's honest computation hashes, at each position `s` of a finite set `Pos`, one input
`cell s v`, a function of the values `v` at the predecessors of `s` (a well-founded relation);
for every `v` the cells of distinct positions differ (`LazyTable`). Against a random oracle `H`
the honest values are the table `tab H` with `tab H s = H (cell s (tab H))` (`tab_eq`), the
only such function (`tab_unique`).

**The law** (`qromEvalDistMap_eq_tableAvg`): averaging over uniform `H` a run observed through the
honest values is averaging over uniform values `v : Pos → Y` the run against runtime 1 with the
cells of `v` hardwired to their values (`hwOf v`). The proof: runtime 1 is the experiment with
the functions `fill v v H`, `H` overwritten at the cells of `v` by `v`
(`evalDistMap_hardwired_liftH`), and `(v, H) ↦ (fill v v H, H ∘ cell · v)` is a bijection
`(Pos → Y) × (D → Y) ≃ (D → Y) × (Pos → Y)` with inverse `(H', u) ↦ (tab H', fill (tab H') u H')`
(`tableEquiv`), so each `H'` arises `|Y|^|Pos|` times, all with `v = tab H'`
(`sum_sum_fill`).
-/

open MeasureTheory
open scoped ENNReal

universe u v w

namespace Quantum.Qrom

open Quantum Quantum.Sponge

/-- **A lazy table** of a random function `D → Y`: each position `s` hashes its cell `cell s v`,
which depends only on the values `v` at the predecessors of `s` (`pre`, well founded) and, for
every `v`, differs from the cells of the other positions. -/
structure LazyTable (Pos D Y : Type) where
  /-- The input hashed at position `s`, given the values `v`. -/
  cell : Pos → (Pos → Y) → D
  /-- `pre s' s`: position `s'` precedes `s`. -/
  pre : Pos → Pos → Prop
  wf : WellFounded pre
  /-- The cell of `s` reads only the values at the predecessors of `s`. -/
  dep : ∀ s v v', (∀ s', pre s' s → v s' = v' s') → cell s v = cell s v'
  /-- Distinct positions hash distinct inputs. -/
  inj : ∀ v, Function.Injective fun s ↦ cell s v

namespace LazyTable

section table

variable {Pos D Y : Type} (T : LazyTable Pos D Y)

/-- The cells of `v`, hardwired to the values `w`: cell `cell s v` holds `w s`. -/
noncomputable def tableDb (v w : Pos → Y) : Database D Y := fun z ↦
  @dite _ (∃ s, T.cell s v = z) (Classical.propDecidable _) (fun h ↦ some (w h.choose))
    fun _ ↦ none

theorem tableDb_cell (v w : Pos → Y) (s : Pos) : T.tableDb v w (T.cell s v) = some (w s) := by
  have h : ∃ s', T.cell s' v = T.cell s v := ⟨s, rfl⟩
  unfold tableDb
  rw [dite_eq_left h, T.inj v h.choose_spec]

theorem tableDb_of_forall_ne {v w : Pos → Y} {z : D} (hz : ∀ s, T.cell s v ≠ z) :
    T.tableDb v w z = none := by
  unfold tableDb
  rw [dite_eq_right]
  rintro ⟨s, hs⟩
  exact hz s hs

/-- `H` with the cells of `v` overwritten by the values `w`. -/
noncomputable def fill (v w : Pos → Y) (H : D → Y) : D → Y :=
  fun z ↦ (T.tableDb v w z).getD (H z)

theorem fill_cell (v w : Pos → Y) (H : D → Y) (s : Pos) : T.fill v w H (T.cell s v) = w s := by
  unfold fill
  rw [tableDb_cell]
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
  · obtain ⟨s, rfl⟩ := hz
    rw [fill_cell, fill_cell]
  · push Not at hz
    rw [T.fill_of_forall_ne hz, T.fill_of_forall_ne hz, T.fill_of_forall_ne hz]

/-- Overwriting the cells by the values they hold changes nothing. -/
theorem fill_of_cell {v w : Pos → Y} {H : D → Y} (hH : ∀ s, H (T.cell s v) = w s) :
    T.fill v w H = H := by
  funext z
  by_cases hz : ∃ s, T.cell s v = z
  · obtain ⟨s, rfl⟩ := hz
    rw [fill_cell, hH]
  · push Not at hz
    rw [T.fill_of_forall_ne hz]

/-- Restoring the overwritten values gives back the function. -/
theorem fill_restore (v w : Pos → Y) (H : D → Y) :
    T.fill v (fun s ↦ H (T.cell s v)) (T.fill v w H) = H := by
  rw [fill_fill]
  exact T.fill_of_cell fun _ ↦ rfl

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

theorem tab_fill (v : Pos → Y) (H : D → Y) : T.tab (T.fill v v H) = v :=
  T.tab_unique (T.fill_cell v v H)

/-- **Overwriting the cells of `v` and reading them** is a bijection
`(v, H) ↦ (fill v v H, H ∘ cell · v)`, with inverse `(H', u) ↦ (tab H', fill (tab H') u H')`. -/
noncomputable def tableEquiv : (Pos → Y) × (D → Y) ≃ (D → Y) × (Pos → Y) where
  toFun p := (T.fill p.1 p.1 p.2, fun s ↦ p.2 (T.cell s p.1))
  invFun q := (T.tab q.1, T.fill (T.tab q.1) q.2 q.1)
  left_inv p := by
    obtain ⟨v, H⟩ := p
    refine Prod.ext (T.tab_fill v H) ?_
    change T.fill (T.tab (T.fill v v H)) (fun s ↦ H (T.cell s v)) (T.fill v v H) = H
    rw [T.tab_fill]
    exact T.fill_restore v v H
  right_inv q := by
    obtain ⟨H, u⟩ := q
    refine Prod.ext ?_ (funext fun s ↦ T.fill_cell _ u H s)
    change T.fill (T.tab H) (T.tab H) (T.fill (T.tab H) u H) = H
    rw [fill_fill]
    exact T.fill_of_cell fun s ↦ (T.tab_eq H s).symm

/-- **Summing over values and functions the overwritten functions** counts every function
`|Y|^|Pos|` times, with its table as values. -/
theorem sum_sum_fill [Fintype Pos] [DecidableEq Pos] [Fintype D] [DecidableEq D] [Fintype Y]
    {β : Type*} [AddCommMonoid β] (F : (Pos → Y) → (D → Y) → β) :
    ∑ v, ∑ H, F v (T.fill v v H) = Fintype.card (Pos → Y) • ∑ H, F (T.tab H) H := by
  calc ∑ v, ∑ H, F v (T.fill v v H)
      = ∑ p : (Pos → Y) × (D → Y), (fun q : (D → Y) × (Pos → Y) ↦ F (T.tab q.1) q.1)
          (T.tableEquiv p) := by
        rw [← Fintype.sum_prod_type']
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        change F p.1 (T.fill p.1 p.1 p.2) = F (T.tab (T.fill p.1 p.1 p.2)) (T.fill p.1 p.1 p.2)
        rw [T.tab_fill]
    _ = ∑ q : (D → Y) × (Pos → Y), F (T.tab q.1) q.1 :=
        T.tableEquiv.sum_comp fun q : (D → Y) × (Pos → Y) ↦ F (T.tab q.1) q.1
    _ = Fintype.card (Pos → Y) • ∑ H, F (T.tab H) H := by
        rw [Fintype.sum_prod_type, Finset.smul_sum]
        refine Finset.sum_congr rfl fun H _ ↦ ?_
        change ∑ _u : Pos → Y, F (T.tab H) H = _
        rw [Finset.sum_const, Finset.card_univ]

end table

/-- The hardwired cells of the values `v`: the cells of `v`, holding `v`. -/
noncomputable def hwOf {Pos D Y : Type} (T : LazyTable Pos D Y) (v : Pos → Y) : Hw Y D :=
  hwCells (T.tableDb v v)

end LazyTable

variable {Pos D Y : Type} [Fintype Pos] [DecidableEq Pos] [Fintype D] [DecidableEq D]
  [Fintype Y] [DecidableEq Y] [AddCommGroup D] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **The lazy table law.** A program against a uniform random oracle `H`, observed through its
table `tab H`, has the law of the average over uniform values `v` of the lifted program against
runtime 1 started with the cells of `v` hardwired to `v`. -/
theorem qromEvalDistMap_eq_tableAvg (T : LazyTable Pos D Y) {M : Type} [Fintype M]
    [DecidableEq M] (m₀ : M) {β : Type*} [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp L (qromSpec D Y) W A) (ρ : SubState A)
    (g : (Pos → Y) → (Σ u, W u) → β) :
    qromEvalDistMap I x ρ (fun H ↦ g (T.tab H)) =
      ∑ v : Pos → Y, (Fintype.card (Pos → Y) : ℝ≥0∞)⁻¹ •
        (spongeHardwiredReadRuntime Y D (T.hwOf v) m₀).evalDistMap I (liftH x).liftOrdinary ρ
          (g v) := by
  have hrun : ∀ v : Pos → Y,
      (spongeHardwiredReadRuntime Y D (T.hwOf v) m₀).evalDistMap I (liftH x).liftOrdinary ρ
          (g v) =
        (Fintype.card (D → Y) : ℝ≥0∞)⁻¹ • ∑ H : D → Y,
          (additiveOracleRuntime (T.fill v v H)).evalDistMap I x ρ (g v) :=
    fun v ↦ evalDistMap_hardwired_liftH (T.hwOf v) m₀ I x ρ (g v)
  have key : ∑ v : Pos → Y, ∑ H : D → Y,
      (additiveOracleRuntime (T.fill v v H)).evalDistMap I x ρ (g v) =
      Fintype.card (Pos → Y) • ∑ H : D → Y,
        (additiveOracleRuntime H).evalDistMap I x ρ (g (T.tab H)) :=
    T.sum_sum_fill fun v H ↦ (additiveOracleRuntime H).evalDistMap I x ρ (g v)
  have hP : (Fintype.card (Pos → Y) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [qromEvalDistMap, sampledEvalDistMap_eq_sum]
  simp only [hrun, smul_smul, ← Finset.smul_sum]
  rw [key, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul, mul_right_comm,
    ENNReal.inv_mul_cancel hP (ENNReal.natCast_ne_top _), one_mul]

end Quantum.Qrom

end
