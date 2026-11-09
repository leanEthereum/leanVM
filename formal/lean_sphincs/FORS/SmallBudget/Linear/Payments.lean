module

public import FORS.LazyRun.Interpreter

@[expose] public section

section

/-! Bookkeeping for linear potentials on the interpreted comparison: the number of message-digest
queries of a trace, and the expected final payoff of a state once its unexposed coordinates are
completed. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenDebt

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- Number of message-digest queries of a trace. -/
noncomputable def digestCount (entries : List (Entry D)) : ℕ :=
  (entries.filter fun entry => match entry with
    | .inl input => decide (tg.digest input)
    | .inr _ => false).length

omit [Fintype ι] [SampleableType R] in
theorem digestCount_append (first second : List (Entry D)) :
    digestCount tg (first ++ second) = digestCount tg first + digestCount tg second := by
  simp [digestCount, List.filter_append]

/-- Expected final payoff of a state, once its unexposed coordinates are completed. -/
noncomputable def endValue (payoff : (ι → Digest) → DebtState D R ι → ℝ≥0∞) (state : DebtState D R ι) :
    ℝ≥0∞ :=
  ∑' table, Pr{let x ← completion state.known}[x = table] * payoff table state

end FORS.Security.HiddenDebt

end

section

/-! A linear potential on the interpreted comparison with two payments: a fixed amount per
message-digest query, and a fixed amount per query whose input lies in a second class (later, the
FORS leaf inputs, counted whether fresh or cached). If every step keeps the potential in
expectation while making both payments, the potential at the start bounds the expected final
payoff plus all payments of the run. Interpreted runs have total mass one. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenDebt

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- Number of queries of a trace whose input satisfies `IsFleaf`. -/
noncomputable def fleafCount (IsFleaf : D → Prop) (entries : List (Entry D)) : ℕ :=
  (entries.filter fun entry => match entry with
    | .inl input => decide (IsFleaf input)
    | .inr _ => false).length

theorem fleafCount_append (IsFleaf : D → Prop) (first second : List (Entry D)) :
    fleafCount IsFleaf (first ++ second) = fleafCount IsFleaf first + fleafCount IsFleaf second := by
  simp [fleafCount, List.filter_append]

@[simp]
theorem fleafCount_cons_inr (IsFleaf : D → Prop) (amount : ℕ) (entries : List (Entry D)) :
    fleafCount IsFleaf (.inr amount :: entries) = fleafCount IsFleaf entries := by
  simp [fleafCount]

theorem fleafCount_cons_inl (IsFleaf : D → Prop) (input : D) (entries : List (Entry D)) :
    (fleafCount IsFleaf (.inl input :: entries) : ℝ≥0∞) =
      (if IsFleaf input then 1 else 0) + fleafCount IsFleaf entries := by
  by_cases h : IsFleaf input
  · simp [fleafCount, h, add_comm]
  · simp [fleafCount, h]

theorem fleafCount_recorded_inl {H : Type} (IsFleaf : D → Prop) (input : D) :
    (fleafCount IsFleaf (recorded (H := H) (D := D) (R := R) (ι := ι) (.inl (.inr (.inl input)))) : ℝ≥0∞) =
      if IsFleaf input then 1 else 0 := by
  change (fleafCount IsFleaf [.inl input] : ℝ≥0∞) = _
  have h := fleafCount_cons_inl IsFleaf input []
  simpa using h

/-- Steps other than ordinary queries record no input of the class. -/
theorem fleafCount_recorded_eq_zero {H : Type} (IsFleaf : D → Prop) (input : (SourceCostSpec D R ι H).Domain)
    (h : ∀ bytes, input = .inl (.inr (.inl bytes)) → ¬IsFleaf bytes) :
    fleafCount IsFleaf (recorded input) = 0 := by
  rcases input with (draw | (bytes | coordinate)) | (amount | honest)
  · rfl
  · have hb := h bytes rfl
    simp [fleafCount, recorded, hb]
  · rfl
  · simp [fleafCount, recorded]
  · rfl

/-! ### Honest reads

A computation over the cost interface with honest reads (`SourceCostSpec D R ι H`) whose every
honest read stands for a raw input of a class `P`. The potential arguments below take the honest
case of their step hypothesis only at inputs of `P`: an honest read is free (no cost, nothing
recorded), so its step must keep the potential at the same budget, which holds for harmless
classes only (prepared inputs, inputs no potential term reads). -/

section Honest

variable {H : Type} [HonestInputs H D]

/-- Every honest read of the computation stands for a raw input of the class `P`. -/
def HonestWith (P : D → Prop) {α : Type} (computation : OracleComp (SourceCostSpec D R ι H) α) : Prop :=
  OracleComp.construct (fun _ => True)
    (fun input _ next =>
      (∀ honest, input = .inr (.inr honest) → P (HonestInputs.toInput honest)) ∧ ∀ value, next value)
    computation

omit [Fintype ι] [SampleableType R] in
theorem honestWith_pure (P : D → Prop) {α : Type} (value : α) :
    HonestWith (R := R) (ι := ι) (H := H) P (pure value : OracleComp (SourceCostSpec D R ι H) α) := trivial

omit [Fintype ι] [SampleableType R] in
theorem honestWith_query_bind (P : D → Prop) {α : Type} (input : (SourceCostSpec D R ι H).Domain)
    (next : (SourceCostSpec D R ι H).Range input → OracleComp (SourceCostSpec D R ι H) α) :
    HonestWith P (liftM ((SourceCostSpec D R ι H).query input) >>= next) ↔
      (∀ honest, input = .inr (.inr honest) → P (HonestInputs.toInput honest)) ∧
        ∀ value, HonestWith P (next value) :=
  Iff.rfl

end Honest

omit [Fintype ι] [SampleableType R] in
/-- Without honest reads (`H = Empty`) every computation is honest for every class. -/
theorem honestWith_empty (P : D → Prop) {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    HonestWith P computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact honestWith_pure P value
  | query_bind input next ih =>
      exact (honestWith_query_bind P input next).2 ⟨fun honest _ => Empty.elim honest, ih⟩

/-- Interpreted runs lose no mass. -/
theorem interp_mass {H : Type} [HonestInputs H D] {α : Type} (computation : OracleComp (SourceCostSpec D R ι H) α)
    (budget : ℕ) (state : DebtState D R ι) :
    ∑' out, Pr{let x ← interp tg initial model computation budget state}[x = out] = 1 := by
  simp

end FORS.Security.HiddenDebt

end
