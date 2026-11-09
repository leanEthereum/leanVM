module

public import FORS.LazyRun.InterpreterFacts

@[expose] public section

/-! Honest reads (`HiddenCost.honestRead`, the cost interface's third summand): raw queries the
honest parties make, answered by the comparison as the raw query they stand for, but free (no
cost, nothing recorded, no baseline payment) so that a budget bounds the other parties' queries
only. A potential argument pays for a query out of its budget decrement; an honest read brings
none, so it must be harmless: its raw input is unparsed (no row query, hence no guess) and either
prepared in the initial cache (answered from it, the state unchanged) or untargeted (a fresh
answer creates no debt). `HonestGood` is that condition, `HonestOk` says every honest read of a
computation meets it, and the step lemmas below are the honest case of every potential's
induction: the invariant at the same probe count and the weight in the mean. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenDebt

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R] {H : Type} [HonestInputs H D]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-! ### The harmless raw inputs -/

/-- A raw input an honest read may stand for: unparsed, and prepared in the initial cache or
untargeted. -/
def HonestGood (bytes : D) : Prop :=
  model.parse bytes = none ∧ (initial bytes ≠ none ∨ tg.kind bytes = .none)

/-- Every honest read of the computation stands for a harmless raw input. -/
def HonestOk {α : Type} (computation : OracleComp (SourceCostSpec D R ι H) α) : Prop :=
  OracleComp.construct (fun _ => True)
    (fun input _ next =>
      (∀ honest, input = .inr (.inr honest) → HonestGood tg initial model (HonestInputs.toInput honest)) ∧
        ∀ value, next value)
    computation

omit [Fintype ι] [SampleableType R] in
@[simp] theorem sourceCost_honest (honest : H) :
    sourceCost (D := D) (R := R) (ι := ι) (.inr (.inr honest)) = 0 := rfl

omit [Fintype ι] [SampleableType R] in
theorem honestOk_query_bind {α : Type} (input : (SourceCostSpec D R ι H).Domain)
    (next : (SourceCostSpec D R ι H).Range input → OracleComp (SourceCostSpec D R ι H) α) :
    HonestOk tg initial model (liftM ((SourceCostSpec D R ι H).query input) >>= next) ↔
      (∀ honest, input = .inr (.inr honest) → HonestGood tg initial model (HonestInputs.toInput honest)) ∧
        ∀ value, HonestOk tg initial model (next value) :=
  Iff.rfl

omit [Fintype ι] [SampleableType R] in
/-- A query other than an honest read imposes nothing. -/
theorem honestOk_query_of_ne (input : (SourceCostSpec D R ι H).Domain)
    (hinput : ∀ honest, input ≠ .inr (.inr honest)) :
    HonestOk tg initial model
      (liftM ((SourceCostSpec D R ι H).query input) : OracleComp (SourceCostSpec D R ι H) _) := by
  rw [← bind_pure (liftM ((SourceCostSpec D R ι H).query input))]
  exact (honestOk_query_bind tg initial model input _).2
    ⟨fun honest h => absurd h (hinput honest), fun _ => trivial⟩

omit [Fintype ι] [SampleableType R] in
theorem honestOk_reveal (coordinate : ι) :
    HonestOk tg initial model (reveal (H := H) (D := D) (R := R) coordinate) :=
  honestOk_query_of_ne tg initial model _ fun _ h => by cases h

/-! ### Free steps -/

/-! ### A harmless honest read keeps the invariant and the weight -/

omit [Fintype ι] in
/-- A harmless honest read is the outside read of its raw input. -/
theorem costStep_honest_good (honest : H) (state : DebtState D R ι)
    (hgood : HonestGood tg initial model (HonestInputs.toInput honest)) :
    costStep model (.inr (.inr honest)) state = readOutside (HonestInputs.toInput honest) state := by
  rw [costStep_honest, costStep_inl]
  exact lazyStep_unparsed model _ state hgood.1

omit [Fintype ι] in
/-- A prepared raw input is answered from the cache, the state unchanged. -/
theorem readOutside_prepared (bytes : D) (state : DebtState D R ι) (hprepared : Prepared initial state)
    (hi : initial bytes ≠ none) : ∃ output, readOutside bytes state = pure (output, state) := by
  obtain ⟨output, hout⟩ := Option.ne_none_iff_exists'.mp hi
  exact ⟨output, readOutside_cached bytes state output (hprepared bytes output hout)⟩

/-- **A harmless honest read keeps the invariant at the same probe count.** -/
theorem inv_honest (honest : H) (state : DebtState D R ι) (probes : ℕ) (hinv : Inv tg initial state probes)
    (hgood : HonestGood tg initial model (HonestInputs.toInput honest))
    (result : R × DebtState D R ι) (hresult : result ∈ support (costStep model (.inr (.inr honest)) state)) :
    Inv tg initial result.2 probes := by
  rw [costStep_honest_good tg initial model honest state hgood] at hresult
  rcases hgood.2 with hi | hk
  · obtain ⟨output, hout⟩ := readOutside_prepared initial _ state hinv.prepared hi
    rw [hout, support_pure, Set.mem_singleton_iff] at hresult
    rw [hresult]
    exact hinv
  · exact inv_readOutside_none tg initial _ state probes hinv hk result hresult

/-- **A harmless honest read keeps the weight in the mean.** -/
theorem meanWeight_honest (honest : H) (state : DebtState D R ι) (hprepared : Prepared initial state)
    (hgood : HonestGood tg initial model (HonestInputs.toInput honest)) :
    meanWeight tg initial (costStep model (.inr (.inr honest)) state) = weight tg initial state := by
  rw [costStep_honest_good tg initial model honest state hgood]
  rcases hgood.2 with hi | hk
  · obtain ⟨output, hout⟩ := readOutside_prepared initial _ state hprepared hi
    rw [meanWeight, hout, OracleComp.tsum_prEvent_pure_mul]
  · exact meanWeight_readOutside_none tg initial _ state hk hprepared

end FORS.Security.HiddenDebt
