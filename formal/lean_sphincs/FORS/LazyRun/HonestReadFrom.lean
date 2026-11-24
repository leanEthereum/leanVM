module

public import FORS.LazyRun.HonestRead

@[expose] public section

/-! Honest reads from a prepared state. `HonestOk` asks every honest read of a computation, along
every answer, to be harmless; an honest search that stops at its first success then fails the
check at the trials past it, which no run from a prepared state reaches (the earlier trials are
answered from the initial cache and the search stops where it stopped when the cache was made).
`HonestOkFrom` asks less: at an honest read of a prepared raw input only the continuation of its
initial answer is constrained, the one answer the comparison gives from a prepared state
(`readOutside_cached`). `honestOkFrom_step` is what a potential's induction uses at an honest
step: the read is harmless, and every continuation the step can reach is again `HonestOkFrom`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenDebt

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R] {H : Type} [HonestInputs H D]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- The answers a run from a prepared state can give a query: the initial answer at an honest read
of a prepared raw input, any answer otherwise. -/
def AllowedAnswer : (input : (SourceCostSpec D R ι H).Domain) → (SourceCostSpec D R ι H).Range input → Prop
  | .inr (.inr honest), value => ∀ output, initial (HonestInputs.toInput honest) = some output → value = output
  | .inl _, _ => True
  | .inr (.inl _), _ => True

/-- Every honest read the computation can reach from a prepared state stands for a harmless raw
input. -/
def HonestOkFrom {α : Type} (computation : OracleComp (SourceCostSpec D R ι H) α) : Prop :=
  OracleComp.construct (fun _ => True)
    (fun input _ next =>
      (∀ honest, input = .inr (.inr honest) → HonestGood tg initial model (HonestInputs.toInput honest)) ∧
        ∀ value, AllowedAnswer initial input value → next value)
    computation

omit [Fintype ι] [SampleableType R] in
theorem honestOkFrom_pure {α : Type} (value : α) :
    HonestOkFrom tg initial model (pure value : OracleComp (SourceCostSpec D R ι H) α) := trivial

omit [Fintype ι] [SampleableType R] in
theorem honestOkFrom_query_bind {α : Type} (input : (SourceCostSpec D R ι H).Domain)
    (next : (SourceCostSpec D R ι H).Range input → OracleComp (SourceCostSpec D R ι H) α) :
    HonestOkFrom tg initial model (liftM ((SourceCostSpec D R ι H).query input) >>= next) ↔
      (∀ honest, input = .inr (.inr honest) → HonestGood tg initial model (HonestInputs.toInput honest)) ∧
        ∀ value, AllowedAnswer initial input value → HonestOkFrom tg initial model (next value) :=
  Iff.rfl

omit [Fintype ι] [SampleableType R] in
theorem honestOkFrom_bind {α β : Type} {first : OracleComp (SourceCostSpec D R ι H) α}
    {next : α → OracleComp (SourceCostSpec D R ι H) β} (hfirst : HonestOkFrom tg initial model first)
    (hnext : ∀ value, HonestOkFrom tg initial model (next value)) :
    HonestOkFrom tg initial model (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using hnext value
  | query_bind input rest ih =>
      rw [bind_assoc, honestOkFrom_query_bind]
      obtain ⟨hin, hrest⟩ := (honestOkFrom_query_bind tg initial model input rest).1 hfirst
      exact ⟨hin, fun value hv => ih value (hrest value hv)⟩

omit [Fintype ι] [SampleableType R] in
/-- `HonestOk` asks more. -/
theorem honestOkFrom_of_honestOk {α : Type} {computation : OracleComp (SourceCostSpec D R ι H) α}
    (h : HonestOk tg initial model computation) : HonestOkFrom tg initial model computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact honestOkFrom_pure tg initial model value
  | query_bind input next ih =>
      obtain ⟨hin, hrest⟩ := (honestOk_query_bind tg initial model input next).1 h
      exact (honestOkFrom_query_bind tg initial model input next).2 ⟨hin, fun value _ => ih value (hrest value)⟩

omit [Fintype ι] [SampleableType R] in
/-- A query other than an honest read imposes nothing. -/
theorem honestOkFrom_query_of_ne (input : (SourceCostSpec D R ι H).Domain)
    (hinput : ∀ honest, input ≠ .inr (.inr honest)) :
    HonestOkFrom tg initial model
      (liftM ((SourceCostSpec D R ι H).query input) : OracleComp (SourceCostSpec D R ι H) _) :=
  honestOkFrom_of_honestOk tg initial model (honestOk_query_of_ne tg initial model input hinput)

omit [Fintype ι] [SampleableType R] in
theorem honestOkFrom_reveal (coordinate : ι) :
    HonestOkFrom tg initial model (reveal (H := H) (D := D) (R := R) coordinate) :=
  honestOkFrom_of_honestOk tg initial model (honestOk_reveal tg initial model coordinate)

omit [Fintype ι] [SampleableType R] in
/-- An honest read of a harmless raw input, then a continuation constrained at the answers a
prepared state allows. -/
theorem honestOkFrom_honestRead_bind {α : Type} (honest : H) (next : R → OracleComp (SourceCostSpec D R ι H) α)
    (hgood : HonestGood tg initial model (HonestInputs.toInput honest))
    (hnext : ∀ value, (∀ output, initial (HonestInputs.toInput honest) = some output → value = output) →
      HonestOkFrom tg initial model (next value)) :
    HonestOkFrom tg initial model (honestRead (D := D) (R := R) (ι := ι) honest >>= next) := by
  unfold honestRead
  refine (honestOkFrom_query_bind tg initial model (.inr (.inr honest)) next).2
    ⟨fun honest' h => ?_, fun value hv => hnext value hv⟩
  cases h
  exact hgood

omit [Fintype ι] [SampleableType R] in
theorem honestOkFrom_sequenceFin {α : Type} :
    ∀ {n : ℕ} (computation : Fin n → OracleComp (SourceCostSpec D R ι H) α),
      (∀ i, HonestOkFrom tg initial model (computation i)) →
        HonestOkFrom tg initial model (Concrete.sequenceFin computation)
  | 0, _, _ => honestOkFrom_pure tg initial model _
  | n + 1, computation, h => by
      unfold Concrete.sequenceFin
      exact honestOkFrom_bind tg initial model (h 0) fun _ =>
        honestOkFrom_bind tg initial model (honestOkFrom_sequenceFin (fun i : Fin n => computation i.succ)
          fun i => h i.succ) fun _ => honestOkFrom_pure tg initial model _

/-! ### The honest step from a prepared state -/

omit [Fintype ι] in
/-- **The honest case of a potential's induction.** From a prepared state, an honest read the
computation can reach is harmless, and every result of its comparison step leaves a continuation
that is again `HonestOkFrom`. -/
theorem honestOkFrom_step {α : Type} (honest : H) (next : R → OracleComp (SourceCostSpec D R ι H) α)
    (state : DebtState D R ι) (hprepared : Prepared initial state)
    (h : HonestOkFrom tg initial model
      (liftM ((SourceCostSpec D R ι H).query (.inr (.inr honest))) >>= next)) :
    HonestGood tg initial model (HonestInputs.toInput honest) ∧
      ∀ result ∈ support (costStep model (.inr (.inr honest)) state),
        HonestOkFrom tg initial model (next result.1) := by
  obtain ⟨hin, hrest⟩ := (honestOkFrom_query_bind tg initial model (.inr (.inr honest)) next).1 h
  have hgood := hin honest rfl
  refine ⟨hgood, fun result hresult => hrest result.1 ?_⟩
  rw [costStep_honest_good tg initial model honest state hgood] at hresult
  intro output hout
  rw [readOutside_cached _ state output (hprepared _ output hout), support_pure,
    Set.mem_singleton_iff] at hresult
  rw [hresult]

end FORS.Security.HiddenDebt
