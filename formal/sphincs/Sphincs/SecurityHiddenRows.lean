import Sphincs.SecurityHiddenReveal

/-! The generic stopped execution of an oracle whose canonical rows read one hidden digest
coordinate and expose one successor. Instantiating the parser later keeps all byte layouts
explicit without making the kernel unfold concrete cryptographic types here. -/
open OracleComp OracleSpec ENNReal
namespace Sphincs.Security.HiddenRows
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

structure Model (D R A ι : Type) where
  parse : D → Option (A × Digest)
  incoming : A → ι
  outgoing : A → ι
  combine : A → Digest → R

variable {D R A ι : Type} [Fintype ι]
noncomputable local instance : DecidableEq ι := Classical.decEq _

/-- The high half of every canonical answer remains explicit and adversary visible. -/
noncomputable def answer (model : Model D R A ι) (table : (ι → Digest)) (outside : D → R) : D → R :=
  fun bytes => (model.parse bytes).elim (outside bytes) fun query =>
    if query.2 = table (model.incoming query.1) then
      model.combine query.1 (table (model.outgoing query.1))
    else outside bytes

def KnownAgrees (table : (ι → Digest)) (known : (HiddenReveal.Knowledge ι)) : Prop :=
  ∀ coordinate value, known coordinate = some value → table coordinate = value

omit [Fintype ι] in
theorem knownAgrees_completion (known : (HiddenReveal.Knowledge ι)) (table : (ι → Digest)) :
    KnownAgrees (tableExtending known table) known :=
  fun coordinate value hvalue => HiddenReveal.completion_known known coordinate value hvalue table

omit [Fintype ι] in
theorem KnownAgrees.reveal {table : (ι → Digest)} {known : (HiddenReveal.Knowledge ι)} (h : KnownAgrees table known)
    (coordinate : ι) :
    KnownAgrees table (known.cacheQuery coordinate (table coordinate)) := by
  intro other value hvalue
  by_cases heq : other = coordinate
  · subst other
    simpa only [QueryCache.cacheQuery_self, Option.some.injEq] using hvalue
  · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hvalue
    exact h other value hvalue

/-- Privileged disclosures are explicit operations, so honest calls can reveal a signature's
frontier or FORS secret without being mistaken for an adversarial equality guess. -/
abbrev SourceSpec (D R ι : Type) := unifSpec + ((D →ₒ R) + (ι →ₒ Digest))

/-- Execute the actual programmed oracle, stopping immediately before an ordinary query
guesses any still-hidden canonical input. This is a concrete experiment, not an independence
assumption about the transcript. -/
noncomputable def stoppedStep {α : Type} (model : Model D R A ι)
    (table : (ι → Digest)) (outside : D → R)
    (source : (SourceSpec D R ι).Domain) (next : (SourceSpec D R ι).Range source → (HiddenReveal.Knowledge ι) → ProbComp (Option α))
    (known : (HiddenReveal.Knowledge ι)) : ProbComp (Option α) :=
  match source with
      | .inl draw => do
          let value ← liftM (unifSpec.query draw)
          next value known
      | .inr (.inr coordinate) =>
          next (table coordinate) (known.cacheQuery coordinate (table coordinate))
      | .inr (.inl bytes) =>
          match model.parse bytes with
          | none => next (answer model table outside bytes) known
          | some query =>
              let address := query.1
              let value := query.2
              if known (model.incoming address) = none ∧ value = table (model.incoming address) then
                pure none
              else if value = table (model.incoming address) then
                next (answer model table outside bytes)
                  (known.cacheQuery (model.outgoing address) (table (model.outgoing address)))
              else next (answer model table outside bytes) known

noncomputable def stopped {α : Type} (model : Model D R A ι) (table : (ι → Digest)) (outside : D → R)
    (computation : OracleComp (SourceSpec D R ι) α) : (HiddenReveal.Knowledge ι) → ProbComp (Option α) :=
  OracleComp.construct (fun value _ => pure (some value))
    (fun source _ next => stoppedStep model table outside source next) computation

set_option maxHeartbeats 100000
section Equations
variable {α : Type} (model : Model D R A ι)
  (table : (ι → Digest)) (outside : D → R)
  (known : (HiddenReveal.Knowledge ι))

omit [Fintype ι] in
theorem stopped_private (draw : unifSpec.Domain)
    (next : unifSpec.Range draw → OracleComp (SourceSpec D R ι) α) :
    stopped model table outside (liftM ((SourceSpec D R ι).query (.inl draw)) >>= next) known =
      (liftM (unifSpec.query draw) >>= fun value =>
        stopped model table outside (next value) known) := rfl

omit [Fintype ι] in
theorem stopped_reveal (coordinate : ι) (next : Digest → OracleComp (SourceSpec D R ι) α) :
    stopped model table outside
      (liftM ((SourceSpec D R ι).query (.inr (.inr coordinate))) >>= next) known =
      stopped model table outside (next (table coordinate))
        (known.cacheQuery coordinate (table coordinate)) := rfl

omit [Fintype ι] in
theorem stopped_hash (bytes : D) (next : R → OracleComp (SourceSpec D R ι) α) :
    stopped model table outside (liftM ((SourceSpec D R ι).query (.inr (.inl bytes))) >>= next) known =
      match model.parse bytes with
      | none => stopped model table outside
          (next (answer model table outside bytes)) known
      | some query =>
          if known (model.incoming query.1) = none ∧ query.2 = table (model.incoming query.1) then
            pure none
          else if query.2 = table (model.incoming query.1) then
            stopped model table outside
              (next (answer model table outside bytes))
              (known.cacheQuery (model.outgoing query.1) (table (model.outgoing query.1)))
          else stopped model table outside
            (next (answer model table outside bytes)) known := by
  unfold stopped
  rw [OracleComp.construct_query_bind]
  rfl

end Equations

noncomputable def stoppedExperiment {α : Type} (model : Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceSpec D R ι) α) (known : (HiddenReveal.Knowledge ι)) : ProbComp (Option α) :=
  HiddenReveal.completion known >>= fun table => stopped model table outside computation known

end Sphincs.Security.HiddenRows
