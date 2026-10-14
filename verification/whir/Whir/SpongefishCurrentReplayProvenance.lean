import Whir.SpongefishCurrentCallerGetter
import Whir.PCSBCSIdealConstructionAnswers

/-! Literal observations of the unchanged Program interpreters. This small
operational relation is proof-only: it neither evaluates nor fills a missing
public answer. Its trace includes precisely asks, never compiler-cache hits. -/
namespace Whir.SpongefishCurrentReplayProvenance
open Concrete FiatShamirGame DuplexFraming DuplexModeGame
set_option autoImplicit false

inductive Runs {A : Type} : Program A → List Observation → A → Prop
  | done (a : A) : Runs (.done a) [] a
  | ask (q : Query) (next : Digest32 → Program A) (d : Digest32)
      {os : List Observation} {a : A} (tail : Runs (next d) os a) :
      Runs (.ask q next) (⟨q,d⟩ :: os) a

theorem real_runs {A : Type} (C : PrimitiveOracle) (iv : Digest32) (p : Program A) :
    Runs p (runReal C iv p).view.observations (runReal C iv p).view.result := by
  induction p with
  | done a => exact .done a
  | ask q next ih => exact .ask q next (realAnswer C iv q) (ih _)

theorem ideal_runs {Q : Nat} {Seed State A : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State) (p : Program A)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p) :
    Runs p (runIdeal sim ro iv state p remaining cap counted).view.observations
      (runIdeal sim ro iv state p remaining cap counted).view.result := by
  induction p generalizing remaining state with
  | done a => exact .done a
  | ask q next ih =>
    cases q with
    | primitive purpose input =>
      exact .ask _ _ _ (ih _ _ _ _ (counted.2 _))
    | construction q valid =>
      exact .ask _ _ _ (ih _ _ _ _ (counted.2 _))

theorem bind_runs {A B : Type} (p : Program A) (next : A → Program B)
    {os : List Observation} {b : B} (ran : Runs (WHIRModeFinal.bind p next) os b) :
    ∃ a before after, os = before ++ after ∧ Runs p before a ∧ Runs (next a) after b := by
  induction p generalizing os b with
  | done a => exact ⟨a,[],os,rfl,.done a,ran⟩
  | ask q cont ih =>
    cases ran with
    | ask _ _ d tail =>
      obtain ⟨a,before,after,equal,first,last⟩ := ih d tail
      exact ⟨a,⟨q,d⟩ :: before,after,by simp [equal],.ask q cont d first,last⟩

theorem observation_cap {A : Type} {p : Program A} {os : List Observation} {a : A}
    (ran : Runs p os a) (Q : Nat) (counted : Counts Q p) :
    ∀ o ∈ os, o.query.cost ≤ Q := by
  induction ran generalizing Q with
  | done => simp
  | ask q next d tail ih =>
    intro o member
    rcases List.mem_cons.mp member with rfl | later
    · exact counted.1
    · exact (ih _ (counted.2 d) o later).trans (Nat.sub_le _ _)

theorem bind_real_observations {A B : Type} (C : PrimitiveOracle) (iv : Digest32)
    (p : Program A) (next : A → Program B) :
    (runReal C iv (WHIRModeFinal.bind p next)).view.observations =
      (runReal C iv p).view.observations ++
      (runReal C iv (next (runReal C iv p).view.result)).view.observations := by
  induction p with
  | done a => rfl
  | ask q cont ih =>
    simp only [WHIRModeFinal.bind,runReal,prepend,List.cons_append]
    exact congrArg (List.cons ⟨q,realAnswer C iv q⟩) (ih (realAnswer C iv q))

/-- Coverage is derived from the actual full execution, not a GetterCovers
certificate. An actual construction-only subrun may use any public prefix or
suffix; its keys inherit the aggregate Program.Counts cap. -/
theorem actual_getter {A B : Type} (C : PrimitiveOracle) (iv : Digest32)
    (whole : Program A) (part : Program B) (Q : Nat) (counted : Counts Q whole)
    (included : ∀ o ∈ (runReal C iv part).view.observations,
      o ∈ (runReal C iv whole).view.observations)
    (construction : ∀ o ∈ (runReal C iv part).view.observations,
      ∃ q valid, o.query = .construction q valid) :
    ∀ o ∈ (runReal C iv part).view.observations,
      SpongefishCurrentCallerGetter.answer (Q := Q)
        (runReal C iv whole).view.observations o.query = some o.answer := by
  intro o member
  obtain ⟨q,valid,equal⟩ := construction o member
  have present := included o member
  have cap := observation_cap (real_runs C iv whole) Q counted o present
  have consistent := SpongefishCurrentCallerGetter.real_consistent C iv whole
  have value := consistent o present
  rw [equal] at cap value ⊢
  change SpongefishCurrentCallerGetter.bounded (Q := Q) _ q = some o.answer
  rw [SpongefishCurrentCallerGetter.bounded_real C iv _ consistent q valid cap
    ⟨o,present,equal⟩]
  exact congrArg some value.symm

theorem run_observed {A : Type} {p : Program A} {os : List Observation} {a : A}
    (ran : Runs p os a) (get : Query → Option Digest32)
    (observed : ∀ o ∈ os, get o.query = some o.answer) :
    SpongefishCurrentCallerGetter.run get p = some a := by
  induction ran with
  | done a => rfl
  | ask q next d tail ih =>
    have first := observed ⟨q,d⟩ List.mem_cons_self
    simp only [SpongefishCurrentCallerGetter.run,first,Option.bind_some]
    exact ih (fun o h => observed o (List.mem_cons_of_mem _ h))

/-- Lookup returns a literal answer, even when a coordinate occurs repeatedly.
Only equality of its observed full replies matters; no oracle is run here. -/
theorem lookup_literal (os : List Observation) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) (d : Digest32)
    (same : ∀ o ∈ os, o.query = .construction q valid → o.answer = d)
    (present : ∃ o ∈ os, o.query = .construction q valid) :
    SpongefishCurrentCallerGetter.lookup q os = some d := by
  induction os with
  | nil => simp at present
  | cons o os ih =>
    have tail := ih (fun x h => same x (List.mem_cons_of_mem _ h))
    cases query : o.query with
    | primitive purpose input =>
      simp only [SpongefishCurrentCallerGetter.lookup,query]
      apply tail
      obtain ⟨x,member,equal⟩ := present
      rcases List.mem_cons.mp member with rfl | member
      · rw [query] at equal
        cases equal
      · exact ⟨x,member,equal⟩
    | construction other proof =>
      simp only [SpongefishCurrentCallerGetter.lookup,query]
      split
      · rename_i equal
        subst other
        exact congrArg some (same o List.mem_cons_self query)
      · rename_i different
        apply tail
        obtain ⟨x,member,equal⟩ := present
        rcases List.mem_cons.mp member with rfl | member
        · rw [query] at equal
          cases equal
          exact False.elim (different rfl)
        · exact ⟨x,member,equal⟩

/-- The literal ideal construction answer is recoverable from the full public
view, with its bounded key, irrespective of ordinary simulator work or abort. -/
theorem ideal_observed_getter {Q : Nat} {Seed State A : Type}
    (sim : Simulator Q Seed State) (ro : RawKey Q → Digest32) (iv : Digest32)
    (state : State) (p : Program A) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining p) (q : Coordinate) (valid : DuplexEncoding.Admissible q)
    (d : Digest32)
    (present : (⟨.construction q valid,d⟩ : Observation) ∈
      (runIdeal sim ro iv state p remaining cap counted).view.observations) :
    ∃ work : pathCost q ≤ Q,
      d = ro (constructionKey Q iv q work) ∧
      SpongefishCurrentCallerGetter.raw iv
        (runIdeal sim ro iv state p remaining cap counted).view.observations
        (constructionKey Q iv q work) = some d := by
  obtain ⟨work,answer⟩ := PCSBCSIdealConstructionAnswers.construction_observations
    sim ro iv state p remaining cap counted q valid d present
  refine ⟨work,answer,?_⟩
  rw [SpongefishCurrentCallerGetter.raw_construction iv _ q valid work]
  apply lookup_literal _ q valid d _ ⟨_,present,rfl⟩
  intro o member equal
  have literal : (⟨.construction q valid,o.answer⟩ : Observation) ∈
      (runIdeal sim ro iv state p remaining cap counted).view.observations := by
    have observation : o = ⟨.construction q valid,o.answer⟩ := by
      cases o
      simp_all
    exact observation ▸ member
  obtain ⟨otherWork,otherAnswer⟩ := PCSBCSIdealConstructionAnswers.construction_observations
    sim ro iv state p remaining cap counted q valid o.answer literal
  exact otherAnswer.trans answer.symm

#print axioms real_runs
#print axioms ideal_runs
#print axioms bind_runs
#print axioms observation_cap
#print axioms actual_getter
#print axioms lookup_literal
#print axioms ideal_observed_getter
#print axioms run_observed
end Whir.SpongefishCurrentReplayProvenance
