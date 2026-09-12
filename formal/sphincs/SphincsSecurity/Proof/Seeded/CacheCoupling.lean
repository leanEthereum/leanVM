import SphincsSecurity.Proof.Seeded.StoppedRun

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

def hashBad (bad : HashInput → Prop) : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => bad input

instance (bad : HashInput → Prop) [DecidablePred bad] : DecidablePred (hashBad bad) :=
  fun input => match input with
    | .inl _ => isFalse id
    | .inr input => inferInstanceAs (Decidable (bad input))

def AgreeOutside (bad : HashInput → Prop) (left right : QueryCache HashSpec) : Prop :=
  ∀ input, ¬bad input → left input = right input

theorem AgreeOutside.cacheQuery {bad : HashInput → Prop} {left right : QueryCache HashSpec}
    (h : AgreeOutside bad left right) (input : HashInput) (answer : HashOutput) :
    AgreeOutside bad (left.cacheQuery input answer) (right.cacheQuery input answer) := by
  intro other hother
  by_cases heq : other = input
  · subst other; simp
  · simpa only [QueryCache.cacheQuery_of_ne _ _ heq] using h other hother

theorem run'_stopBefore_eq {α : Type} (bad : HashInput → Prop) [DecidablePred bad]
    (computation : OracleComp OracleWorld α) (left right : QueryCache HashSpec)
    (h : AgreeOutside bad left right) :
    (simulateQ romImpl (stopBefore (hashBad bad) computation)).run' left =
      (simulateQ romImpl (stopBefore (hashBad bad) computation)).run' right := by
  induction computation using OracleComp.inductionOn generalizing left right with
  | pure value => simp [stopBefore_pure]
  | query_bind input next ih =>
      rw [stopBefore_query_bind]
      by_cases hbad : hashBad bad input
      · simp [hbad]
      · simp only [if_neg hbad, run'_query_bind]
        cases input with
        | inl input =>
            dsimp [OracleWorld] at next ih ⊢
            change ((fun answer => (answer, left)) <$> (liftM (unifSpec.query input) : ProbComp _) >>= _) =
              ((fun answer => (answer, right)) <$> (liftM (unifSpec.query input) : ProbComp _) >>= _)
            simp only [bind_map_left]
            congr 1
            funext answer
            exact ih answer left right h
        | inr input =>
            dsimp [OracleWorld] at next ih ⊢
            change ((randomOracle input).run left >>= _) = ((randomOracle input).run right >>= _)
            have heq := h input hbad
            cases hleft : left input with
            | none =>
                have hright : right input = none := heq.symm.trans hleft
                rw [QueryImpl.withCaching_run_none _ hleft, QueryImpl.withCaching_run_none _ hright]
                simp only [bind_map_left]
                congr 1
                funext answer
                exact ih answer _ _ (h.cacheQuery input answer)
            | some answer =>
                have hright : right input = some answer := heq.symm.trans hleft
                rw [QueryImpl.withCaching_run_some _ hleft, QueryImpl.withCaching_run_some _ hright]
                simp only [pure_bind]
                exact ih answer left right h

theorem probEvent_cache_change_le {α : Type} (bad : HashInput → Prop) [DecidablePred bad]
    (computation : OracleComp OracleWorld α) (left right : QueryCache HashSpec)
    (h : AgreeOutside bad left right) (event : α → Prop) :
    Pr[event | (simulateQ romImpl computation).run' left] ≤
      Pr[event | (simulateQ romImpl computation).run' right] +
      Pr[= none | (simulateQ romImpl (stopBefore (hashBad bad) computation)).run' right] := by
  have hbound := probEvent_le_stopBefore_add_failure (hashBad bad) computation left event
  rw [run'_stopBefore_eq bad computation left right h] at hbound
  exact hbound.trans (add_le_add
    (probEvent_stopBefore_le (hashBad bad) computation right event) le_rfl)

end SphincsSecurity.Seeded
