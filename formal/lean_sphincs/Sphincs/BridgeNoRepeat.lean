import Sphincs.BridgeNoRepeatDef
import Sphincs.BridgeInternalize

/-! Adversaries that never request a signature on the same message twice stay so when their long
hash inputs are internalized. -/

open OracleComp OracleSpec

namespace Sphincs.Security.ForsPotential

open Internalize Short

theorem noRepeat_map {α β : Type} (g : α → β) :
    ∀ (M : OracleComp AdvSpec α) (S : List Message), NoRepeat M S → NoRepeat (g <$> M) S := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure a => intro S _; exact trivial
  | query_bind t next ih =>
      intro S h
      rw [map_bind]
      rcases t with t | m
      · exact fun v => ih v S (h v)
      · exact ⟨h.1, fun r => ih r _ (h.2 r)⟩

theorem noRepeat_liftWorld_bind {α β : Type} :
    ∀ (x : OracleComp OracleWorld α) (k : α → OracleComp AdvSpec β) (S : List Message),
      (∀ a, NoRepeat (k a) S) → NoRepeat (liftWorld x >>= k) S := by
  intro x
  induction x using OracleComp.inductionOn with
  | pure a =>
      intro k S h
      simp only [liftWorld, simulateQ_pure, pure_bind]
      exact h a
  | query_bind t next ih =>
      intro k S h
      simp only [liftWorld, simulateQ_bind, simulateQ_spec_query, bind_assoc]
      exact fun v => ih v k S h

theorem noRepeat_map_liftWorld_bind {α β γ : Type} (f : α → β) (x : OracleComp OracleWorld α)
    (k : β → OracleComp AdvSpec γ) (S : List Message) (h : ∀ a, NoRepeat (k (f a)) S) :
    NoRepeat ((f <$> liftWorld x) >>= k) S := by
  rw [bind_map_left]
  exact noRepeat_liftWorld_bind x _ S h

theorem noRepeat_internalize {α : Type} :
    ∀ (M : OracleComp AdvSpec α) (S : List Message) (cache : QueryCache HashSpec),
      NoRepeat M S → NoRepeat ((simulateQ internalImpl M).run cache) S := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure a =>
      intro S cache _
      simp only [simulateQ_pure, StateT.run_pure]
      exact trivial
  | query_bind t next ih =>
      intro S cache h
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rcases t with (draw | input) | m
      · change NoRepeat ((forward (.inl (.inl draw))).run cache >>= _) S
        simp only [forward, StateT.run, bind_map_left]
        exact fun v => ih v S cache (h v)
      · change NoRepeat ((if IsShort input then forward (.inl (.inr input)) else privateRead input).run cache >>= _) S
        split_ifs with hs
        · simp only [forward, StateT.run, bind_map_left]
          exact fun v => ih v S cache (h v)
        · simp only [privateRead, StateT.run]
          cases hc : cache input with
          | some answer =>
              exact ih answer S cache (h answer)
          | none =>
              exact noRepeat_map_liftWorld_bind _ _ _ S fun v => ih v S _ (h v)
      · change NoRepeat ((forward (.inr m)).run cache >>= _) S
        simp only [forward, StateT.run, bind_map_left]
        exact ⟨h.1, fun r => ih r _ cache (h.2 r)⟩

theorem noRepeat_internalize_adversary [Params] (adversary : Adversary) (h : adversary.NoRepeat) :
    (internalize adversary).NoRepeat := by
  intro pk
  exact noRepeat_map _ _ [] (noRepeat_internalize _ [] ∅ (h pk))

end Sphincs.Security.ForsPotential
