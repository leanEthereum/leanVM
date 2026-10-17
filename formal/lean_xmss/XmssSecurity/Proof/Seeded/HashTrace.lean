import XmssSecurity.Proof.Seeded.CacheCoupling
import XmssSecurity.Proof.ConsistentQueryBound

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

def prependHash (input : OracleWorld.Domain) (inputs : List HashInput) : List HashInput :=
  match input with
  | .inl _ => inputs
  | .inr input => input :: inputs

noncomputable def traceHashes {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp OracleWorld (α × List HashInput) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => do
      let answer ← liftM (OracleWorld.query input)
      let result ← next answer
      return (result.1, prependHash input result.2)) computation

theorem traceHashes_pure {α : Type} (value : α) :
    traceHashes (pure value) = pure (value, []) := rfl

theorem traceHashes_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) :
    traceHashes (liftM (OracleWorld.query input) >>= next) = (do
      let answer ← liftM (OracleWorld.query input)
      let result ← traceHashes (next answer)
      return (result.1, prependHash input result.2)) := rfl

theorem traceHashes_length {α : Type} (computation : OracleComp OracleWorld α) :
    (fun result => (result.1, result.2.length)) <$> traceHashes computation =
      countHashQueries computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [traceHashes_query_bind, countHashQueries_query_bind, map_bind, map_pure]
      congr 1
      funext answer
      rw [← ih answer]
      simp only [bind_pure_comp, Functor.map_map]
      congr 1
      funext result
      cases input <;> simp [prependHash, Nat.add_comm]

theorem traceHashes_length_le {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat) (hbound : HashQueryBound computation cache q)
    (result : α × List HashInput)
    (hresult : result ∈ support ((simulateQ romImpl (traceHashes computation)).run' cache)) :
    result.2.length ≤ q := by
  apply hbound (result.1, result.2.length)
  rw [← traceHashes_length, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map, support_map]
  rw [StateT.run'_eq, support_map] at hresult
  obtain ⟨record, hrecord, rfl⟩ := hresult
  exact ⟨record, hrecord, rfl⟩

def TraceHits (bad : HashInput → Prop) (inputs : List HashInput) : Prop :=
  ∃ input ∈ inputs, bad input

theorem traceHits_prepend (bad : HashInput → Prop) (input : OracleWorld.Domain)
    (inputs : List HashInput) :
    TraceHits bad (prependHash input inputs) ↔ hashBad bad input ∨ TraceHits bad inputs := by
  cases input <;> simp [TraceHits, prependHash, hashBad]

theorem probOutput_stopBefore_none {α : Type} (bad : HashInput → Prop) [DecidablePred bad]
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    Pr[= none | (simulateQ romImpl (stopBefore (hashBad bad) computation)).run' cache] =
      Pr[fun result => TraceHits bad result.2 |
        (simulateQ romImpl (traceHashes computation)).run' cache] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [stopBefore_pure, traceHashes_pure, TraceHits]
  | query_bind input next ih =>
      rw [stopBefore_query_bind, traceHashes_query_bind]
      by_cases hbad : hashBad bad input
      · rw [if_pos hbad, run'_query_bind]
        simp [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map]
        intro a b answer cache' _ a' inputs cache'' _ _ hb
        rw [← hb, traceHits_prepend]
        exact Or.inl hbad
      · rw [if_neg hbad, run'_query_bind, run'_query_bind]
        simp only [probOutput_bind_eq_tsum, probEvent_bind_eq_tsum]
        apply tsum_congr
        intro result
        rw [ih result.1 result.2]
        simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
          Functor.map_map, probEvent_map, Function.comp_def, traceHits_prepend, hbad, false_or]

end XmssSecurity.Seeded
