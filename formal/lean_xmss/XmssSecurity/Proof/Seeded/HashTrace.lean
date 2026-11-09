module

public import XmssSecurity.Proof.Seeded.CacheCoupling
public import XmssSecurity.Proof.ConsistentQueryBound

@[expose] public section

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
    Pr{let x ← (simulateQ romImpl (stopBefore (hashBad bad) computation)).run' cache}[x = none] =
      Pr{let result ← (simulateQ romImpl (traceHashes computation)).run' cache}[TraceHits bad result.2] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [stopBefore_pure, traceHashes_pure, TraceHits]
  | query_bind input next ih =>
      rw [stopBefore_query_bind, traceHashes_query_bind]
      by_cases hbad : hashBad bad input
      · rw [ite_eq_left hbad, run'_query_bind]
        simp [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map]
        simp only [traceHits_prepend, hbad, true_or]
        rw [← map_bind, OracleComp.prEvent_true_eq_one]
      · rw [ite_eq_right hbad, run'_query_bind, run'_query_bind]
        simp only [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
        apply tsum_congr
        intro result
        rw [ih result.1 result.2]
        simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
          Functor.map_map, traceHits_prepend, hbad, false_or]


end XmssSecurity.Seeded
