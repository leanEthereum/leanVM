import Whir.DuplexRawProgram
import Whir.DuplexPublicSimulator
import Whir.WHIRObservableAllocations

/-! Source-only fuel for the actual public-log simulator. The ambient key domain
may be larger than the independently counted source. Lowering uses the existing
raw compiler and stop operation; no raw oracle is an input to the sampler.
The exact chronological trace retains repeated construction calls and omits
primitive cache hits precisely as the chosen simulator does.

`bounded_eval` rules out exhaustion at source fuel A, while
`bounded_rawAnswers` identifies the full executed answer trace with public
replay. `source_path_length_le` and `bounded_length_le` bound public and raw
request counts by A; `bounded_key_lengths` separately bounds both components
of every raw key's physical path by A, starting from any fixed private seed. -/
namespace Whir.WHIRSourceRawProgram
open FiatShamirGame DuplexFraming DuplexModeGame TypedOracleCompiler
open DuplexRefinement hiding State
open DuplexPublicSimulator
open DuplexRawProgram (compileIdeal stop)

/-- The chosen simulator spends at most one raw call per primitive; a
construction spends one, charged to its positive source path cost. -/
theorem compileIdeal_calls_le {Q : Nat} {R : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (state : State) (p : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p)
    (A : Nat) (sourceCounted : Counts A p) :
    (runRO ro (compileIdeal (simulator Q) iv state p remaining cap counted)).2 ≤ A := by
  induction p generalizing state remaining A with
  | done r => simp [compileIdeal, runRO]
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      have hr := ih (runRO ro ((simulator Q).answer state input)).1.2
        (runRO ro ((simulator Q).answer state input)).1.1
        (remaining-1) (by omega) (counted.2 _) (A-1) (sourceCounted.2 _)
      have ha := answer_queries_le_one Q ro state input
      have hc : 1 ≤ A := sourceCounted.1
      simp only [compileIdeal, DuplexRawProgram.ROProgram.run_bind,
        DuplexRawProgram.ROProgram.run_map] at ⊢
      omega
    | construction q valid =>
      have hr := ih (ro (constructionKey Q iv q (counted.1.trans cap))) state
        (remaining-pathCost q) (by omega) (counted.2 _)
        (A-pathCost q) (sourceCounted.2 _)
      have hp := DuplexRawProgram.pathCost_pos q
      have hc : pathCost q ≤ A := sourceCounted.1
      simp only [compileIdeal, runRO, DuplexRawProgram.ROProgram.run_map]
      omega

/-- Executable source sampler, with source fuel rather than ambient-domain fuel.
Both Counts witnesses concern the same source program. -/
def bounded (Q : Nat) {R : Type} (iv : Digest32) (state : State)
    (p : Program R) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining p) (A : Nat) (_sourceCounted : Counts A p) :
    Sampling (RawKey Q) (fun _ => Digest32) (Option (View R)) A :=
  stop A (compileIdeal (simulator Q) iv state p remaining cap counted)

theorem bounded_eval {Q : Nat} {R : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (state : State) (p : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p)
    (A : Nat) (sourceCounted : Counts A p) :
    Sampling.eval ro (bounded Q iv state p remaining cap counted A sourceCounted) =
      some (runIdeal (simulator Q) ro iv state p remaining cap counted).view := by
  unfold bounded
  rw [DuplexRawProgram.stop_exact ro _ _
    (compileIdeal_calls_le ro iv state p remaining cap counted A sourceCounted)]
  rw [DuplexRawProgram.run_compileIdeal]

theorem bounded_ne_exhausted {Q : Nat} {R : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (state : State) (p : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p)
    (A : Nat) (sourceCounted : Counts A p) :
    Sampling.eval ro (bounded Q iv state p remaining cap counted A sourceCounted) ≠ none := by
  rw [bounded_eval]
  exact Option.some_ne_none _

theorem requests_bind {Q : Nat} {R S : Type} (ro : RawKey Q → Digest32)
    (p : ROProgram Q R) (f : R → ROProgram Q S) :
    requests ro (DuplexRawProgram.ROProgram.bind p f) =
      requests ro p ++ requests ro (f (runRO ro p).1) := by
  induction p with
  | done r => rfl
  | ask key next ih => simp [DuplexRawProgram.ROProgram.bind, requests, runRO, ih]

theorem requests_map {Q : Nat} {R S : Type} (ro : RawKey Q → Digest32)
    (f : R → S) (p : ROProgram Q R) :
    requests ro (DuplexRawProgram.ROProgram.map f p) = requests ro p := by
  induction p with
  | done r => rfl
  | ask key next ih => simp [DuplexRawProgram.ROProgram.map, requests, ih]

theorem requests_compileIdeal {Q : Nat} {R : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (state : State) (p : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p) :
    requests ro (compileIdeal (simulator Q) iv state p remaining cap counted) =
      actualRequests ro iv state p remaining cap counted := by
  induction p generalizing state remaining with
  | done r => rfl
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [compileIdeal, requests_bind, requests_map, actualRequests]
      exact congrArg (requests ro ((simulator Q).answer state input) ++ ·)
        (ih _ _ _ _ _)
    | construction q valid =>
      simp only [compileIdeal, requests, requests_map, actualRequests]
      exact congrArg (constructionKey Q iv q (counted.1.trans cap) :: ·)
        (ih _ _ _ _ _)

/-- Generic stopping preserves the complete answer sequence whenever fuel
covers actual calls. No deduplication is performed. -/
theorem rawAnswers_stop {Q : Nat} {R : Type} (ro : RawKey Q → Digest32)
    (fuel : Nat) (p : ROProgram Q R) (enough : (runRO ro p).2 ≤ fuel) :
    WHIRObservableAllocations.rawAnswers Q ro (stop fuel p) =
      (requests ro p).map (fun key => (key,ro key)) := by
  induction fuel generalizing p with
  | zero =>
    cases p with
    | done r => rfl
    | ask key next => simp [runRO] at enough
  | succ fuel ih =>
    cases p with
    | done r => rfl
    | ask key next =>
      have h : (runRO ro (next (ro key))).2 ≤ fuel := by
        simp only [runRO] at enough
        omega
      simpa only [WHIRObservableAllocations.rawAnswers, stop, Sampling.execute,
        List.map_cons, requests] using congrArg ((key,ro key) :: ·) (ih _ h)

/-- Exact chronological raw answers, including repeated keys and the chosen
simulator's cache behavior, reconstructed only from the actual public view. -/
theorem bounded_rawAnswers {Q : Nat} {R : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (state : State) (p : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p)
    (A : Nat) (sourceCounted : Counts A p) :
    WHIRObservableAllocations.rawAnswers Q ro
      (bounded Q iv state p remaining cap counted A sourceCounted) =
      replayAnswers Q iv state.publicLog
        (runIdeal (simulator Q) ro iv state p remaining cap counted).view.observations := by
  unfold bounded
  rw [rawAnswers_stop ro _ _
    (compileIdeal_calls_le ro iv state p remaining cap counted A sourceCounted),
    requests_compileIdeal, ← replay_actual, ← replayAnswers_keys, List.map_map]
  trans List.map id (replayAnswers Q iv state.publicLog
    (runIdeal (simulator Q) ro iv state p remaining cap counted).view.observations)
  · apply List.map_congr_left
    intro entry member
    exact Prod.ext rfl (replayAnswers_consistent ro iv state p remaining cap counted entry member).symm
  · exact List.map_id _

/-- The number of public source observations is bounded independently of Q. -/
theorem source_path_length_le {Q : Nat} {R : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (state : State) (p : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p)
    (A : Nat) (sourceCounted : Counts A p) :
    (runIdeal (simulator Q) ro iv state p remaining cap counted).view.observations.length ≤ A := by
  induction p generalizing state remaining A with
  | done r => simp [runIdeal]
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      have hr := ih (runRO ro ((simulator Q).answer state input)).1.2
        (runRO ro ((simulator Q).answer state input)).1.1
        (remaining-1) (by omega) (counted.2 _) (A-1) (sourceCounted.2 _)
      have hc : 1 ≤ A := sourceCounted.1
      simp only [runIdeal, prepend, List.length_cons]
      omega
    | construction q valid =>
      have hr := ih (ro (constructionKey Q iv q (counted.1.trans cap))) state
        (remaining-pathCost q) (by omega) (counted.2 _)
        (A-pathCost q) (sourceCounted.2 _)
      have hp := DuplexRawProgram.pathCost_pos q
      have hc : pathCost q ≤ A := sourceCounted.1
      simp only [runIdeal, prepend, List.length_cons]
      omega

theorem bounded_length_le {Q : Nat} {R : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (state : State) (p : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p)
    (A : Nat) (sourceCounted : Counts A p) :
    (WHIRObservableAllocations.rawAnswers Q ro
      (bounded Q iv state p remaining cap counted A sourceCounted)).length ≤ A := by
  simp only [WHIRObservableAllocations.rawAnswers, List.length_map, bounded,
    DuplexRawProgram.execute_stop_length]
  exact Nat.min_le_left _ _

/-- Each actual raw key's physical path is source-bounded, even when Q includes
additional completion capacity. Initial private seeds are arbitrary. -/
theorem bounded_key_lengths {Q : Nat} {R : Type} (ro : RawKey Q → Digest32)
    (iv : Digest32) (seed : Seed) (p : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p)
    (A : Nat) (sourceCounted : Counts A p) :
    ∀ entry ∈ WHIRObservableAllocations.rawAnswers Q ro
      (bounded Q iv ((simulator Q).initial seed) p remaining cap counted A sourceCounted),
      entry.1.1.1.val ≤ A ∧ entry.1.2.1.val ≤ A := by
  rw [bounded_rawAnswers]
  exact replayAnswers_source_bound ro iv seed p remaining cap counted A sourceCounted

#print axioms compileIdeal_calls_le
#print axioms bounded_eval
#print axioms bounded_ne_exhausted
#print axioms bounded_rawAnswers
#print axioms source_path_length_le
#print axioms bounded_length_le
#print axioms bounded_key_lengths
end Whir.WHIRSourceRawProgram
