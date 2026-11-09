/-
# Fork-compatible formulation of the committed soundness game

To analyze the non-interactive committed soundness game with the replay
forking lemma, the game is reformulated so that the random-oracle entropy is
exposed through a single *counted* challenge oracle that the forking machinery
can rewind (mirroring `FiatShamir.Fork.runTrace` in VCVio):

* the adversary's oracles are simulated by `unifForward + roImpl`: uniform
  queries are forwarded, random-oracle queries are answered by a caching
  implementation whose cache *misses* issue a fresh query to the counted
  oracle `Unit →ₒ L` and append the queried commitment to an internal log
  (cache hits touch neither);
* the wrapped computation runs the adversary and then queries the oracle once
  more on the commitment it output, so the winning commitment's challenge is
  always cached and its first-miss position always appears in the log;
* `runTrace` records the run in a `Trace`: the adversary's output, the final
  cache and miss log, and the win verdict of the committed soundness game;
* `forkPoint` extracts the rewinding position: the index of the first miss on
  the output commitment, provided the run wins.

Repeated queries to the same commitment are collapsed by the cache to a single
counted query, so rewinding the counted oracle at the fork point replaces the
challenge of the *first* (hence every) query on the target commitment.

Benedikt Wagner's formalization (https://github.com/b-wagn/fv-pq-da), ported at 4475179c and
modified for VCVio afa6593.
-/
module

public import PqDas.Proof.CommittedSoundness.Defs
public import VCVio.CryptoFoundations.ReplayFork
public import PqDas.Defs

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PqDas

namespace CommittedSoundness

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L : Type}

/-- A cache hit returns the recorded answer and leaves the state unchanged. -/
lemma roImpl_run_hit [DecidableEq ComVC] {com : ComVC}
    {cache : (ComVC →ₒ L).QueryCache} {log : List ComVC} {v : L}
    (h : cache com = some v) :
    (roImpl ComVC L com).run (cache, log) = pure (v, cache, log) := by
  simp [roImpl, StateT.run_bind, StateT.run_get, h]

/-- A cache miss draws a fresh challenge from the counted oracle, records it,
and logs the queried commitment. -/
lemma roImpl_run_miss [DecidableEq ComVC] {com : ComVC}
    {cache : (ComVC →ₒ L).QueryCache} {log : List ComVC}
    (h : cache com = none) :
    (roImpl ComVC L com).run (cache, log) =
      (query (spec := wrappedSpec L) (Sum.inr ()) : OracleComp (wrappedSpec L) L) >>=
        fun v => pure (v, cache.cacheQuery com v, log ++ [com]) := by
  simp only [roImpl, StateT.run_bind, StateT.run_get, pure_bind, h, StateT.run_set,
    bind_assoc, StateT.run_monadLift]
  rfl

/-- If `forkPoint` selects a rewinding index, the recorded run wins. -/
lemma win_of_forkPoint_eq_some [DecidableEq ComVC] {Q : ℕ}
    {trace : Trace Λ n ComVC L} {s : Fin (Q + 1)}
    (hs : forkPoint Q trace = some s) : trace.win = true := by
  simp_all [forkPoint]

/-- If `forkPoint` selects a rewinding index, the output commitment appears in
the miss log. -/
lemma com_mem_queryLog_of_forkPoint_eq_some [DecidableEq ComVC] {Q : ℕ}
    {trace : Trace Λ n ComVC L} {s : Fin (Q + 1)}
    (hs : forkPoint Q trace = some s) : trace.com ∈ trace.queryLog := by
  simp_all [forkPoint]

/-- The index selected by `forkPoint` locates the output commitment in the
miss log. -/
lemma forkPoint_getElem?_eq_some_com [DecidableEq ComVC] {Q : ℕ}
    {trace : Trace Λ n ComVC L} {s : Fin (Q + 1)}
    (hs : forkPoint Q trace = some s) : trace.queryLog[↑s]? = some trace.com := by
  grind [forkPoint]

/-! ### Query bounds -/

/-- Structural bound on random-oracle queries of a computation in the
committed soundness adversary's oracle world: at most `Q` queries hit the
right (random-oracle) summand; uniform-sampling queries are unrestricted. -/
def HashQueryBound {α : Type}
    (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) (Q : ℕ) : Prop :=
  OracleComp.IsQueryBoundP oa (· matches .inr _) Q

@[simp]
lemma hashQueryBound_query_bind_iff {α : Type}
    (t : (unifSpec + (ComVC →ₒ L)).Domain)
    (oa : (unifSpec + (ComVC →ₒ L)).Range t → OracleComp (unifSpec + (ComVC →ₒ L)) α)
    (Q : ℕ) :
    HashQueryBound (liftM ((unifSpec + (ComVC →ₒ L)).query t) >>= oa) Q ↔
      (match t with
      | .inl _ => True
      | .inr _ => 0 < Q) ∧
      ∀ u, HashQueryBound (oa u) (match t with
        | .inl _ => Q
        | .inr _ => Q - 1) := by
  simp only [HashQueryBound, OracleComp.isQueryBoundP_query_bind_iff]
  cases t <;> simp

/-- Simulating a computation with at most `Q` random-oracle queries grows the
internal miss log by at most `Q` entries (each miss consumes one unit of the
budget; hits and uniform queries do not touch the log). -/
theorem queryLog_length_le_of_hashQueryBound [DecidableEq ComVC] {α : Type}
    {oa : OracleComp (unifSpec + (ComVC →ₒ L)) α} {Q : ℕ}
    (hQ : HashQueryBound oa Q) (st : SimState ComVC L) {z : α × SimState ComVC L}
    (hz : z ∈ support ((simulateQ (unifForward ComVC L + roImpl ComVC L) oa).run st)) :
    z.2.2.length ≤ st.2.length + Q := by
  induction oa using OracleComp.inductionOn generalizing Q st z with
  | pure x =>
      obtain rfl : z = (x, st) := by
        simpa [simulateQ_pure, StateT.run_pure, support_pure] using hz
      simp
  | query_bind t mx ih =>
      rw [hashQueryBound_query_bind_iff] at hQ
      rw [simulateQ_query_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨us, hus, hz'⟩ := hz
      cases t with
      | inl i =>
          rcases st with ⟨cache, log⟩
          obtain ⟨u, rfl⟩ : us ∈ Set.range (fun u => (u, cache, log)) := by
            simpa [QueryImpl.add_apply_inl, unifForward, support_map] using hus
          simpa using ih u (hQ.2 u) (cache, log) hz'
      | inr com =>
          rcases st with ⟨cache, log⟩
          cases hcache : cache com with
          | some v =>
              have hus' : us ∈ ({(v, cache, log)} : Set _) := by
                convert hus using 1
                simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get, hcache]
                exact Iff.rfl
              obtain rfl := Set.mem_singleton_iff.mp hus'
              have hrec : z.2.2.length ≤ log.length + (Q - 1) := by
                simpa using ih v (hQ.2 v) (cache, log) hz'
              exact le_trans hrec (Nat.add_le_add_left (Nat.sub_le _ _) _)
          | none =>
              obtain ⟨u, rfl⟩ : us ∈ Set.range (fun u : L =>
                  (u, cache.cacheQuery com u, log ++ [com])) := by
                convert hus using 1
                simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get,
                  hcache, StateT.run_set]
                exact Iff.rfl
              have hrec : z.2.2.length ≤ (log ++ [com]).length + (Q - 1) := by
                simpa using
                  ih u (hQ.2 u)
                    ((cache.cacheQuery com u : (ComVC →ₒ L).QueryCache), log ++ [com]) hz'
              have hQpos : 0 < Q := hQ.1
              simp only [List.length_append, List.length_singleton] at hrec ⊢
              lia

end CommittedSoundness

end PqDas
