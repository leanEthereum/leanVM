import Whir.WHIRSourceResolver
import Whir.WHIRPublicBackfill

/-! The physical public completion of a source retains compiler-owned metadata.
Its budget is derived only on reachable compiler outputs, never on forged event
lists. Every repeated completion is charged; root metadata remains free. -/
namespace Whir.WHIRSourceBackfill
open FiatShamirGame DuplexFraming DuplexModeGame
open RawWHIRKeys (Context Packet)
open WHIRModeFinal WHIRPublicBackfill

variable {cap : Nat} {R S : Type}

/-- Public requests depend only on source-owned observations. -/
def requests (ctx : Context) (Q : Nat) (result : WHIRSourceChronology.Result cap R) : List (RawKey Q) :=
  DuplexPublicSimulator.replay Q ctx.iv [] (WHIRSourceChronology.observations result.events)

/-- The executable wrapper returns no simulator state, seed, or oracle. -/
def instrument (ctx : Context) (Q : Nat) (source : WHIRSourceChronology.Source cap R)
    (select : R → Option (Packet ctx Q)) :
    Program (WHIRPublicBackfill.Completed ctx Q (WHIRSourceChronology.Result cap R)) :=
  bind (WHIRSourceChronology.compile source)
    (fun result => backfill ctx Q result (requests ctx Q result) (select result.value))

/-- Universal over actual continuation branches, not arbitrary result values. -/
def AllResults (post : R → Prop) : Program R → Prop
  | .done r => post r
  | .ask _ next => ∀ answer, AllResults post (next answer)

theorem allResults_mono (p : Program R) (post next : R → Prop)
    (h : AllResults post p) (imp : ∀ r, post r → next r) : AllResults next p := by
  induction p with
  | done r => exact imp r h
  | ask q cont ih => exact fun d => ih d (h d)

theorem allResults_map (p : Program R) (f : R → S) (post : S → Prop) :
    AllResults post (WHIRSourceChronology.map f p) = AllResults (fun r => post (f r)) p := by
  induction p with
  | done => rfl
  | ask q next ih => simp only [WHIRSourceChronology.map, AllResults, ih]

theorem allResults_of_forall (p : Program R) (post : R → Prop) (all : ∀ result, post result) :
    AllResults post p := by
  induction p with
  | done result => exact all result
  | ask _ _ ih => exact ih

theorem allResults_and (p : Program R) (left right : R → Prop)
    (hl : AllResults left p) (hr : AllResults right p) : AllResults (fun result => left result ∧ right result) p := by
  induction p with
  | done => exact ⟨hl,hr⟩
  | ask _ _ ih => exact fun answer => ih answer (hl answer) (hr answer)

/-- Instrumentation preserves exactly which public values can be returned; metadata cannot manufacture a verifier result. -/
theorem compile_value_outputs (source : WHIRSourceChronology.Source cap R) (post : R → Prop) :
    AllResults (fun result => post result.value) (WHIRSourceChronology.compile source) ↔
      AllResults post (WHIRSourceChronology.erase source) := by
  induction source with
  | done => rfl
  | ask query next ih =>
      simp only [WHIRSourceChronology.compile,WHIRSourceChronology.erase,AllResults,allResults_map,
        WHIRSourceChronology.prepend]
      exact forall_congr' ih
  | commit root next ih =>
      simpa only [WHIRSourceChronology.compile,WHIRSourceChronology.erase,allResults_map,
        WHIRSourceChronology.prepend] using ih
  | claims profile entry request next ih =>
      simpa only [WHIRSourceChronology.compile,WHIRSourceChronology.erase,allResults_map,
        WHIRSourceChronology.prepend] using ih

theorem bind_counted_reachable (p : Program R) (next : R → Program S) (post : R → Prop)
    (a b : Nat) (before : Counts a p) (reachable : AllResults post p)
    (after : ∀ r, post r → Counts b (next r)) : Counts (a+b) (bind p next) := by
  induction p generalizing a with
  | done r => exact counts_mono (after r reachable) (by omega)
  | ask q cont ih =>
      refine ⟨by have := before.1; omega, fun d => ?_⟩
      have h := ih d (a-q.cost) (before.2 d) (reachable d)
      exact counts_mono h (by have := before.1; omega)

def observationCost (observations : List Observation) : Nat :=
  (observations.map (fun o => o.query.cost)).sum

theorem compile_outputs (source : WHIRSourceChronology.Source cap R) (A : Nat)
    (counted : WHIRSourceChronology.Counts A source) :
    AllResults (fun r => observationCost (WHIRSourceChronology.observations r.events) ≤ A)
      (WHIRSourceChronology.compile source) := by
  induction source generalizing A with
  | done r => simp [WHIRSourceChronology.compile, AllResults, WHIRSourceChronology.observations, observationCost]
  | ask q next ih =>
      intro answer
      rw [allResults_map]
      apply allResults_mono _ _ _ (ih answer (A-q.cost) (counted.2 answer))
      intro r hr
      change q.cost + observationCost (WHIRSourceChronology.observations r.events) ≤ A
      have := counted.1
      omega
  | commit root next ih =>
      simpa only [WHIRSourceChronology.compile, allResults_map,
        WHIRSourceChronology.prepend, WHIRSourceChronology.observations] using ih A counted
  | claims profile entry request next ih =>
      simpa only [WHIRSourceChronology.compile, allResults_map,
        WHIRSourceChronology.prepend, WHIRSourceChronology.observations] using ih A counted

/-- Even adversarial answer lists are bounded by their source instruction costs.
The primitive recognizer's fuel is the finite source log, not ambient Q. -/
theorem replay_bounds (Q : Nat) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog)
    (obs : List Observation) :
    (DuplexPublicSimulator.replay Q iv log obs).length ≤ observationCost obs ∧
    ∀ raw ∈ DuplexPublicSimulator.replay Q iv log obs,
      raw.1.1.val ≤ log.length + observationCost obs := by
  induction obs generalizing log with
  | nil => simp [DuplexPublicSimulator.replay, observationCost]
  | cons observation rest ih =>
      rcases observation with ⟨query,answer⟩
      cases query with
      | primitive purpose input =>
          have tail := ih (DuplexPublicSimulator.observe log input answer)
          have len : (DuplexPublicSimulator.privateKey Q log input).toList.length ≤ 1 := by
            cases DuplexPublicSimulator.privateKey Q log input <;> simp
          simp only [DuplexPublicSimulator.replay, List.length_append]
          constructor
          · simp only [observationCost, List.map_cons, List.sum_cons, Query.cost] at *
            omega
          · intro raw member
            rcases List.mem_append.mp member with member | member
            · have key : DuplexPublicSimulator.privateKey Q log input = some raw := by
                simpa only [Option.mem_toList, Option.mem_def] using member
              have h := (DuplexPublicSimulator.privateKey_lengths_log key).1
              simp only [observationCost, List.map_cons, List.sum_cons, Query.cost]
              omega
            · have h := tail.2 raw member
              simp only [DuplexPublicSimulator.observe, List.length_cons,
                observationCost, List.map_cons, List.sum_cons, Query.cost] at *
              omega
      | construction coordinate valid =>
          have tail := ih log
          have positive : 1 ≤ pathCost coordinate := by
            simp [pathCost, DuplexEncoding.plan]
          by_cases h : pathCost coordinate ≤ Q
          · simp only [DuplexPublicSimulator.replay, h, ↓reduceDIte, List.length_cons]
            constructor
            · simp only [observationCost, List.map_cons, List.sum_cons, Query.cost] at *
              omega
            · intro raw member
              rcases List.mem_cons.mp member with rfl | member
              · simp only [constructionKey, restrictKey, shortList, (modeKey_lengths iv coordinate).1,
                  observationCost, List.map_cons, List.sum_cons, Query.cost]
                omega
              · have := tail.2 raw member
                simp only [observationCost, List.map_cons, List.sum_cons, Query.cost] at *
                omega
          · simp only [DuplexPublicSimulator.replay, h, ↓reduceDIte]
            constructor
            · simp only [observationCost, List.map_cons, List.sum_cons, Query.cost] at *
              omega
            · intro raw member
              have := tail.2 raw member
              simp only [observationCost, List.map_cons, List.sum_cons, Query.cost] at *
              omega

def budget (ctx : Context) (A Mf : Nat) : Nat :=
  A + (A * (pathFactor ctx * A) + pathFactor ctx * Mf)

/-- A final path cap is needed only for reachable public outputs, so an arbitrary attacker cannot supply a fabricated accepted result merely to satisfy accounting. -/
theorem counted_reachable (ctx : Context) (Q A Mf : Nat) (source : WHIRSourceChronology.Source cap R)
    (select : R → Option (Packet ctx Q)) (before : WHIRSourceChronology.Counts A source)
    (finalPaths : AllResults
      (fun result => ∀ packet, select result = some packet →
        pathCost (RawWHIRKeys.coordinate ctx packet.val 0) ≤ Mf)
      (WHIRSourceChronology.erase source)) :
    Counts (budget ctx A Mf) (instrument ctx Q source select) := by
  have outputs := (compile_value_outputs source _).mpr finalPaths
  apply bind_counted_reachable _ _
    (fun result => observationCost (WHIRSourceChronology.observations result.events) ≤ A ∧
      ∀ packet, select result.value = some packet →
        pathCost (RawWHIRKeys.coordinate ctx packet.val 0) ≤ Mf) A _
    ((WHIRSourceChronology.compile_counted source A).mpr before)
    (allResults_and _ _ _ (compile_outputs source A before) outputs)
  intro result reachable
  apply counts_mono (backfill_counted ctx Q result _ _)
  have bounds := replay_bounds Q ctx.iv [] (WHIRSourceChronology.observations result.events)
  have paths : ∀ raw ∈ requests ctx Q result, raw.1.1.val ≤ A := by
    intro raw member
    exact (bounds.2 raw member).trans (by simpa using reachable.1)
  exact (cost_bound_pathCaps ctx Q A Mf (requests ctx Q result) (select result.value)
    paths reachable.2).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (bounds.1.trans reachable.1)) _)

/-- Source-only, noncircular physical accounting. Q is only a key-domain index;
the caller separately requires `budget ctx A Mf ≤ Q` to run the ideal mode. -/
theorem counted (ctx : Context) (Q A Mf : Nat) (source : WHIRSourceChronology.Source cap R)
    (select : R → Option (Packet ctx Q)) (before : WHIRSourceChronology.Counts A source)
    (finalPaths : ∀ r p, select r = some p → pathCost (RawWHIRKeys.coordinate ctx p.val 0) ≤ Mf) :
    Counts (budget ctx A Mf) (instrument ctx Q source select) := by
  exact counted_reachable ctx Q A Mf source select before
    (allResults_of_forall _ _ finalPaths)

/-- State-independent continuation results permit exact physical suffix composition. -/
theorem bind_ideal_result {Q : Nat} {Seed State : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State)
    (p : Program R) (next : R → Program S) (value : R → S)
    (after : ∀ r state rem (hc : rem ≤ Q) (hn : Counts rem (next r)),
      (runIdeal sim ro iv state (next r) rem hc hn).view.result = value r)
    (remaining : Nat) (limit : remaining ≤ Q) (before : Counts remaining p)
    (whole : Counts remaining (bind p next)) :
    (runIdeal sim ro iv state (bind p next) remaining limit whole).view.result =
      value (runIdeal sim ro iv state p remaining limit before).view.result := by
  induction p generalizing state remaining with
  | done r => exact after r state remaining limit whole
  | ask query cont ih =>
      cases query with
      | primitive purpose input =>
          exact ih (runRO ro (sim.answer state input)).1.2
            (runRO ro (sim.answer state input)).1.1 (remaining-1) (by omega) (before.2 _) (whole.2 _)
      | construction coordinate valid =>
          exact ih (ro (constructionKey Q iv coordinate (before.1.trans limit))) state
            (remaining-pathCost coordinate) (by omega) (before.2 _) (whole.2 _)

theorem ideal_result (ctx : Context) (Q : Nat) {Seed State : Type}
    (sim : Simulator Q Seed State) (ro : RawKey Q → Digest32) (state : State)
    (source : WHIRSourceChronology.Source cap R) (select : R → Option (Packet ctx Q))
    (remaining : Nat) (limit : remaining ≤ Q)
    (whole : Counts remaining (instrument ctx Q source select)) :
    (runIdeal sim ro ctx.iv state (instrument ctx Q source select) remaining limit whole).view.result =
      let result := (runIdeal sim ro ctx.iv state (WHIRSourceChronology.compile source) remaining limit
        (bind_prefix_counted _ (fun r => backfill ctx Q r (requests ctx Q r) (select r.value))
          remaining whole)).view.result
      ⟨result, idealRecords ctx Q ro (selections ctx Q (requests ctx Q result) (select result.value))⟩ :=
  bind_ideal_result sim ro ctx.iv state _ _ _
    (fun r state rem hc hn => backfill_ideal_result ctx Q sim ro state r _ _ rem hc hn)
    remaining limit (bind_prefix_counted _ _ remaining whole) whole

theorem real_result (ctx : Context) (Q : Nat) (oracle : PrimitiveOracle)
    (source : WHIRSourceChronology.Source cap R) (select : R → Option (Packet ctx Q)) :
    (runReal oracle ctx.iv (instrument ctx Q source select)).view.result =
      let result := (runReal oracle ctx.iv (WHIRSourceChronology.compile source)).view.result
      ⟨result, realRecords ctx Q oracle (selections ctx Q (requests ctx Q result) (select result.value))⟩ := by
  rw [instrument, bind_real_result, backfill_real_result]

/-- The public replay is exactly the original source's actual private requests,
for every chosen initial seed. Completion queries cannot enter this replay. -/
theorem requests_actual (ctx : Context) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : WHIRSourceChronology.Source cap R)
    (remaining : Nat) (limit : remaining ≤ Q)
    (before : Counts remaining (WHIRSourceChronology.compile source)) :
    requests ctx Q (runIdeal (DuplexPublicSimulator.simulator Q) ro ctx.iv
      ((DuplexPublicSimulator.simulator Q).initial seed)
      (WHIRSourceChronology.compile source) remaining limit before).view.result =
    DuplexPublicSimulator.actualRequests ro ctx.iv
      ((DuplexPublicSimulator.simulator Q).initial seed)
      (WHIRSourceChronology.compile source) remaining limit before := by
  unfold requests
  rw [WHIRSourceResolver.ideal_source_trace _ _ _ _ source remaining limit
    ((WHIRSourceChronology.compile_counted source remaining).mp before)]
  exact DuplexPublicSimulator.replay_actual ro ctx.iv
    ((DuplexPublicSimulator.simulator Q).initial seed)
    (WHIRSourceChronology.compile source) remaining limit before

theorem ideal_actual_result (ctx : Context) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : WHIRSourceChronology.Source cap R)
    (select : R → Option (Packet ctx Q)) (remaining : Nat) (limit : remaining ≤ Q)
    (whole : Counts remaining (instrument ctx Q source select)) :
    (runIdeal (DuplexPublicSimulator.simulator Q) ro ctx.iv
      ((DuplexPublicSimulator.simulator Q).initial seed)
      (instrument ctx Q source select) remaining limit whole).view.result =
      let before := bind_prefix_counted (WHIRSourceChronology.compile source)
        (fun r => backfill ctx Q r (requests ctx Q r) (select r.value)) remaining whole
      let state := (DuplexPublicSimulator.simulator Q).initial seed
      let result := (runIdeal (DuplexPublicSimulator.simulator Q) ro ctx.iv state
        (WHIRSourceChronology.compile source) remaining limit before).view.result
      ⟨result, idealRecords ctx Q ro (selections ctx Q
        (DuplexPublicSimulator.actualRequests ro ctx.iv state
          (WHIRSourceChronology.compile source) remaining limit before) (select result.value))⟩ := by
  rw [ideal_result]
  dsimp only
  rw [requests_actual]

theorem requests_replayAnswers (ctx : Context) (Q : Nat) (result : WHIRSourceChronology.Result cap R) :
    requests ctx Q result =
      (DuplexPublicSimulator.replayAnswers Q ctx.iv []
        (WHIRSourceChronology.observations result.events)).map Prod.fst :=
  (DuplexPublicSimulator.replayAnswers_keys ..).symm

private def smokeContext : Context :=
  ⟨.stack,fun _ => 0,fun _ => 1,fun _ => some (0,0),fun _ => 1,1⟩

/-- Runs the actual source compiler, public simulator, and physical wrapper.
The source performs a raw-request-producing primitive chain, a repeat, and
interleaved free commitment metadata; no final packet is selected. -/
private def smoke : IO Unit := do
  let seedNode : Node := ⟨fun _ => 41,fun _ => 0,UInt64.ofNat (2^56),true⟩
  let terminal : Node := ⟨fun _ => 7,fun _ => 0,UInt64.ofNat (6*2^56),true⟩
  let source : WHIRSourceChronology.Source 0 Digest32 :=
    .commit (fun _ => 41) (.ask (.primitive .direct seedNode) (fun _ =>
      .ask (.primitive .auxiliary terminal) (fun d =>
        .commit d (.ask (.primitive .verification terminal) (fun repeated => .done repeated)))))
  let Q := budget smokeContext 3 0 + 4096
  let select : Digest32 → Option (Packet smokeContext Q) := fun _ => none
  have sourceCounted : WHIRSourceChronology.Counts 3 source := by
    simp [source, WHIRSourceChronology.Counts, Query.cost]
  have finalPaths : ∀ r p, select r = some p →
      pathCost (RawWHIRKeys.coordinate smokeContext p.val 0) ≤ 0 := by
    intro r p h
    cases h
  let total := budget smokeContext 3 0
  if limit : total ≤ Q then
    let ro : RawKey Q → Digest32 := fun _ _ => 99
    let seed : DuplexPublicSimulator.Seed := fun _ _ => 7
    let ideal := runIdeal (DuplexPublicSimulator.simulator Q) ro smokeContext.iv
      ((DuplexPublicSimulator.simulator Q).initial seed)
      (instrument smokeContext Q source select) total limit
      (counted smokeContext Q 3 0 source select sourceCounted finalPaths)
    let real := runReal (fun n _ => if n.tweak = terminal.tweak then 99 else 7)
      smokeContext.iv (instrument smokeContext Q source select)
    let raw := requests smokeContext Q ideal.view.result.result
    unless decide (ideal.view.result.result.value = fun _ => 99) &&
        decide (real.view.result.result.value = ideal.view.result.result.value) &&
        ideal.view.result.result.events.length == 5 &&
        ideal.view.observations.length == 3 && ideal.primitiveCost == 3 &&
        real.primitiveCost == 3 && ideal.simulatorQueries == 1 &&
        raw.length == 1 && raw.all (fun key => key.1.1.val == 2) &&
        (ideal.view.result.records.map (fun record => record.history.length)) == [0,0] &&
        (real.view.result.records.map (fun record => record.history.length)) == [0,0] do
      throw (IO.userError "source backfill raw-path/repeat/metadata diagram failed")
    let fallback : WHIRSourceChronology.Source 0 Digest32 :=
      .ask (.primitive .pow terminal) WHIRSourceChronology.Source.done
    have fallbackCounted : WHIRSourceChronology.Counts 1 fallback := by
      simp [fallback, WHIRSourceChronology.Counts, Query.cost]
    have small : budget smokeContext 1 0 ≤ total := by
      dsimp [total, budget]
      omega
    let fallbackRun := runIdeal (DuplexPublicSimulator.simulator Q) ro smokeContext.iv
      ((DuplexPublicSimulator.simulator Q).initial seed)
      (instrument smokeContext Q fallback select) total limit
      (counts_mono (counted smokeContext Q 1 0 fallback select fallbackCounted finalPaths) small)
    unless decide (fallbackRun.view.result.result.value = fun _ => 7) &&
        fallbackRun.simulatorQueries == 0 && fallbackRun.primitiveCost == 1 &&
        (requests smokeContext Q fallbackRun.view.result.result).isEmpty &&
        (fallbackRun.view.result.records.map (fun record => record.history.length)) == [0] do
      throw (IO.userError "source backfill exact no-final fallback failed")
    IO.println s!"source backfill smoke: metadata=5, source calls=3, raw calls=1, raw path=2, repeat charged, empty final; source-only budget={total}, domain={Q}; fallback=7, raw calls=0"
  else
    throw (IO.userError "source-only smoke budget exceeds key domain")

#eval smoke

#print axioms counted
#print axioms ideal_actual_result
#print axioms real_result

end Whir.WHIRSourceBackfill
