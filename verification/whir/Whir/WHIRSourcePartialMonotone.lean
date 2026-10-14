import Whir.DuplexPublicSimulator
import Whir.WHIRSourceChronology
import Whir.WHIRSourceResolver

/-! Finite-cache replay is monotone for a fixed source and fixed simulator coins.
A cache extension preserves answers, not just domains: overwriting a repeated raw
key with a different digest is deliberately not an extension. Metadata recovery
includes all free instructions before the first unanswered public query.

`allocationEvents_mono` derives cursor growth from actual prepare/addGroup
operations and finite-cache consistency. `runPartial_covers_prefix` and
`replay_factor` locate the next raw allocation in the public observation stream.
`source_complete` needs only the actual finite request schedule to be cached.
The public cutoff theorem transports these private fixed-source facts through
the compiler-owned view equality; the public data contains no total oracle. -/
namespace Whir.WHIRSourcePartialMonotone
open FiatShamirGame DuplexModeGame DuplexFraming DuplexPublicSimulator
open WHIRSourceChronology

variable {Q cap : Nat} {R : Type}

def CacheExtends (old new : RawKey Q → Option Digest32) : Prop :=
  ∀ key answer, old key = some answer → new key = some answer

theorem CacheExtends.refl (cache : RawKey Q → Option Digest32) : CacheExtends cache cache :=
  fun _ _ h => h

theorem CacheExtends.trans {a b c : RawKey Q → Option Digest32}
    (ab : CacheExtends a b) (bc : CacheExtends b c) : CacheExtends a c :=
  fun key answer h => bc key answer (ab key answer h)

private theorem prefix_cons {α : Type} {a b : List α} (h : a.IsPrefix b) (x : α) :
    (x :: a).IsPrefix (x :: b) := by
  obtain ⟨rest,rfl⟩ := h
  exact ⟨rest,rfl⟩

theorem runPartialRO_mono {old new : RawKey Q → Option Digest32}
    (growth : CacheExtends old new) (p : ROProgram Q R) (result : R)
    (success : runPartialRO old p = .ok result) : runPartialRO new p = .ok result := by
  induction p with
  | done r => exact success
  | ask key next ih =>
      cases h : old key with
      | none => simp [runPartialRO,h] at success
      | some answer =>
          simpa only [runPartialRO,growth key answer h] using
            ih answer (by simpa only [runPartialRO,h] using success)

/-- Fallback C calls and primitive cache hits are ordinary successful RO programs;
this theorem does not require a new raw allocation for every observation. -/
theorem runPartial_mono {old new : RawKey Q → Option Digest32}
    (growth : CacheExtends old new) (iv : Digest32) (state : State) (p : Program R)
    (remaining : Nat) (limit : remaining ≤ Q) (counted : DuplexModeGame.Counts remaining p) :
    (runPartial old iv state p remaining limit counted).observations.IsPrefix
      (runPartial new iv state p remaining limit counted).observations := by
  induction p generalizing state remaining with
  | done r => exact ⟨[],rfl⟩
  | ask query next ih =>
      cases query with
      | primitive purpose input =>
          cases h : runPartialRO old ((simulator Q).answer state input) with
          | error key => simp [runPartial,h]
          | ok answer =>
              have hn := runPartialRO_mono growth _ answer h
              simpa only [runPartial,h,hn,prependPartial] using
                prefix_cons (ih answer.2 answer.1 (remaining-1) (by omega) (counted.2 _)) _
      | construction q valid =>
          cases h : old (constructionKey Q iv q (counted.1.trans limit)) with
          | none => simp [runPartial,h]
          | some answer =>
              simpa only [runPartial,h,growth _ answer h,prependPartial] using
                prefix_cons (ih answer state (remaining-pathCost q) (by omega) (counted.2 _)) _

/-- Free commits and claims before a pending query are retained at both cursors. -/
theorem recover_mono (source : Source cap R) {old new : List Observation}
    (prior : old.IsPrefix new) : (recover source old).events.IsPrefix (recover source new).events := by
  induction source generalizing old new with
  | done r => exact ⟨[],rfl⟩
  | ask query next ih =>
      cases old with
      | nil => simp [recover]
      | cons answer rest =>
          obtain ⟨suffix,hs⟩ := prior
          subst new
          simpa only [List.cons_append,recover,prependPrefix] using
            prefix_cons (ih answer.answer (List.prefix_append rest suffix)) _
  | commit root next ih => exact prefix_cons (ih prior) _
  | claims profile entry request next ih => exact prefix_cons (ih prior) _

theorem sourceEvents_mono {old new : RawKey Q → Option Digest32}
    (growth : CacheExtends old new) (iv : Digest32) (seed : Seed)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source) :
    (recover source (runPartial old iv ((simulator Q).initial seed) (compile source)
      Q (by omega) ((compile_counted source Q).mpr counted)).observations).events.IsPrefix
    (recover source (runPartial new iv ((simulator Q).initial seed) (compile source)
      Q (by omega) ((compile_counted source Q).mpr counted)).observations).events :=
  recover_mono source (runPartial_mono growth iv _ _ _ _ _)

theorem runPartialRO_complete (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (p : ROProgram Q R)
    (covered : ∀ key ∈ requests ro p, cache key = some (ro key)) :
    runPartialRO cache p = .ok (runRO ro p).1 := by
  induction p with
  | done r => rfl
  | ask key next ih =>
      have hit := covered key (by simp [requests])
      simpa only [runPartialRO,hit,runRO] using
        ih (ro key) (fun k hk => covered k (by simp [requests,hk]))

/-- Coverage refers only to the actual requested keys, not to a total cache. -/
theorem runPartial_complete (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State) (p : Program R)
    (remaining : Nat) (limit : remaining ≤ Q) (counted : DuplexModeGame.Counts remaining p)
    (covered : ∀ key ∈ actualRequests ro iv state p remaining limit counted,
      cache key = some (ro key)) :
    runPartial cache iv state p remaining limit counted =
      ⟨(runIdeal (simulator Q) ro iv state p remaining limit counted).view.observations,
       .ok (runIdeal (simulator Q) ro iv state p remaining limit counted).view.result⟩ := by
  induction p generalizing state remaining with
  | done r => rfl
  | ask query next ih =>
      cases query with
      | primitive purpose input =>
          have hit := runPartialRO_complete cache ro ((simulator Q).answer state input)
            (fun k hk => covered k (List.mem_append_left _ hk))
          have rest := ih (runRO ro ((simulator Q).answer state input)).1.2
            (runRO ro ((simulator Q).answer state input)).1.1 (remaining-1) (by omega)
            (counted.2 _) (fun k hk => covered k (List.mem_append_right _ hk))
          simp only [runPartial,hit,rest,prependPartial,runIdeal,DuplexModeGame.prepend]
      | construction q valid =>
          have hit := covered (constructionKey Q iv q (counted.1.trans limit)) (by simp [actualRequests])
          have rest := ih (ro (constructionKey Q iv q (counted.1.trans limit))) state
            (remaining-pathCost q) (by omega) (counted.2 _)
            (fun k hk => covered k (List.mem_cons_of_mem _ hk))
          simp only [runPartial,hit,rest,prependPartial,runIdeal,DuplexModeGame.prepend]

theorem source_complete (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (iv : Digest32) (seed : Seed)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (covered : ∀ key ∈ actualRequests ro iv ((simulator Q).initial seed) (compile source)
      Q (by omega) ((compile_counted source Q).mpr counted), cache key = some (ro key)) :
    recover source (runPartial cache iv ((simulator Q).initial seed) (compile source)
      Q (by omega) ((compile_counted source Q).mpr counted)).observations =
    completedPrefix (runIdeal (simulator Q) ro iv ((simulator Q).initial seed) (compile source)
      Q (by omega) ((compile_counted source Q).mpr counted)).view.result := by
  rw [runPartial_complete cache ro iv _ _ _ _ _ covered]
  exact recover_ideal (simulator Q) ro iv _ source Q (by omega) counted

/-- Acquiring all raw requests of an actual observation prefix reaches at least
that prefix. Deterministic fallback and repeated primitive hits need no cell. -/
theorem runPartial_covers_prefix (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32)
    (iv : Digest32) (state : State) (p : Program R)
    (remaining : Nat) (limit : remaining ≤ Q) (counted : DuplexModeGame.Counts remaining p)
    (seen : List Observation)
    (prior : seen.IsPrefix
      (runIdeal (simulator Q) ro iv state p remaining limit counted).view.observations)
    (covered : ∀ key ∈ DuplexPublicSimulator.replay Q iv state.publicLog seen,
      cache key = some (ro key)) :
    seen.IsPrefix (runPartial cache iv state p remaining limit counted).observations := by
  induction p generalizing state remaining seen with
  | done r => simpa only [runIdeal,runPartial] using prior
  | ask query next ih =>
      cases seen with
      | nil => exact List.nil_prefix
      | cons observation rest =>
          cases query with
          | primitive purpose input =>
              let answer := (runRO ro ((simulator Q).answer state input)).1
              have split : observation = ⟨.primitive purpose input,answer.2⟩ ∧
                  rest.IsPrefix (runIdeal (simulator Q) ro iv answer.1 (next answer.2)
                    (remaining-1) (by omega) (counted.2 _)).view.observations := by
                simpa only [runIdeal,DuplexModeGame.prepend,List.cons_prefix_cons] using prior
              rcases split with ⟨rfl,tail⟩
              have hit := runPartialRO_complete cache ro ((simulator Q).answer state input)
                (fun k hk => covered k (by
                  simp only [DuplexPublicSimulator.replay,answer_requests] at *
                  exact List.mem_append_left _ hk))
              have restHit : ∀ key ∈ DuplexPublicSimulator.replay Q iv answer.1.publicLog rest,
                  cache key = some (ro key) := by
                intro k hk
                apply covered k
                simp only [DuplexPublicSimulator.replay]
                apply List.mem_append_right
                simpa only [answer,answer_publicLog] using hk
              simpa only [runPartial,hit,prependPartial] using
                prefix_cons (ih answer.2 answer.1 (remaining-1) (by omega)
                  (counted.2 _) rest tail restHit) _
          | construction q valid =>
              let key := constructionKey Q iv q (counted.1.trans limit)
              have split : observation = ⟨.construction q valid,ro key⟩ ∧
                  rest.IsPrefix (runIdeal (simulator Q) ro iv state (next (ro key))
                    (remaining-pathCost q) (by omega) (counted.2 _)).view.observations := by
                simpa only [runIdeal,DuplexModeGame.prepend,List.cons_prefix_cons] using prior
              rcases split with ⟨rfl,tail⟩
              have hq : pathCost q ≤ Q := counted.1.trans limit
              have hit : cache key = some (ro key) := covered key (by
                simp [DuplexPublicSimulator.replay,hq,key])
              have restHit : ∀ k ∈ DuplexPublicSimulator.replay Q iv state.publicLog rest,
                  cache k = some (ro k) := by
                intro k hk
                exact covered k (by simp [DuplexPublicSimulator.replay,hq,hk])
              dsimp only [key] at hit
              simpa only [runPartial,hit,prependPartial] using
                prefix_cons (ih (ro key) state (remaining-pathCost q) (by omega)
                  (counted.2 _) rest tail restHit) _

theorem addGroup_cacheExtends (ctx : RawWHIRKeys.Context) (ro : RawKey Q → Digest32)
    (state : CausalBindingState.State cap)
    (agrees : WHIRSourceRawCache.LogAgrees ro (state.rawAnswers Q))
    (group : RawOracleCoupling.Concrete.GroupKey ctx Q) :
    CacheExtends (WHIRSourceRawCache.cache Q state)
      (WHIRSourceRawCache.cache Q (WHIRSourceRawCache.addGroup ctx Q state group
        ((RawOracleCoupling.Concrete.partition ctx Q).split ro group))) :=
  WHIRSourceRawCache.cache_addGroup_preserves ctx Q ro state agrees group

theorem cache_eq_of_raw_eq (left right : CausalBindingState.State cap)
    (same : right.rawAnswers = left.rawAnswers) :
    WHIRSourceRawCache.cache Q right = WHIRSourceRawCache.cache Q left := by
  simp only [WHIRSourceRawCache.cache,same]

/-- Preparation and bookkeeping replay do not allocate raw replies. -/
theorem replay_cache (state : CausalBindingState.State cap) (events : List (Event cap)) :
    WHIRSourceRawCache.cache Q (WHIRSourceObserver.replayTracked state events) =
      WHIRSourceRawCache.cache Q state :=
  cache_eq_of_raw_eq _ _ (WHIRSourceRawCache.replayTracked_raw state events)

theorem prepare_cache (registry : WHIRCallerRegistry.Public) (seed : Seed)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state : CausalBindingState.State cap)
    (key : RawOracleCoupling.Concrete.AllocationKey (WHIRCallerRegistry.context registry) Q) :
    WHIRSourceRawCache.cache Q
      (WHIRCausalRawROM.prepare (WHIRCallerRegistry.context registry) rfl Q cap
        (WHIRSourceResolver.privateResolver registry Q seed source counted) state key).1 =
      WHIRSourceRawCache.cache Q state :=
  cache_eq_of_raw_eq _ _ (WHIRSourceResolver.privatePrepare_raw registry Q seed source counted state key)

theorem privateEvents_mono {old new : RawKey Q → Option Digest32}
    (growth : CacheExtends old new) (iv : Digest32) (seed : Seed)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source) :
    (WHIRSourceObserver.privateEvents Q iv old seed source counted).IsPrefix
      (WHIRSourceObserver.privateEvents Q iv new seed source counted) :=
  sourceEvents_mono growth iv seed source counted

/-- The public cutoff inherits monotonicity on the actual compiler-owned view;
neither a source machine nor a total oracle is stored in that view. -/
theorem publicEvents_mono {old new : RawKey Q → Option Digest32}
    (growth : CacheExtends old new) (ro : RawKey Q → Digest32)
    (oldAgrees : CacheAgrees old ro) (newAgrees : CacheAgrees new ro)
    (iv : Digest32) (seed : Seed) (source : Source cap R)
    (counted : WHIRSourceChronology.Counts Q source) :
    let view := (runIdeal (simulator Q) ro iv ((simulator Q).initial seed) (compile source)
      Q (by omega) ((compile_counted source Q).mpr counted)).view
    (WHIRSourceObserver.publicEvents Q iv old view).IsPrefix
      (WHIRSourceObserver.publicEvents Q iv new view) := by
  dsimp only
  rw [WHIRSourceObserver.publicEvents_actual Q iv old ro oldAgrees seed source counted,
      WHIRSourceObserver.publicEvents_actual Q iv new ro newAgrees seed source counted]
  exact privateEvents_mono growth iv seed source counted

/-- At most one raw request is emitted by a public observation. -/
def queryKey (Q : Nat) (iv : Digest32) (log : PublicLog) : Query → Option (RawKey Q)
  | .primitive _ input => privateKey Q log input
  | .construction q _ => if h : pathCost q ≤ Q then some (constructionKey Q iv q h) else none

theorem replay_cons (iv : Digest32) (log : PublicLog) (observation : Observation)
    (rest : List Observation) :
    DuplexPublicSimulator.replay Q iv log (observation :: rest) =
      (queryKey Q iv log observation.query).toList ++
        DuplexPublicSimulator.replay Q iv (finalLog log [observation]) rest := by
  rcases observation with ⟨query,answer⟩
  cases query with
  | primitive => rfl
  | construction q valid =>
      by_cases h : pathCost q ≤ Q <;>
        simp [DuplexPublicSimulator.replay,queryKey,finalLog,h]

/-- Locate an actual raw request at its emitting public query, retaining every
preceding fallback/cache-hit observation even though it emitted no request. -/
theorem replay_factor (iv : Digest32) (log : PublicLog) (observations : List Observation)
    (prior : List (RawKey Q)) (current : RawKey Q) (rest : List (RawKey Q))
    (schedule : DuplexPublicSimulator.replay Q iv log observations = prior ++ current :: rest) :
    ∃ before observation after,
      observations = before ++ observation :: after ∧
      DuplexPublicSimulator.replay Q iv log before = prior ∧
      queryKey Q iv (finalLog log before) observation.query = some current := by
  induction observations generalizing log prior with
  | nil => simp [DuplexPublicSimulator.replay] at schedule
  | cons observation tail ih =>
      rw [replay_cons] at schedule
      cases key : queryKey Q iv log observation.query with
      | none =>
          simp only [key,Option.toList_none,List.nil_append] at schedule
          obtain ⟨before,emitter,after,split,replayed,origin⟩ :=
            ih (finalLog log [observation]) prior schedule
          refine ⟨observation :: before,emitter,after,by simp [split],?_,?_⟩
          · rw [replay_cons,key]
            exact replayed
          · cases observation with
            | mk query answer => cases query <;> exact origin
      | some raw =>
          simp only [key,Option.toList_some,List.cons_append,List.nil_append] at schedule
          cases prior with
          | nil =>
              have equal : raw = current := (List.cons.inj schedule).1
              exact ⟨[],observation,tail,rfl,rfl,by simpa only [finalLog,equal] using key⟩
          | cons first prior =>
              have equal : raw = first := (List.cons.inj schedule).1
              obtain ⟨before,emitter,after,split,replayed,origin⟩ :=
                ih (finalLog log [observation]) prior (List.cons.inj schedule).2
              refine ⟨observation :: before,emitter,after,by simp [split],?_,?_⟩
              · rw [replay_cons,key]
                simp only [Option.toList_some,List.cons_append,List.nil_append,equal,replayed]
              · cases observation with
                | mk query answer => cases query <;> exact origin

/-- One actual resolver allocation advances the source cursor. The premise is
finite cache/table consistency, never an assumed cursor monotonicity invariant. -/
theorem allocationEvents_mono (registry : WHIRCallerRegistry.Public) (ro : RawKey Q → Digest32)
    (seed : Seed) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state : CausalBindingState.State cap)
    (agrees : WHIRSourceRawCache.LogAgrees ro (state.rawAnswers Q))
    (key : RawOracleCoupling.Concrete.AllocationKey (WHIRCallerRegistry.context registry) Q) :
    let prepared := (WHIRCausalRawROM.prepare (WHIRCallerRegistry.context registry) rfl Q cap
      (WHIRSourceResolver.privateResolver registry Q seed source counted) state key).1
    let next := (WHIRSourceResolver.after registry Q prepared key
      ((RawOracleCoupling.Concrete.partition (WHIRCallerRegistry.context registry) Q).split ro key.1)).state
    (WHIRSourceObserver.privateEvents Q registry.iv (WHIRSourceRawCache.cache Q state)
      seed source counted).IsPrefix
    (WHIRSourceObserver.privateEvents Q registry.iv (WHIRSourceRawCache.cache Q next)
      seed source counted) := by
  dsimp only
  apply privateEvents_mono
  rw [← prepare_cache registry seed source counted state key]
  apply addGroup_cacheExtends
  simpa only [WHIRSourceResolver.privatePrepare_raw] using agrees

-- Executable source progression: no total cache and no fabricated cache misses.
#eval show IO Unit from do
  let digest (n : Nat) : Digest32 := fun _ => ⟨n % 256,Nat.mod_lt _ (by decide)⟩
  let block : DuplexRefinement.Block64 := fun i => ⟨i.val,by omega⟩
  let seedNode : Node := ⟨digest 41,block,UInt64.ofNat (2^56),true⟩
  let internal : Node := ⟨digest 41,block,UInt64.ofNat (2*2^56+17),true⟩
  let terminal : Node := ⟨digest 2,block,UInt64.ofNat (6*2^56+23),true⟩
  let seed : Seed := fun n => if isSeed n then n.cv else digest 2
  let coordinate : Coordinate := ⟨⟨digest 0,digest 1,[]⟩,.output 0⟩
  have valid : DuplexEncoding.Admissible coordinate := by
    simp [coordinate,DuplexEncoding.Admissible,DuplexEncoding.TerminalValid]
  let source : Source 0 Digest32 :=
    .commit (digest 10) (.ask (.primitive .direct seedNode) (fun _ =>
    .ask (.primitive .auxiliary internal) (fun _ =>
    .commit (digest 11) (.ask (.primitive .verification terminal) (fun _ =>
    .commit (digest 12) (.ask (.primitive .pow terminal) (fun _ =>
    .ask (.construction coordinate valid) (fun _ =>
    .commit (digest 13) (.ask (.construction coordinate valid) Source.done)))))))))
  have counted : WHIRSourceChronology.Counts 16 source := by
    simp [source,WHIRSourceChronology.Counts,Query.cost,pathCost,DuplexEncoding.plan,coordinate]
  let ro : RawKey 16 → Digest32 := fun _ => digest 99
  let initial := (simulator 16).initial seed
  let keys : List (RawKey 16) := actualRequests ro (digest 0) initial (compile source) 16 (by omega)
    ((compile_counted source 16).mpr counted)
  let finiteCache (n : Nat) : RawKey 16 → Option Digest32 :=
    fun key => if key ∈ keys.take n then some (ro key) else none
  let progress (n : Nat) := runPartial (finiteCache n) (digest 0) initial (compile source)
    16 (by omega) ((compile_counted source 16).mpr counted)
  let a := progress 0
  let b := progress 1
  let c := progress 2
  let commits (events : List (Event 0)) : List Nat := events.filterMap (fun (e : Event 0) =>
    match e with | .commit root => some (root ⟨0,by decide⟩).val | _ => none)
  let checks : List (String × Bool) := [
    ("actual repeated raw schedule",keys.length == 3 &&
      decide ((keys[1]? : Option (RawKey 16)) = keys[2]?)),
    ("fallbacks reach first missing terminal",a.observations.length == 2 &&
      commits (recover source a.observations).events == [10,11]),
    ("primitive hit advances between raw queries",b.observations.length == 4 &&
      commits (recover source b.observations).events == [10,11,12]),
    ("finite two-key cache completes repeated construction",c.observations.length == 6 &&
      commits (recover source c.observations).events == [10,11,12,13] &&
      decide ((recover source c.observations).value = some (digest 99)))]
  for (name,ok) in checks do
    if !ok then throw (IO.userError s!"source partial replay smoke failed: {name}")
    IO.println s!"source partial replay: {name}: true"

end Whir.WHIRSourcePartialMonotone
