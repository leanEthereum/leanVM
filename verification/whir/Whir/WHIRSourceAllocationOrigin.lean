import Whir.WHIRObservableAllocations

/-! Causal origins of the actual allocation compiler's emitted trace.

`compile_origin` associates every fresh allocation with the first uncovered
query on the executed raw path, or with final completion after that path is
covered. Its witness is the exact replay prefix, including cache hits.
`compile_prefix_recorded` derives dependency closure at that prefix, while
`replay_cached` locates every cached answer in the already-emitted trace.
No source coverage or allocation-origin certificate is an input. The generic
source path can be instantiated with `WHIRSourceRawProgram.bounded_rawAnswers`;
the resolver's finite raw-cache transport is deliberately a separate layer.
-/

namespace Whir.WHIRSourceAllocationOrigin
open TypedOracleCompiler TypedFiatShamirGame RawOracleCoupling
open RawOracleCoupling.Concrete FiatShamirGame DuplexModeGame
open RawWHIRKeys (Context Packet)
open WHIRObservableAllocations WHIRPublicBackfill

section Replay
universe u
variable {Key : Type u} {Answer : Key → Type u} [DecidableEq Key]
variable (deps : Key → List Key) (table : (key : Key) → Answer key)

theorem replay_growth (keys : List Key) (cache : Cache Key Answer) :
    Growth cache (tableReplay deps table keys cache).1 := by
  induction keys generalizing cache with
  | nil => exact growth_refl _
  | cons key keys ih =>
    cases hit : cache key with
    | some answer => simpa only [tableReplay, hit] using ih cache
    | none =>
      simpa only [tableReplay, hit] using
        growth_trans (growth_put cache key (table key) hit) (ih (put cache key (table key)))

theorem replay_covered (keys : List Key) (cache : Cache Key Answer) :
    ∀ key ∈ keys, ∃ answer, (tableReplay deps table keys cache).1 key = some answer := by
  induction keys generalizing cache with
  | nil => intro key member; cases member
  | cons key keys ih =>
    intro wanted member
    cases hit : cache key with
    | some answer =>
      simp only [tableReplay, hit]
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨answer, replay_growth deps table keys cache wanted answer hit⟩
      · exact ih cache wanted member
    | none =>
      simp only [tableReplay, hit]
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨table wanted, replay_growth deps table keys (put cache wanted (table wanted))
          wanted (table wanted) (put_self _ _ _)⟩
      · exact ih (put cache key (table key)) wanted member

theorem replay_append (left right : List Key) (cache : Cache Key Answer) :
    tableReplay deps table (left ++ right) cache =
      let a := tableReplay deps table left cache
      let b := tableReplay deps table right a.1
      (b.1, a.2 ++ b.2) := by
  induction left generalizing cache with
  | nil => rfl
  | cons key keys ih =>
    cases hit : cache key with
    | some answer => simpa only [List.cons_append, tableReplay, hit] using ih cache
    | none => simp only [List.cons_append, tableReplay, hit, ih, List.cons_append]

/-- A concrete allocation determines an exact request prefix and the actual
memo-cache just before the allocation, including all preceding cache hits. -/
theorem replay_origin (keys : List Key) (cache : Cache Key Answer)
    (before after : List (Sigma (AnnotatedAnswer (Answer := Answer))))
    (entry : Sigma (AnnotatedAnswer (Answer := Answer)))
    (trace : (tableReplay deps table keys cache).2 = before ++ entry :: after) :
    ∃ left right, keys = left ++ entry.1.1 :: right ∧
      (tableReplay deps table left cache).2 = before ∧
      (tableReplay deps table left cache).1 entry.1.1 = none ∧
      entry.1.2 = dependencyHistory deps (tableReplay deps table left cache).1 entry.1.1 ∧
      entry.2 = table entry.1.1 := by
  induction keys generalizing cache before with
  | nil => simp [tableReplay] at trace
  | cons key keys ih =>
    cases hit : cache key with
    | some answer =>
      simp only [tableReplay, hit] at trace
      obtain ⟨left,right,split,hprefix,miss,history,value⟩ := ih cache before trace
      refine ⟨key :: left,right,?_,?_,?_,?_,value⟩
      · simp only [List.cons_append, split]
      · simpa only [tableReplay, hit] using hprefix
      · simpa only [tableReplay, hit] using miss
      · simpa only [tableReplay, hit] using history
    | none =>
      simp only [tableReplay, hit] at trace
      cases before with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at trace
        have he := trace.1
        subst entry
        exact ⟨[],keys,rfl,rfl,hit,rfl,rfl⟩
      | cons first before =>
        simp only [List.cons_append, List.cons.injEq] at trace
        obtain ⟨left,right,split,hprefix,miss,history,value⟩ :=
          ih (put cache key (table key)) before trace.2
        refine ⟨key :: left,right,?_,?_,?_,?_,value⟩
        · simp only [List.cons_append, split]
        · simp only [tableReplay, hit, hprefix, trace.1]
        · simpa only [tableReplay, hit] using miss
        · simpa only [tableReplay, hit] using history

/-- Executed scheduling invariant: every fresh draw has its dependencies ready. -/
def SafeKeys : List Key → Cache Key Answer → Prop
  | [], _ => True
  | key :: rest, cache =>
    match cache key with
    | some _ => SafeKeys rest cache
    | none => Ready deps cache key ∧ SafeKeys rest (put cache key (table key))

theorem safeKeys_execute {R : Type u} {n} (p : Sampling Key Answer R n)
    (cache : Cache Key Answer) (consistent : Consistent table cache)
    {post : R × Cache Key Answer → Prop} (safe : Safe deps post p cache) :
    SafeKeys deps table ((Sampling.execute table p).2.map Sigma.fst) cache := by
  induction p generalizing cache with
  | ret => trivial
  | draw key next ih =>
    simp only [Sampling.execute, List.map_cons, SafeKeys]
    cases hit : cache key with
    | some answer =>
      have equal := consistent key answer hit
      rw [equal]
      exact ih answer cache consistent (by simpa only [Safe,hit] using safe)
    | none =>
      have hs : Ready deps cache key ∧
          ∀ answer, Safe deps post (next answer) (put cache key answer) := by
        simpa only [Safe,hit] using safe
      exact ⟨hs.1,ih (table key) _ (consistent.put key) (hs.2 (table key))⟩

theorem safeKeys_prefix (left right : List Key) (cache : Cache Key Answer)
    (safe : SafeKeys deps table (left ++ right) cache) :
    SafeKeys deps table left cache := by
  induction left generalizing cache with
  | nil => trivial
  | cons key keys ih =>
    cases hit : cache key with
    | some answer =>
      simp only [List.cons_append, SafeKeys, hit] at safe ⊢
      exact ih cache safe
    | none =>
      simp only [List.cons_append, SafeKeys, hit] at safe ⊢
      exact ⟨safe.1,ih _ safe.2⟩

theorem replay_recorded (keys : List Key) (cache : Cache Key Answer)
    (before : List (Sigma (AnnotatedAnswer (Answer := Answer))))
    (recorded : Recorded deps cache before) (safe : SafeKeys deps table keys cache) :
    Recorded deps (tableReplay deps table keys cache).1
      (before ++ (tableReplay deps table keys cache).2) := by
  induction keys generalizing cache before with
  | nil => simpa only [tableReplay,List.append_nil] using recorded
  | cons key keys ih =>
    cases hit : cache key with
    | some answer =>
      simp only [tableReplay,hit]
      exact ih cache before recorded (by simpa only [SafeKeys,hit] using safe)
    | none =>
      have hs : Ready deps cache key ∧ SafeKeys deps table keys (put cache key (table key)) := by
        simpa only [SafeKeys,hit] using safe
      have step := ih (put cache key (table key))
        (before ++ [⟨(key,dependencyHistory deps cache key),table key⟩])
        (Recorded.insert deps recorded hs.1 hit (table key)) hs.2
      simpa only [tableReplay,hit,List.append_assoc,List.singleton_append] using step

/-- Every cache hit is either inherited or emitted by this exact replay. -/
theorem replay_cache_origin (keys : List Key) (cache : Cache Key Answer)
    (key : Key) (answer : Answer key)
    (hit : (tableReplay deps table keys cache).1 key = some answer) :
    cache key = some answer ∨ ∃ history,
      (⟨(key,history),answer⟩ : Sigma (AnnotatedAnswer (Answer := Answer))) ∈
        (tableReplay deps table keys cache).2 := by
  induction keys generalizing cache with
  | nil => exact Or.inl hit
  | cons current keys ih =>
    cases known : cache current with
    | some value =>
      simp only [tableReplay,known] at hit ⊢
      exact ih cache hit
    | none =>
      simp only [tableReplay,known] at hit ⊢
      rcases ih (put cache current (table current)) hit with inherited | ⟨history,member⟩
      · by_cases equal : key = current
        · subst current
          have equalAnswer : table key = answer := by simpa only [put_self,Option.some.injEq] using inherited
          right
          exact ⟨dependencyHistory deps cache key,by simp [equalAnswer]⟩
        · left
          simpa only [put_other _ _ _ _ equal] using inherited
      · exact Or.inr ⟨history,List.mem_cons_of_mem _ member⟩

theorem replay_cached (keys : List Key) (key : Key) (answer : Answer key)
    (hit : (tableReplay deps table keys (fun _ => none)).1 key = some answer) :
    ∃ history, (⟨(key,history),answer⟩ : Sigma (AnnotatedAnswer (Answer := Answer))) ∈
      (tableReplay deps table keys (fun _ => none)).2 := by
  rcases replay_cache_origin deps table keys (fun _ => none) key answer hit with impossible | member
  · cases impossible
  · exact member
end Replay

/-- Split an occurrence in the flattened compiler schedule without deduplicating
the initiating raw path. The prefix statement records chronological coverage. -/
theorem flatMap_origin {A B : Type} (f : A → List B) (raws : List A)
    (terminal before after : List B) (key : B)
    (split : raws.flatMap f ++ terminal = before ++ key :: after) :
    (∃ prior current rest, raws = prior ++ current :: rest ∧ key ∈ f current ∧
      (prior.flatMap f).IsPrefix before) ∨
    (key ∈ terminal ∧ (raws.flatMap f).IsPrefix before) := by
  induction raws generalizing before with
  | nil =>
    right
    refine ⟨?_,⟨before,rfl⟩⟩
    simp only [List.flatMap_nil, List.nil_append] at split
    rw [split]
    simp
  | cons raw raws ih =>
    simp only [List.flatMap_cons, List.append_assoc] at split
    rcases List.append_eq_append_iff.mp split with ⟨middle,front,back⟩ | ⟨middle,front,back⟩
    · rcases ih middle back with ⟨prior,current,rest,path,member,hprior⟩ | ⟨member,hprior⟩
      · left
        refine ⟨raw :: prior,current,rest,?_,member,?_⟩
        · simp [path]
        · obtain ⟨suffix,hsuffix⟩ := hprior
          exact ⟨suffix,by simp only [List.flatMap_cons, List.append_assoc, hsuffix, front]⟩
      · right
        refine ⟨member,?_⟩
        obtain ⟨suffix,hsuffix⟩ := hprior
        exact ⟨suffix,by simp only [List.flatMap_cons, List.append_assoc, hsuffix, front]⟩
    · cases middle with
      | nil =>
        simp only [List.append_nil] at front
        simp only [List.nil_append] at back
        rcases ih [] back.symm with ⟨prior,current,rest,path,member,hprior⟩ | ⟨member,hprior⟩
        · left
          refine ⟨raw :: prior,current,rest,by simp [path],member,?_⟩
          obtain ⟨suffix,hsuffix⟩ := hprior
          exact ⟨suffix,by simp only [List.flatMap_cons, List.append_assoc, hsuffix,
            List.append_nil, front]⟩
        · right
          obtain ⟨suffix,hsuffix⟩ := hprior
          exact ⟨member, suffix,by simp only [List.flatMap_cons, List.append_assoc,
            hsuffix, List.append_nil, front]⟩
      | cons head middle =>
        simp only [List.cons_append, List.cons.injEq] at back
        left
        refine ⟨[],raw,raws,rfl,?_,⟨before,rfl⟩⟩
        rw [front,← back.1]
        simp

private instance (ctx : Context) (Q : Nat) : DecidableEq (GroupKey ctx Q) := inferInstance

/-- Compiler-owned causal stage for every concrete fresh allocation. Earlier
raw requests are covered by the actual memo cache, not by a supplied certificate. -/
theorem allocation_origin (ctx : Context) (Q : Nat)
    (table : RawKey Q → Digest32) (raws : List (RawKey Q)) (final : Option (Packet ctx Q))
    (before after : List (Sigma (AllocationAnswer ctx Q))) (entry : Sigma (AllocationAnswer ctx Q))
    (trace : (tableReplay (dependencyKeys ctx Q) ((partition ctx Q).split table)
      (allocationRequests ctx Q raws final) (fun _ => none)).2 = before ++ entry :: after) :
    ∃ keys, let cache := (tableReplay (dependencyKeys ctx Q) ((partition ctx Q).split table)
        keys (fun _ => none)).1
      (tableReplay (dependencyKeys ctx Q) ((partition ctx Q).split table) keys
        (fun _ => none)).2 = before ∧ cache entry.1.1 = none ∧
      entry.1.2 = dependencyHistory (dependencyKeys ctx Q) cache entry.1.1 ∧
      entry.2 = (partition ctx Q).split table entry.1.1 ∧
      ((∃ prior current rest, raws = prior ++ current :: rest ∧
        entry.1.1 ∈ requestKeys ctx Q current ∧
        ∀ raw ∈ prior, ∀ key ∈ requestKeys ctx Q raw, ∃ answer, cache key = some answer) ∨
      (entry.1.1 ∈ finalKeys ctx Q final ∧
        ∀ raw ∈ raws, ∀ key ∈ requestKeys ctx Q raw, ∃ answer, cache key = some answer)) := by
  obtain ⟨keys,suffix,split,hprefix,miss,history,value⟩ :=
    replay_origin (dependencyKeys ctx Q) ((partition ctx Q).split table) _ (fun _ => none)
      before after entry trace
  refine ⟨keys,hprefix,miss,history,value,?_⟩
  rcases flatMap_origin (requestKeys ctx Q) raws (finalKeys ctx Q final) keys suffix
    entry.1.1 split with ⟨prior,current,rest,path,member,hprior⟩ | ⟨member,hprior⟩
  · left
    refine ⟨prior,current,rest,path,member,?_⟩
    intro raw hraw key hkey
    exact replay_covered _ _ keys _ key
      (List.IsPrefix.mem (List.mem_flatMap.mpr ⟨raw,hraw,hkey⟩) hprior)
  · right
    refine ⟨member,?_⟩
    intro raw hraw key hkey
    exact replay_covered _ _ keys _ key
      (List.IsPrefix.mem (List.mem_flatMap.mpr ⟨raw,hraw,hkey⟩) hprior)

/-- Dependency closure holds at every actual request prefix, not just at the
end of compilation. In particular, a cached packet cannot introduce new
dependencies when another block or a repeated request warms that packet. -/
theorem compile_prefix_recorded (ctx : Context) (Q : Nat) {R : Type} {n}
    (table : RawKey Q → Digest32) (final : R → Option (Packet ctx Q))
    (p : Sampling (RawKey Q) (fun _ => Digest32) R n)
    (keys suffix : List (GroupKey ctx Q))
    (split : allocationRequests ctx Q ((Sampling.execute table p).2.map Sigma.fst)
      (final (Sampling.eval table p)) = keys ++ suffix) :
    Recorded (dependencyKeys ctx Q)
      (tableReplay (dependencyKeys ctx Q) ((partition ctx Q).split table) keys (fun _ => none)).1
      (tableReplay (dependencyKeys ctx Q) ((partition ctx Q).split table) keys (fun _ => none)).2 := by
  have safe := safeKeys_execute (dependencyKeys ctx Q) ((partition ctx Q).split table)
    ((partition ctx Q).program (schedule ctx Q) (callerPlan ctx Q) final p) (fun _ => none)
    (by intro key answer hit; cases hit)
    ((partition ctx Q).safe_program (schedule ctx Q) (callerPlan ctx Q)
      (schedule_ordered ctx Q) (caller_coherent ctx Q) final p (fun _ => none))
  rw [program_keys,split] at safe
  exact replay_recorded _ _ keys (fun _ => none) [] (recorded_empty _)
    (safeKeys_prefix _ _ keys suffix _ safe)

/-- Cached recognized packets cover their entire real dependency/caller
completion; cache hits never cause a novel dependency allocation. -/
theorem cached_completion (ctx : Context) (Q : Nat)
    (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q))
    (trace : List (Sigma (AllocationAnswer ctx Q)))
    (recorded : Recorded (dependencyKeys ctx Q) cache trace)
    (packet : Packet ctx Q) (answer : GroupAnswer ctx Q (.inl packet))
    (hit : cache (.inl packet) = some answer) :
    ∀ key ∈ completionKeys ctx Q packet, ∃ value, cache key = some value := by
  intro key member
  rcases List.mem_append.mp member with dependency | self
  · exact (recorded (.inl packet) answer hit).1 key dependency
  · have equal : key = .inl packet := List.mem_singleton.mp self
    subst key
    exact ⟨answer,hit⟩


/-- A source query is covered precisely when its actual partition group is
available. This definition preserves repeated raw requests and block indices. -/
def RawCovered (ctx : Context) (Q : Nat)
    (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q)) (raw : RawKey Q) : Prop :=
  match recognized : RawWHIRKeys.recognize ctx Q raw with
  | some pos => ∃ answer, cache (.inl pos.1) = some answer
  | none => ∃ answer, cache (.inr ⟨raw,recognized⟩) = some answer

theorem request_covered (ctx : Context) (Q : Nat)
    (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q)) (raw : RawKey Q)
    (covered : ∀ key ∈ requestKeys ctx Q raw, ∃ answer, cache key = some answer) :
    RawCovered ctx Q cache raw := by
  unfold RawCovered
  split
  · rename_i pos recognized
    apply covered (.inl pos.1)
    rw [requestKeys_some ctx Q raw pos recognized]
    simp [completionKeys]
  · rename_i recognized
    apply covered (.inr ⟨raw,recognized⟩)
    rw [requestKeys_none ctx Q raw recognized]
    simp

theorem fresh_request_uncovered (ctx : Context) (Q : Nat)
    (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q))
    (trace : List (Sigma (AllocationAnswer ctx Q)))
    (recorded : Recorded (dependencyKeys ctx Q) cache trace)
    (raw : RawKey Q) (key : GroupKey ctx Q)
    (member : key ∈ requestKeys ctx Q raw) (miss : cache key = none) :
    ¬ RawCovered ctx Q cache raw := by
  unfold RawCovered
  split
  · rename_i pos recognized
    intro ⟨answer,hit⟩
    rw [requestKeys_some ctx Q raw pos recognized] at member
    obtain ⟨value,hvalue⟩ := cached_completion ctx Q cache trace recorded pos.1 answer hit key member
    rw [miss] at hvalue
    cases hvalue
  · rename_i recognized
    rw [requestKeys_none ctx Q raw recognized] at member
    have equal : key = .inr ⟨raw,recognized⟩ := List.mem_singleton.mp member
    subst key
    intro ⟨answer,hit⟩
    rw [miss] at hit
    cases hit

/-- Exact all-table compiler provenance. Its stage is the first still-uncovered
raw request, or the selected final completion after all source requests. -/
theorem compile_origin (ctx : Context) (Q : Nat) {R : Type} {n}
    (table : RawKey Q → Digest32) (final : R → Option (Packet ctx Q))
    (p : Sampling (RawKey Q) (fun _ => Digest32) R n)
    (before after : List (Sigma (AllocationAnswer ctx Q))) (entry : Sigma (AllocationAnswer ctx Q))
    (trace : (Sampling.execute (WHIRObservableAllocations.allocationOracle ctx Q table)
      (RawOracleCoupling.Concrete.compile ctx Q final p)).2 = before ++ entry :: after) :
    ∃ keys suffix, let cache := (tableReplay (dependencyKeys ctx Q) ((partition ctx Q).split table)
        keys (fun _ => none)).1
      allocationRequests ctx Q ((Sampling.execute table p).2.map Sigma.fst)
        (final (Sampling.eval table p)) = keys ++ entry.1.1 :: suffix ∧
      (tableReplay (dependencyKeys ctx Q) ((partition ctx Q).split table) keys
        (fun _ => none)).2 = before ∧ cache entry.1.1 = none ∧
      entry.1.2 = dependencyHistory (dependencyKeys ctx Q) cache entry.1.1 ∧
      entry.2 = (partition ctx Q).split table entry.1.1 ∧
      Recorded (dependencyKeys ctx Q) cache before ∧
      ((∃ prior current rest, (Sampling.execute table p).2.map Sigma.fst = prior ++ current :: rest ∧
        entry.1.1 ∈ requestKeys ctx Q current ∧ ¬ RawCovered ctx Q cache current ∧
        ∀ raw ∈ prior, RawCovered ctx Q cache raw) ∨
      (entry.1.1 ∈ finalKeys ctx Q (final (Sampling.eval table p)) ∧
        ∀ raw ∈ (Sampling.execute table p).2.map Sigma.fst, RawCovered ctx Q cache raw)) := by
  rw [compile_execution] at trace
  have path : (WHIRObservableAllocations.rawAnswers Q table p).map Prod.fst =
      (Sampling.execute table p).2.map Sigma.fst := by
    simp [WHIRObservableAllocations.rawAnswers,List.map_map]
  simp only [path] at trace
  obtain ⟨keys,suffix,split,hprefix,miss,history,value⟩ :=
    replay_origin (dependencyKeys ctx Q) ((partition ctx Q).split table) _ (fun _ => none)
      before after entry trace
  have recorded := compile_prefix_recorded ctx Q table final p keys (entry.1.1 :: suffix) split
  rw [hprefix] at recorded
  refine ⟨keys,suffix,split,hprefix,miss,history,value,recorded,?_⟩
  rcases flatMap_origin (requestKeys ctx Q) ((Sampling.execute table p).2.map Sigma.fst)
    (finalKeys ctx Q (final (Sampling.eval table p))) keys suffix entry.1.1 split with
      ⟨prior,current,rest,hpath,member,hprior⟩ | ⟨member,hprior⟩
  · left
    refine ⟨prior,current,rest,hpath,member,
      fresh_request_uncovered ctx Q _ before recorded current entry.1.1 member miss,?_⟩
    intro raw hraw
    apply request_covered ctx Q _ raw
    intro key hkey
    exact replay_covered _ _ keys _ key
      (List.IsPrefix.mem (List.mem_flatMap.mpr ⟨raw,hraw,hkey⟩) hprior)
  · right
    refine ⟨member,?_⟩
    intro raw hraw
    apply request_covered ctx Q _ raw
    intro key hkey
    exact replay_covered _ _ keys _ key
      (List.IsPrefix.mem (List.mem_flatMap.mpr ⟨raw,hraw,hkey⟩) hprior)

end Whir.WHIRSourceAllocationOrigin
