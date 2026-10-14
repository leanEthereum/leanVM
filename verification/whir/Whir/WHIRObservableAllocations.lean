import Whir.WHIRPublicBackfill

/-! Chronological allocation replay from executed public requests and physical
completion records, without an adversary program, private coins, or raw table. -/
namespace Whir.WHIRObservableAllocations
open TypedOracleCompiler TypedFiatShamirGame RawOracleCoupling
open RawOracleCoupling.Concrete FiatShamirGame DuplexModeGame
open RawWHIRKeys (Context Packet)
open WHIRPublicBackfill WHIRModeFinal

section Replay
universe u w
variable {Key : Type u} {Answer : Key → Type u} [DecidableEq Key]
variable (deps : Key → List Key)

/-- An unavailable public answer remains an explicit failure. Existing entries
are reused; only misses generate a chronological allocation annotation. -/
def replayKeys (source : Cache Key Answer) : List Key → Cache Key Answer →
    Option (Cache Key Answer × List (Sigma (AnnotatedAnswer (Answer := Answer))))
  | [], cache => some (cache,[])
  | key :: keys, cache =>
    match cache key with
    | some _ => replayKeys source keys cache
    | none => (source key).bind fun answer =>
      (replayKeys source keys (put cache key answer)).map fun result =>
        (result.1,⟨(key,dependencyHistory deps cache key),answer⟩ :: result.2)

def tableReplay (table : (key : Key) → Answer key) : List Key → Cache Key Answer →
    Cache Key Answer × List (Sigma (AnnotatedAnswer (Answer := Answer)))
  | [], cache => (cache,[])
  | key :: keys, cache =>
    match cache key with
    | some _ => tableReplay table keys cache
    | none =>
      let result := tableReplay table keys (put cache key (table key))
      (result.1,⟨(key,dependencyHistory deps cache key),table key⟩ :: result.2)

theorem replayKeys_of_hits (source : Cache Key Answer) (table : (key : Key) → Answer key)
    (keys : List Key) (cache : Cache Key Answer)
    (covered : ∀ key ∈ keys, source key = some (table key)) :
    replayKeys deps source keys cache = some (tableReplay deps table keys cache) := by
  induction keys generalizing cache with
  | nil => rfl
  | cons key keys ih =>
    simp only [replayKeys, tableReplay]
    cases hit : cache key with
    | some answer => exact ih cache (fun k h => covered k (List.mem_cons_of_mem _ h))
    | none =>
      simp only [covered key (by simp), Option.bind_some,
        ih _ (fun k h => covered k (List.mem_cons_of_mem _ h)), Option.map_some]

def Consistent (table : (key : Key) → Answer key) (cache : Cache Key Answer) : Prop :=
  ∀ key answer, cache key = some answer → table key = answer

theorem Consistent.put {table : (key : Key) → Answer key} {cache : Cache Key Answer}
    (consistent : Consistent table cache) (key : Key) :
    Consistent table (put cache key (table key)) := by
  intro k answer hit
  by_cases same : k = key
  · subst k
    simpa only [put_self, Option.some.injEq] using hit
  · exact consistent k answer (by simpa only [put_other _ _ _ _ same] using hit)

/-- The memo compiler follows exactly the executed path, including cache hits
whose answers select the continuation. No off-path continuation is inspected. -/
theorem execute_relabelMemo {R : Type w} {n}
    (table : (key : Key) → Answer key) (p : Sampling Key Answer R n)
    (cache : Cache Key Answer) (consistent : Consistent table cache) :
    Sampling.execute (fun key : Annotated (Answer := Answer) => table key.1)
        (relabelMemo (dependencyLabels deps) p cache) =
      ((Sampling.eval table p,(tableReplay deps table ((Sampling.execute table p).2.map Sigma.fst) cache).1),
        (tableReplay deps table ((Sampling.execute table p).2.map Sigma.fst) cache).2) := by
  induction p generalizing cache with
  | ret result => rfl
  | draw key next ih =>
    cases hit : cache key with
    | some answer =>
      have equal := consistent key answer hit
      simp only [relabelMemo, hit, Sampling.execute_pad, Sampling.execute, Sampling.eval,
        List.map_cons, tableReplay]
      rw [equal]
      exact ih answer cache consistent
    | none =>
      simp only [relabelMemo, hit, Sampling.execute, Sampling.eval, dependencyLabels,
        Equiv.refl_apply, List.map_cons, tableReplay]
      have step := ih (table key) (put cache key (table key)) (consistent.put key)
      simp only [dependencyLabels] at step
      rw [step]

omit [DecidableEq Key] in
theorem execute_answers {R : Type w} {n} (table : (key : Key) → Answer key)
    (p : Sampling Key Answer R n) :
    ∀ entry ∈ (Sampling.execute table p).2, table entry.1 = entry.2 := by
  induction p with
  | ret => intro entry member; cases member
  | draw key next ih =>
    intro entry member
    rcases List.mem_cons.mp member with equal | member
    · subst entry; rfl
    · exact ih (table key) entry member

theorem eval_relabelMemo {R : Type w} {n} (table : (key : Key) → Answer key)
    (p : Sampling Key Answer R n) (cache : Cache Key Answer) :
    Sampling.eval (fun key : Annotated (Answer := Answer) => table key.1)
      (relabelMemo (dependencyLabels deps) p cache) = Sampling.eval table (memo p cache) := by
  induction p generalizing cache with
  | ret => rfl
  | draw key next ih =>
    cases hit : cache key with
    | some answer => simpa only [relabelMemo, memo, hit, Sampling.eval_pad] using ih answer cache
    | none =>
      simpa only [relabelMemo, memo, hit, Sampling.eval, dependencyLabels, Equiv.refl_apply]
        using ih (table key) (put cache key (table key))

end Replay

private instance (ctx : Context) (Q : Nat) : DecidableEq (GroupKey ctx Q) := inferInstance

/-- Every recognized request completes its real caller outputs and canonical
packet ancestors. Off-image requests have one independent garbage group. -/
def requestKeys (ctx : Context) (Q : Nat) (raw : RawKey Q) : List (GroupKey ctx Q) :=
  match recognized : RawWHIRKeys.recognize ctx Q raw with
  | some pos => completionKeys ctx Q pos.1
  | none => [.inr ⟨raw,recognized⟩]

def finalKeys (ctx : Context) (Q : Nat) : Option (Packet ctx Q) → List (GroupKey ctx Q)
  | none => []
  | some packet => completionKeys ctx Q packet

def allocationRequests (ctx : Context) (Q : Nat) (requests : List (RawKey Q))
    (final : Option (Packet ctx Q)) : List (GroupKey ctx Q) :=
  requests.flatMap (requestKeys ctx Q) ++ finalKeys ctx Q final

/-- The executable observer has no access to the source program or its private
coins. Completed records are explicit physical public-output arguments. -/
def observe (ctx : Context) (Q : Nat) (answers : List (RawKey Q × Digest32))
    (final : Option (Packet ctx Q)) (records : List (Record ctx Q)) :
    Option (PublicCache ctx Q × List (Sigma (AllocationAnswer ctx Q))) :=
  replayKeys (dependencyKeys ctx Q) (observableCache ctx Q answers records)
    (allocationRequests ctx Q (answers.map Prod.fst) final) (fun _ => none)

theorem warm_keys (ctx : Context) (Q : Nat)
    (table : (key : GroupKey ctx Q) → GroupAnswer ctx Q key) (packets : List (Packet ctx Q)) :
    (Sampling.execute table ((partition ctx Q).warm packets)).2.map Sigma.fst = packets.map Sum.inl := by
  induction packets with
  | nil => rfl
  | cons packet rest ih => simp only [Partition.warm, Sampling.execute, List.map_cons, ih]

theorem warmCaller_keys (ctx : Context) (Q : Nat)
    (table : (key : GroupKey ctx Q) → GroupAnswer ctx Q key)
    (calls : List (partition ctx Q).Garbage) :
    (Sampling.execute table ((partition ctx Q).warmCaller calls)).2.map Sigma.fst = calls.map Sum.inr := by
  induction calls with
  | nil => rfl
  | cons raw rest ih => simp only [Partition.warmCaller, Sampling.execute, List.map_cons, ih]

theorem completePacket_keys (ctx : Context) (Q : Nat)
    (table : (key : GroupKey ctx Q) → GroupAnswer ctx Q key) (packet : Packet ctx Q) :
    (Sampling.execute table ((partition ctx Q).completePacket (schedule ctx Q) (callerPlan ctx Q) packet)).2.map
      Sigma.fst = completionKeys ctx Q packet := by
  simp only [Partition.completePacket, Sampling.execute_pad, Sampling.execute_bind,
    Sampling.execute, List.map_append, warmCaller_keys, warm_keys, List.map_cons, List.map_nil]
  simp only [completionKeys, dependencyKeys, Partition.dependencies, List.append_assoc]

theorem request_keys (ctx : Context) (Q : Nat)
    (table : (key : GroupKey ctx Q) → GroupAnswer ctx Q key) (raw : RawKey Q) :
    (Sampling.execute table ((partition ctx Q).request (schedule ctx Q) (callerPlan ctx Q) raw)).2.map
      Sigma.fst = requestKeys ctx Q raw := by
  unfold Partition.request requestKeys
  split
  · rename_i pos recognized
    simp only [Sampling.execute_pad, Sampling.execute_bind, Sampling.execute,
      List.append_nil, completePacket_keys]
    split
    · rename_i other h
      have equal : other = pos := Option.some.inj (h.symm.trans recognized)
      subst other
      rfl
    · rename_i h
      have impossible := h.symm.trans recognized
      cases impossible
  · rename_i recognized
    simp only [Sampling.execute_pad, Sampling.execute, List.map_cons, List.map_nil]
    split
    · rename_i other h
      have impossible := h.symm.trans recognized
      cases impossible
    · rfl

theorem program_keys (ctx : Context) (Q : Nat) {R : Type} {n}
    (table : RawKey Q → Digest32) (final : R → Option (Packet ctx Q))
    (p : Sampling (RawKey Q) (fun _ => Digest32) R n) :
    (Sampling.execute ((partition ctx Q).split table)
      ((partition ctx Q).program (schedule ctx Q) (callerPlan ctx Q) final p)).2.map Sigma.fst =
    allocationRequests ctx Q ((Sampling.execute table p).2.map Sigma.fst) (final (Sampling.eval table p)) := by
  induction p with
  | ret result =>
    simp only [Partition.program, Sampling.execute, Sampling.eval, List.map_nil,
      allocationRequests, List.flatMap_nil, List.nil_append]
    split <;> simp_all only [Sampling.execute_pad, Sampling.execute_bind, Sampling.execute,
      List.append_nil, completePacket_keys, finalKeys, List.map_nil]
  | draw raw next ih =>
    simp only [Partition.program, Sampling.execute_pad, Sampling.execute_bind,
      Partition.eval_request, Partition.join_split, Sampling.execute, Sampling.eval,
      List.map_append, request_keys, ih, List.map_cons, allocationRequests, List.flatMap_cons,
      List.append_assoc]

theorem requestKeys_some (ctx : Context) (Q : Nat) (raw : RawKey Q)
    (pos : RawWHIRKeys.Position ctx Q) (recognized : RawWHIRKeys.recognize ctx Q raw = some pos) :
    requestKeys ctx Q raw = completionKeys ctx Q pos.1 := by
  unfold requestKeys
  split
  · rename_i other h
    have equal : other = pos := Option.some.inj (h.symm.trans recognized)
    subst other
    rfl
  · rename_i h
    have impossible := h.symm.trans recognized
    cases impossible

theorem requestKeys_none (ctx : Context) (Q : Nat) (raw : RawKey Q)
    (recognized : RawWHIRKeys.recognize ctx Q raw = none) :
    requestKeys ctx Q raw = [.inr ⟨raw,recognized⟩] := by
  unfold requestKeys
  split
  · rename_i other h
    have impossible := h.symm.trans recognized
    cases impossible
  · rfl

/-- Coverage is derived from every executed request and the selected completion,
not assumed as a property of the reconstructed state. -/
theorem observable_covered (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (answers : List (RawKey Q × Digest32)) (final : Option (Packet ctx Q))
    (consistent : ∀ answer ∈ answers, table answer.1 = answer.2) :
    ∀ key ∈ allocationRequests ctx Q (answers.map Prod.fst) final,
      observableCache ctx Q answers
        (idealRecords ctx Q table (selections ctx Q (answers.map Prod.fst) final)) key =
        some ((partition ctx Q).split table key) := by
  intro key member
  rcases List.mem_append.mp member with request | terminal
  · obtain ⟨raw,requested,member⟩ := List.mem_flatMap.mp request
    cases recognized : RawWHIRKeys.recognize ctx Q raw with
    | some pos =>
      rw [requestKeys_some ctx Q raw pos recognized] at member
      exact observableCache_request ctx Q table answers _ final consistent raw requested pos recognized key member
    | none =>
      rw [requestKeys_none ctx Q raw recognized] at member
      have equal : key = .inr ⟨raw,recognized⟩ := List.mem_singleton.mp member
      subst key
      obtain ⟨answer,observed,same⟩ := List.mem_map.mp requested
      have rawEq : answer.1 = raw := same
      have hit := observableCache_garbage ctx Q table answers
        (selections ctx Q (answers.map Prod.fst) final) consistent ⟨raw,recognized⟩ answer.2
        (by simpa only [← rawEq] using observed)
      exact hit
  · cases final with
    | none => cases terminal
    | some packet =>
      exact observableCache_final ctx Q table answers _ packet consistent key terminal

def rawAnswers (Q : Nat) {R : Type} {n} (table : RawKey Q → Digest32)
    (p : Sampling (RawKey Q) (fun _ => Digest32) R n) : List (RawKey Q × Digest32) :=
  (Sampling.execute table p).2.map (fun entry => (entry.1,entry.2))

theorem rawAnswers_consistent (Q : Nat) {R : Type} {n} (table : RawKey Q → Digest32)
    (p : Sampling (RawKey Q) (fun _ => Digest32) R n) :
    ∀ answer ∈ rawAnswers Q table p, table answer.1 = answer.2 := by
  intro answer member
  obtain ⟨entry,hm,rfl⟩ := List.mem_map.mp member
  exact execute_answers table p entry hm

theorem rawAnswers_keys (Q : Nat) {R : Type} {n} (table : RawKey Q → Digest32)
    (p : Sampling (RawKey Q) (fun _ => Digest32) R n) :
    (rawAnswers Q table p).map Prod.fst = (Sampling.execute table p).2.map Sigma.fst := by
  simp only [rawAnswers, List.map_map, Function.comp_def]

def allocationOracle (ctx : Context) (Q : Nat) (table : RawKey Q → Digest32)
    (key : AllocationKey ctx Q) : AllocationAnswer ctx Q key :=
  (partition ctx Q).split table key.1

/-- Exact chronological keys, full group answers, and final cache are functions
of the executed raw request path and final selection, not off-path code. -/
theorem compile_execution (ctx : Context) (Q : Nat) {R : Type} {n}
    (table : RawKey Q → Digest32) (final : R → Option (Packet ctx Q))
    (p : Sampling (RawKey Q) (fun _ => Digest32) R n) :
    Sampling.execute (allocationOracle ctx Q table) (compile ctx Q final p) =
      let replay := tableReplay (dependencyKeys ctx Q) ((partition ctx Q).split table)
        (allocationRequests ctx Q (rawAnswers Q table p |>.map Prod.fst) (final (Sampling.eval table p)))
        (fun _ => none)
      ((Sampling.eval table p,replay.1),replay.2) := by
  unfold RawOracleCoupling.Concrete.compile allocationOracle
  rw [execute_relabelMemo (dependencyKeys ctx Q) _ _ _ (by intro key answer h; cases h)]
  simp only [program_keys, Partition.eval_program, Partition.join_split, rawAnswers_keys]

/-- Public replay recovers the complete compiler allocation transcript and its
final cache. Actual executed answers provide consistency, and physical completion
records provide coverage; neither condition is a new coupling assumption. -/
theorem observe_execution (ctx : Context) (Q : Nat) {R : Type} {n}
    (table : RawKey Q → Digest32) (final : R → Option (Packet ctx Q))
    (p : Sampling (RawKey Q) (fun _ => Digest32) R n) :
    observe ctx Q (rawAnswers Q table p) (final (Sampling.eval table p))
      (idealRecords ctx Q table (selections ctx Q ((rawAnswers Q table p).map Prod.fst)
        (final (Sampling.eval table p)))) =
      some ((Sampling.execute (allocationOracle ctx Q table) (compile ctx Q final p)).1.2,
        (Sampling.execute (allocationOracle ctx Q table) (compile ctx Q final p)).2) := by
  unfold observe
  rw [replayKeys_of_hits _ _ ((partition ctx Q).split table) _ _
    (observable_covered ctx Q table _ _ (rawAnswers_consistent Q table p))]
  rw [compile_execution]

theorem compile_cache (ctx : Context) (Q : Nat) {R : Type} {n}
    (table : RawKey Q → Digest32) (final : R → Option (Packet ctx Q))
    (p : Sampling (RawKey Q) (fun _ => Digest32) R n) :
    (Sampling.execute (allocationOracle ctx Q table) (compile ctx Q final p)).1 =
      tableExecution ctx Q final p table := by
  rw [Sampling.execute_value]
  exact eval_relabelMemo (dependencyKeys ctx Q) _ _ _

theorem observe_tableExecution (ctx : Context) (Q : Nat) {R : Type} {n}
    (table : RawKey Q → Digest32) (final : R → Option (Packet ctx Q))
    (p : Sampling (RawKey Q) (fun _ => Digest32) R n) :
    observe ctx Q (rawAnswers Q table p) (final (Sampling.eval table p))
      (idealRecords ctx Q table (selections ctx Q ((rawAnswers Q table p).map Prod.fst)
        (final (Sampling.eval table p)))) =
      some ((tableExecution ctx Q final p table).2,
        (Sampling.execute (allocationOracle ctx Q table) (compile ctx Q final p)).2) := by
  rw [observe_execution, compile_cache]

/-- Distinct adaptive programs, result types, and bounds can be substituted
when their executed raw paths and selected terminal packets agree. -/
theorem compile_path_congr (ctx : Context) (Q : Nat) {R S : Type} {n m}
    (table : RawKey Q → Digest32) (final : R → Option (Packet ctx Q))
    (otherFinal : S → Option (Packet ctx Q))
    (p : Sampling (RawKey Q) (fun _ => Digest32) R n)
    (other : Sampling (RawKey Q) (fun _ => Digest32) S m)
    (path : (rawAnswers Q table p).map Prod.fst = (rawAnswers Q table other).map Prod.fst)
    (selected : final (Sampling.eval table p) = otherFinal (Sampling.eval table other)) :
    ((Sampling.execute (allocationOracle ctx Q table) (compile ctx Q final p)).1.2,
      (Sampling.execute (allocationOracle ctx Q table) (compile ctx Q final p)).2) =
    ((Sampling.execute (allocationOracle ctx Q table) (compile ctx Q otherFinal other)).1.2,
      (Sampling.execute (allocationOracle ctx Q table) (compile ctx Q otherFinal other)).2) := by
  simp only [compile_execution, path, selected]

/-- The same reconstruction theorem directly on the physically executed
completion program. Its records are derived by `runIdeal`, not supplied by a
cache-coverage or state-equality premise. -/
theorem observe_backfill (ctx : Context) (Q : Nat) {R Out Seed State : Type} {n}
    (sim : Simulator Q Seed State) (table : RawKey Q → Digest32) (state : State)
    (final : R → Option (Packet ctx Q))
    (p : Sampling (RawKey Q) (fun _ => Digest32) R n) (output : Out)
    (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining (backfill ctx Q output ((rawAnswers Q table p).map Prod.fst)
      (final (Sampling.eval table p)))) :
    observe ctx Q (rawAnswers Q table p) (final (Sampling.eval table p))
      (runIdeal sim table ctx.iv state
        (backfill ctx Q output ((rawAnswers Q table p).map Prod.fst) (final (Sampling.eval table p)))
        remaining cap counted).view.result.records =
      some ((tableExecution ctx Q final p table).2,
        (Sampling.execute (allocationOracle ctx Q table) (compile ctx Q final p)).2) := by
  rw [backfill_ideal_result]
  exact observe_tableExecution ctx Q table final p

end Whir.WHIRObservableAllocations
