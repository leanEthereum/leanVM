import Whir.RawOracleCoupling
import Whir.RawWHIRKeys

/-! Operational provenance for canonical cache-derived allocation labels. -/
namespace Whir.RawOracleCoupling
open TypedOracleCompiler TypedFiatShamirGame

universe u v w
section Dependencies
variable {Key : Type u} {Answer : Key → Type u} [DecidableEq Key]
variable (deps : Key → List Key)

abbrev Growth (before after : Cache Key Answer) : Prop :=
  ∀ k a, before k = some a → after k = some a

def Ready (cache : Cache Key Answer) (k : Key) : Prop :=
  ∀ j ∈ deps k, ∃ a, cache j = some a

def dependencyHistory (cache : Cache Key Answer) (k : Key) : List (Sigma Answer) :=
  (deps k).filterMap (fun j => (cache j).map (Sigma.mk j))

abbrev Annotated := Key × List (Sigma Answer)
abbrev AnnotatedAnswer (k : Annotated (Answer := Answer)) := Answer k.1

def dependencyLabels : Labeling Key Answer (Annotated (Answer := Answer)) AnnotatedAnswer where
  key cache k := (k, dependencyHistory deps cache k)
  answer _ _ := Equiv.refl _

omit [DecidableEq Key] in
 theorem growth_refl (cache : Cache Key Answer) : Growth cache cache := fun _ _ h => h
omit [DecidableEq Key] in
 theorem growth_trans {a b c : Cache Key Answer} (ab : Growth a b) (bc : Growth b c) :
    Growth a c := fun k x h => bc k x (ab k x h)

 theorem growth_put (cache : Cache Key Answer) (k : Key) (a : Answer k)
    (miss : cache k = none) : Growth cache (put cache k a) := by
  intro j b hit
  by_cases h : j = k
  · subst j; rw [miss] at hit; contradiction
  · simpa only [put_other _ _ _ _ h] using hit

omit [DecidableEq Key] in
 theorem Ready.mono {cache next : Cache Key Answer} {k}
    (ready : Ready deps cache k) (growth : Growth cache next) : Ready deps next k := by
  intro j hj
  obtain ⟨a,ha⟩ := ready j hj
  exact ⟨a,growth j a ha⟩

omit [DecidableEq Key] in
 theorem dependencyHistory_mono {cache next : Cache Key Answer} {k}
    (ready : Ready deps cache k) (growth : Growth cache next) :
    dependencyHistory deps cache k = dependencyHistory deps next k := by
  apply List.filterMap_congr
  intro j hj
  obtain ⟨a,ha⟩ := ready j hj
  rw [ha, growth j a ha]

 def Recorded (cache : Cache Key Answer)
    (trace : List (Sigma (AnnotatedAnswer (Answer := Answer)))) : Prop :=
  ∀ k a, cache k = some a → Ready deps cache k ∧
    (⟨(k, dependencyHistory deps cache k),a⟩ : Sigma AnnotatedAnswer) ∈ trace

omit [DecidableEq Key] in
 theorem recorded_empty : Recorded deps (fun _ => none : Cache Key Answer) [] := by
  intro k a h; cases h

omit [DecidableEq Key] in
 theorem Recorded.mono_trace {cache : Cache Key Answer} {trace more}
    (recorded : Recorded deps cache trace) (subset : ∀ x ∈ trace, x ∈ more) :
    Recorded deps cache more := by
  intro k a hit
  obtain ⟨hr,ht⟩ := recorded k a hit
  exact ⟨hr,subset _ ht⟩

 theorem Recorded.insert {cache : Cache Key Answer} {trace k}
    (recorded : Recorded deps cache trace) (ready : Ready deps cache k)
    (miss : cache k = none) (a : Answer k) :
    Recorded deps (put cache k a)
      (trace ++ [⟨(k,dependencyHistory deps cache k),a⟩]) := by
  have growth := growth_put cache k a miss
  intro j b hit
  by_cases h : j = k
  · subst j
    simp only [put_self, Option.some.injEq] at hit
    subst b
    exact ⟨ready.mono deps growth, by rw [← dependencyHistory_mono deps ready growth]; simp⟩
  · rw [put_other _ _ _ _ h] at hit
    obtain ⟨hr,ht⟩ := recorded j b hit
    exact ⟨hr.mono deps growth, by
      rw [← dependencyHistory_mono deps hr growth]
      exact List.mem_append_left _ ht⟩

/-- This is a recursively checkable safety predicate on a concrete interpreter,
not an oracle-distribution or cache-correctness assumption. -/
def Safe {R : Type w} (post : R × Cache Key Answer → Prop) {n} :
    Sampling Key Answer R n → Cache Key Answer → Prop
  | .ret r, cache => post (r,cache)
  | .draw k next, cache =>
    match cache k with
    | some a => Safe post (next a) cache
    | none => Ready deps cache k ∧ ∀ a, Safe post (next a) (put cache k a)

 theorem Safe.mono {R : Type w} {P Q : R × Cache Key Answer → Prop} {n}
    {p : Sampling Key Answer R n} {cache} (safe : Safe deps P p cache)
    (imp : ∀ result, P result → Q result) : Safe deps Q p cache := by
  induction p generalizing cache with
  | ret => exact imp _ safe
  | draw k next ih =>
    cases hit : cache k with
    | some a =>
      simp only [Safe, hit] at safe ⊢
      exact ih a safe
    | none =>
      simp only [Safe, hit] at safe ⊢
      exact ⟨safe.1,fun a => ih a (safe.2 a)⟩

theorem Safe.eval {R : Type w} {P : R × Cache Key Answer → Prop} {n}
    {p : Sampling Key Answer R n} {cache} (safe : Safe deps P p cache)
    (table : (k : Key) → Answer k) :
    P (Sampling.eval table (memo p cache)) := by
  induction p generalizing cache with
  | ret => exact safe
  | draw k next ih =>
    cases hit : cache k with
    | some a =>
      simp only [memo, hit, Sampling.eval_pad]
      exact ih a (by simpa only [Safe, hit] using safe)
    | none =>
      simp only [memo, hit, Sampling.eval]
      have hs : Ready deps cache k ∧ ∀ a, Safe deps P (next a) (put cache k a) := by
        simpa only [Safe, hit] using safe
      exact ih (table k) (hs.2 (table k))

 theorem safe_pad {R : Type w} (P : R × Cache Key Answer → Prop) {n m}
    (h : n ≤ m) (p : Sampling Key Answer R n) (cache : Cache Key Answer) :
    Safe deps P (Sampling.pad h p) cache ↔ Safe deps P p cache := by
  induction p generalizing m cache with
  | ret => simp only [Sampling.pad, Safe]
  | draw k next ih =>
    cases m with
    | zero => omega
    | succ m =>
      simp only [Sampling.pad, Safe]
      split <;> simp only [ih]

 theorem safe_bind {R T : Type*} (P : T × Cache Key Answer → Prop) {n m}
    (p : Sampling Key Answer R n) (f : R → Sampling Key Answer T m)
    (cache : Cache Key Answer) :
    Safe deps P (Sampling.bind p f) cache ↔
      Safe deps (fun result => Safe deps P (f result.1) result.2) p cache := by
  induction p generalizing cache with
  | ret => simp only [Sampling.bind, safe_pad, Safe]
  | draw k next ih =>
    simp only [Sampling.bind, safe_pad, Safe]
    split <;> simp only [ih]

 theorem safe_runs {R : Type w} {P : R × Cache Key Answer → Prop} {n}
    (p : Sampling Key Answer R n) (cache : Cache Key Answer) {before trace result}
    (recorded : Recorded deps cache before) (safe : Safe deps P p cache)
    (run : Sampling.Runs (relabelMemo (dependencyLabels deps) p cache) trace result) :
    P result ∧ Growth cache result.2 ∧ Recorded deps result.2 (before ++ trace) := by
  induction p generalizing cache before trace result with
  | ret r =>
    cases run
    exact ⟨safe, growth_refl cache, by simpa using recorded⟩
  | draw k next ih =>
    cases hit : cache k with
    | some a =>
      simp only [relabelMemo, hit, Sampling.runs_pad] at run
      exact ih a cache recorded (by simpa only [Safe,hit] using safe) run
    | none =>
      simp only [relabelMemo, hit] at run
      cases run with
      | draw a run =>
        have hs : Ready deps cache k ∧ ∀ a, Safe deps P (next a) (put cache k a) := by
          simpa only [Safe, hit] using safe
        have hr := ih a (put cache k a) (recorded.insert deps hs.1 hit a) (hs.2 a) run
        exact ⟨hr.1, growth_trans (growth_put cache k a hit) hr.2.1,
          by simpa only [List.append_assoc, List.singleton_append, dependencyLabels] using hr.2.2⟩


/-- Every actual allocated answer survives in the final global cache. This
direction complements `Recorded`, which locates cached entries in the trace. -/
theorem dependencyMemo_runs_cache {R : Type w} {n} (p : Sampling Key Answer R n)
    (cache : Cache Key Answer) {trace result}
    (run : Sampling.Runs (relabelMemo (dependencyLabels deps) p cache) trace result) :
    Growth cache result.2 ∧ ∀ entry ∈ trace, result.2 entry.1.1 = some entry.2 := by
  induction p generalizing cache trace result with
  | ret r =>
    cases run
    exact ⟨growth_refl cache, by intro entry member; cases member⟩
  | draw k next ih =>
    cases hit : cache k with
    | some a =>
      simp only [relabelMemo, hit, Sampling.runs_pad] at run
      exact ih a cache run
    | none =>
      simp only [relabelMemo, hit] at run
      cases run with
      | draw a run =>
        have rest := ih a (put cache k a) run
        refine ⟨growth_trans (growth_put cache k a hit) rest.1,?_⟩
        intro entry member
        rcases List.mem_cons.mp member with equal | member
        · subst entry
          exact rest.1 k a (put_self _ _ _)
        · exact rest.2 entry member

/-- A private annotation is fixed when its dependencies are already cached.
No later allocation or final-state reconstruction can change that annotation. -/
theorem safe_runs_history {R : Type w} {P : R × Cache Key Answer → Prop} {n}
    (p : Sampling Key Answer R n) (cache : Cache Key Answer) {trace result}
    (safe : Safe deps P p cache)
    (run : Sampling.Runs (relabelMemo (dependencyLabels deps) p cache) trace result) :
    ∀ entry ∈ trace, entry.1.2 = dependencyHistory deps result.2 entry.1.1 := by
  induction p generalizing cache trace result with
  | ret r =>
    cases run
    intro entry member
    cases member
  | draw k next ih =>
    cases hit : cache k with
    | some a =>
      simp only [relabelMemo, hit, Sampling.runs_pad] at run
      exact ih a cache (by simpa only [Safe,hit] using safe) run
    | none =>
      simp only [relabelMemo, hit] at run
      cases run with
      | draw a run =>
        have hs : Ready deps cache k ∧ ∀ a, Safe deps P (next a) (put cache k a) := by
          simpa only [Safe,hit] using safe
        have growth := (dependencyMemo_runs_cache deps (next a) (put cache k a) run).1
        intro entry member
        rcases List.mem_cons.mp member with equal | member
        · subst entry
          exact dependencyHistory_mono deps hs.1 (growth_trans (growth_put cache k a hit) growth)
        · exact ih a (put cache k a) (hs.2 a) run entry member

end Dependencies

namespace Partition
variable {Raw Packet D : Type u} {Block : Packet → Type u}
variable (part : Partition Raw Packet Block)
variable [DecidableEq Packet] [DecidableEq Raw]

def dependencies {B C} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C) : part.Key → List part.Key
  | .inl p => (caller.calls p).map Sum.inr ++ (schedule.ancestors p).map Sum.inl
  | .inr _ => []

def CachedKeys (cache : Cache part.Key (part.Answer (D := D))) (xs : List Packet) : Prop :=
  ∀ p ∈ xs, ∃ a, cache (.inl p) = some a

def CachedCallers (cache : Cache part.Key (part.Answer (D := D)))
    (calls : List part.Garbage) : Prop :=
  ∀ raw ∈ calls, ∃ answer, cache (.inr raw) = some answer

def Ordered {B} (schedule : Schedule Packet B) (prior xs : List Packet) : Prop :=
  ∀ before p after, xs = before ++ p :: after →
    ∀ a ∈ schedule.ancestors p, a ∈ prior ++ before

theorem safe_warm {B C} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C) (prior xs : List Packet)
    (cache : Cache part.Key (part.Answer (D := D)))
    (known : part.CachedKeys cache prior) (ordered : Ordered schedule prior xs)
    (callerKnown : ∀ p ∈ xs, part.CachedCallers cache (caller.calls p)) :
    Safe (part.dependencies schedule caller)
      (fun result => Growth cache result.2 ∧ part.CachedKeys result.2 (prior ++ xs))
      (part.warm xs) cache := by
  induction xs generalizing prior cache with
  | nil => exact ⟨growth_refl cache, by simpa using known⟩
  | cons p ps ih =>
    have ready : Ready (part.dependencies schedule caller) cache (.inl p) := by
      intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · obtain ⟨raw,member,rfl⟩ := List.mem_map.mp hj
        exact callerKnown p List.mem_cons_self raw member
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hj
        exact known a (by simpa using ordered [] p ps rfl a ha)
    have ordered' : Ordered schedule (prior ++ [p]) ps := by
      intro before q after he a ha
      have hm := ordered (p::before) q after (by simp [he]) a ha
      simpa only [List.append_assoc, List.singleton_append] using hm
    simp only [warm, Safe]
    cases hit : cache (.inl p) with
    | some a =>
      have known' : part.CachedKeys cache (prior ++ [p]) := by
        intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact known q hq
        · simp only [List.mem_singleton] at hq; subst q; exact ⟨a,hit⟩
      exact (ih (prior ++ [p]) cache known' ordered'
        (fun q hq => callerKnown q (List.mem_cons_of_mem _ hq))).mono _ (fun result h =>
        ⟨h.1,by simpa only [List.append_assoc, List.singleton_append] using h.2⟩)
    | none =>
      refine ⟨ready,fun a => ?_⟩
      have growth := growth_put cache (.inl p) a hit
      have known' : part.CachedKeys (put cache (.inl p) a) (prior ++ [p]) := by
        intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨b,hb⟩ := known q hq; exact ⟨b,growth _ _ hb⟩
        · simp only [List.mem_singleton] at hq; subst q; exact ⟨a,put_self _ _ _⟩
      have nextCaller : ∀ q ∈ ps, part.CachedCallers (put cache (.inl p) a) (caller.calls q) := by
        intro q hq raw member
        obtain ⟨b,hb⟩ := callerKnown q (List.mem_cons_of_mem _ hq) raw member
        exact ⟨b,growth _ _ hb⟩
      exact (ih (prior ++ [p]) _ known' ordered' nextCaller).mono _ (fun result h =>
        ⟨growth_trans growth h.1,by simpa only [List.append_assoc, List.singleton_append] using h.2⟩)


theorem safe_warmCaller {B C} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C) (calls : List part.Garbage)
    (cache : Cache part.Key (part.Answer (D := D))) :
    Safe (part.dependencies schedule caller)
      (fun result => Growth cache result.2 ∧ part.CachedCallers result.2 calls)
      (part.warmCaller calls) cache := by
  induction calls generalizing cache with
  | nil => exact ⟨growth_refl cache,by intro raw member; cases member⟩
  | cons raw rest ih =>
    simp only [warmCaller, Safe]
    cases hit : cache (.inr raw) with
    | some a =>
      apply (ih cache).mono
      intro result h
      refine ⟨h.1,?_⟩
      intro key member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨a,h.1 _ _ hit⟩
      · exact h.2 key member
    | none =>
      refine ⟨?_,fun a => ?_⟩
      · intro key member; cases member
      · apply (ih (put cache (.inr raw) a)).mono
        intro result h
        refine ⟨growth_trans (growth_put cache (.inr raw) a hit) h.1,?_⟩
        intro key member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨a,h.1 _ _ (put_self _ _ _)⟩
        · exact h.2 key member

theorem safe_completePacket {B C} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C)
    (ordered : ∀ p, Ordered schedule [] (schedule.ancestors p))
    (coherent : ∀ p a, a ∈ schedule.ancestors p → caller.calls a = caller.calls p)
    (packet : Packet) (cache : Cache part.Key (part.Answer (D := D))) :
    Safe (part.dependencies schedule caller)
      (fun result => part.CachedKeys result.2 (schedule.ancestors packet ++ [packet]) ∧
        part.CachedCallers result.2 (caller.calls packet))
      (part.completePacket schedule caller packet) cache := by
  rw [completePacket, safe_pad, safe_bind]
  apply (part.safe_warmCaller schedule caller (caller.calls packet) cache).mono
  intro first hf
  rw [safe_bind]
  have callerKnown : ∀ ancestor ∈ schedule.ancestors packet,
      part.CachedCallers first.2 (caller.calls ancestor) := by
    intro ancestor member
    rw [coherent packet ancestor member]
    exact hf.2
  apply (part.safe_warm schedule caller [] (schedule.ancestors packet) first.2
    (by intro p hp; cases hp) (ordered packet) callerKnown).mono
  intro past hp
  have ready : Ready (part.dependencies schedule caller) past.2 (.inl packet) := by
    intro key member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨raw,hm,rfl⟩ := List.mem_map.mp member
      obtain ⟨a,ha⟩ := hf.2 raw hm
      exact ⟨a,hp.1 _ _ ha⟩
    · obtain ⟨ancestor,hm,rfl⟩ := List.mem_map.mp member
      exact hp.2 ancestor (by simpa using hm)
  have done (nextCache : Cache part.Key (part.Answer (D := D)))
      (growth : Growth past.2 nextCache) (a : part.Answer (D := D) (.inl packet))
      (hit : nextCache (.inl packet) = some a) :
      part.CachedKeys nextCache (schedule.ancestors packet ++ [packet]) ∧
        part.CachedCallers nextCache (caller.calls packet) := by
    constructor
    · intro key member
      rcases List.mem_append.mp member with member | member
      · obtain ⟨b,hb⟩ := hp.2 key (by simpa using member)
        exact ⟨b,growth _ _ hb⟩
      · simp only [List.mem_singleton] at member
        subst key
        exact ⟨a,hit⟩
    · intro key member
      obtain ⟨b,hb⟩ := hf.2 key member
      exact ⟨b,growth _ _ (hp.1 _ _ hb)⟩
  simp only [Safe]
  cases hit : past.2 (.inl packet) with
  | some a => exact done past.2 (growth_refl _) a hit
  | none =>
    exact ⟨ready,fun a => done _ (growth_put _ _ a hit) a (put_self _ _ _)⟩

theorem safe_request {B C} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C)
    (ordered : ∀ p, Ordered schedule [] (schedule.ancestors p))
    (coherent : ∀ p a, a ∈ schedule.ancestors p → caller.calls a = caller.calls p)
    (raw : Raw) (cache : Cache part.Key (part.Answer (D := D))) :
    Safe (part.dependencies schedule caller) (fun _ => True) (part.request schedule caller raw) cache := by
  unfold request
  split
  · rename_i c recognized
    rw [safe_pad, safe_bind]
    exact (part.safe_completePacket schedule caller ordered coherent c.1 cache).mono _
      (fun _ _ => True.intro)
  · rw [safe_pad]
    simp only [Safe]
    split
    · trivial
    · refine ⟨?_,fun _ => True.intro⟩
      intro j hj
      cases hj

def finishPackets {B} (schedule : Schedule Packet B) : Option Packet → List Packet
  | none => []
  | some p => schedule.ancestors p ++ [p]

def finishCallers {C} (caller : CallerPlan Packet part.Garbage C) : Option Packet → List part.Garbage
  | none => []
  | some p => caller.calls p

theorem safe_program {R : Type u} {B C n} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C)
    (ordered : ∀ p, Ordered schedule [] (schedule.ancestors p))
    (coherent : ∀ p a, a ∈ schedule.ancestors p → caller.calls a = caller.calls p)
    (final : R → Option Packet)
    (p : Sampling Raw (fun _ => D) R n) (cache : Cache part.Key (part.Answer (D := D))) :
    Safe (part.dependencies schedule caller) (fun result =>
      part.CachedKeys result.2 (finishPackets schedule (final result.1)) ∧
        part.CachedCallers result.2 (part.finishCallers caller (final result.1)))
      (part.program schedule caller final p) cache := by
  induction p generalizing cache with
  | ret r =>
    simp only [program]
    split
    · rename_i selected
      simp only [Safe, selected, finishPackets, finishCallers]
      constructor <;> intro key member <;> cases member
    · rename_i packet selected
      rw [safe_pad, safe_bind]
      apply (part.safe_completePacket schedule caller ordered coherent packet cache).mono
      intro result h
      simpa only [Safe, selected, finishPackets, finishCallers] using h
  | draw raw next ih =>
    simp only [program, safe_pad, safe_bind]
    exact (part.safe_request schedule caller ordered coherent raw cache).mono _ (fun result _ => ih _ _)

/-- Caller prewarming and all WHIR ancestor readiness are proved by the
interpreter; no initial correctness or completion certificate is supplied. -/
theorem program_recorded {R : Type u} {B C n} (schedule : Schedule Packet B)
    (caller : CallerPlan Packet part.Garbage C)
    (ordered : ∀ p, Ordered schedule [] (schedule.ancestors p))
    (coherent : ∀ p a, a ∈ schedule.ancestors p → caller.calls a = caller.calls p)
    (final : R → Option Packet) (p : Sampling Raw (fun _ => D) R n) {trace result}
    (run : Sampling.Runs
      (relabelMemo (dependencyLabels (part.dependencies schedule caller))
        (part.program schedule caller final p) (fun _ => none)) trace result) :
    (part.CachedKeys result.2 (finishPackets schedule (final result.1)) ∧
      part.CachedCallers result.2 (part.finishCallers caller (final result.1))) ∧
      Recorded (part.dependencies schedule caller) result.2 trace := by
  have h := safe_runs (part.dependencies schedule caller) _ _ (recorded_empty _)
    (part.safe_program schedule caller ordered coherent final p _) run
  exact ⟨h.1,by simpa using h.2.2⟩

omit [DecidableEq Packet] in
theorem ordered_of_get {B} (schedule : Schedule Packet B) (xs : List Packet)
    (chain : ∀ i (hi : i < xs.length), schedule.ancestors (xs[i]'hi) = xs.take i) :
    Ordered schedule [] xs := by
  intro before p after he a ha
  have hi : before.length < xs.length := by simp [he]
  have hp : (xs[before.length]'hi) = p := by simp [he]
  have h := chain before.length hi
  rw [hp] at h
  have ht : xs.take before.length = before := by simp [he]
  simpa only [List.nil_append, h, ht] using ha
end Partition

namespace Concrete
open RawWHIRKeys DuplexModeGame
open FiatShamirGame (Digest32 average)

abbrev partition (ctx : Context) (Q : Nat) :
    Partition (RawKey Q) (Packet ctx Q) (fun p => Fin (blocks ctx p.val)) where
  encode := encode ctx Q
  recognize := recognize ctx Q
  recognize_encode := recognize_encode ctx Q
  encode_recognize := encode_recognize ctx Q

def schedule (ctx : Context) (Q : Nat) : Partition.Schedule (Packet ctx Q) maxDepth where
  positive := maxDepth_positive
  ancestors := ancestors ctx Q
  bounded := ancestors_maxDepth ctx Q

def callerPlan (ctx : Context) (Q : Nat) :
    Partition.CallerPlan (Packet ctx Q) (partition ctx Q).Garbage ctx.callerOutputCap where
  calls := callerGroups ctx Q
  bounded := callerGroups_bound ctx Q

theorem caller_coherent (ctx : Context) (Q : Nat) (p a : Packet ctx Q)
    (member : a ∈ (schedule ctx Q).ancestors p) :
    (callerPlan ctx Q).calls a = (callerPlan ctx Q).calls p :=
  callerGroups_ancestor ctx Q p a member

/-- Public worst-case charge includes all hidden caller-output blocks. -/
abbrev allocationBudget (ctx : Context) : Nat := maxDepth + ctx.callerOutputCap

def dependencyKeys (ctx : Context) (Q : Nat) :
    (partition ctx Q).Key → List (partition ctx Q).Key :=
  (partition ctx Q).dependencies (schedule ctx Q) (callerPlan ctx Q)

theorem schedule_ordered (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    Partition.Ordered (schedule ctx Q) [] ((schedule ctx Q).ancestors p) :=
  Partition.ordered_of_get _ _ (ancestors_ancestors ctx Q p)

def completion (ctx : Context) (Q : Nat) (p : Packet ctx Q) : List (Packet ctx Q) :=
  ancestors ctx Q p ++ [p]

theorem completion_bound (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    (completion ctx Q p).length ≤ maxDepth := by
  simpa only [completion, List.length_append, List.length_singleton] using ancestors_maxDepth ctx Q p

theorem completion_ordered (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    Partition.Ordered (schedule ctx Q) [] (completion ctx Q p) :=
  Partition.ordered_of_get _ _ (completion_ancestors ctx Q p)

def terminalCompletion (ctx : Context) (Q : Nat) : Option (Packet ctx Q) → List (Packet ctx Q)
  | none => []
  | some p => completion ctx Q p

theorem finishPackets_eq (ctx : Context) (Q : Nat) (p : Option (Packet ctx Q)) :
    Partition.finishPackets (schedule ctx Q) p = terminalCompletion ctx Q p := by
  cases p <;> rfl

theorem terminalCompletion_bound (ctx : Context) (Q : Nat) (p : Option (Packet ctx Q)) :
    (terminalCompletion ctx Q p).length ≤ maxDepth := by
  cases p with
  | none => exact Nat.zero_le _
  | some p => exact completion_bound ctx Q p

theorem terminalCompletion_ordered (ctx : Context) (Q : Nat) (p : Option (Packet ctx Q)) :
    Partition.Ordered (schedule ctx Q) [] (terminalCompletion ctx Q p) := by
  cases p with
  | none =>
    intro before p after he
    have := congrArg List.length he
    simp [terminalCompletion] at this
  | some p => exact completion_ordered ctx Q p

abbrev GroupKey (ctx : Context) (Q : Nat) := (partition ctx Q).Key
abbrev GroupAnswer (ctx : Context) (Q : Nat) := (partition ctx Q).Answer (D := Digest32)
abbrev AllocationKey (ctx : Context) (Q : Nat) := Annotated (Answer := GroupAnswer ctx Q)
abbrev AllocationAnswer (ctx : Context) (Q : Nat) :=
  AnnotatedAnswer (Answer := GroupAnswer ctx Q)

private instance packetDecidableEq (ctx : Context) (Q : Nat) : DecidableEq (Packet ctx Q) :=
  inferInstance
private instance rawKeyDecidableEq (Q : Nat) : DecidableEq (RawKey Q) := inferInstance


/-- One executable global-cache interpreter for every raw request source,
including simulator and auxiliary raw queries. Only returned raw blocks flow
into the original adversary continuation. -/
def compile (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K) :
    Sampling (AllocationKey ctx Q) (AllocationAnswer ctx Q)
      (R × Cache (GroupKey ctx Q) (GroupAnswer ctx Q)) (allocationBudget ctx*K+allocationBudget ctx) :=
  relabelMemo (dependencyLabels (dependencyKeys ctx Q))
    ((partition ctx Q).program (schedule ctx Q) (callerPlan ctx Q) final p) (fun _ => none)

/-- Reference execution with a uniformly selected raw table. The table is
private to the evaluator; the original strategy still sees only raw replies. -/
def tableExecution (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K)
    (table : RawKey Q → Digest32) : R × Cache (GroupKey ctx Q) (GroupAnswer ctx Q) :=
  Sampling.eval ((partition ctx Q).split table)
    (memo ((partition ctx Q).program (schedule ctx Q) (callerPlan ctx Q) final p) (fun _ => none))

theorem tableExecution_result (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K)
    (table : RawKey Q → Digest32) :
    (tableExecution ctx Q final p table).1 = Sampling.eval table p := by
  simp only [tableExecution, memo_eval_first, overlay_empty, Partition.eval_program,
    Partition.join_split]

/-- Final completion caches every requested ancestor in the concrete table
execution, including packets not previously observed by the adversary. -/
theorem tableExecution_cached (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K)
    (table : RawKey Q → Digest32) :
    (partition ctx Q).CachedKeys (tableExecution ctx Q final p table).2
      (terminalCompletion ctx Q (final (tableExecution ctx Q final p table).1)) := by
  have h := (Safe.eval (dependencyKeys ctx Q)
    ((partition ctx Q).safe_program (schedule ctx Q) (callerPlan ctx Q) (schedule_ordered ctx Q)
      (caller_coherent ctx Q) final p (fun _ => none)) ((partition ctx Q).split table)).1
  simpa only [finishPackets_eq, tableExecution] using h

theorem tableExecution_cache (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K)
    (table : RawKey Q → Digest32) (key : GroupKey ctx Q) (a : GroupAnswer ctx Q key)
    (hit : (tableExecution ctx Q final p table).2 key = some a) :
    (partition ctx Q).split table key = a :=
  memo_eval_consistent _ (fun _ => none) _ (by intro _ _ h; cases h) key a hit

/-- Every byte, including unused payload padding, in a completed packet is
the value at its exact concrete raw block coordinate. -/
theorem tableExecution_block (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K)
    (table : RawKey Q → Digest32) (packet : Packet ctx Q)
    (a : Fin (blocks ctx packet.val) → Digest32)
    (hit : (tableExecution ctx Q final p table).2 (.inl packet) = some a)
    (block : Fin (blocks ctx packet.val)) :
    a block = table (encode ctx Q ⟨packet,block⟩) :=
  (congrFun (tableExecution_cache ctx Q final p table (.inl packet) a hit) block).symm

private instance : Finite UInt64 :=
  Finite.of_injective ByteCodec.encodeK ByteCodec.encodeK_injective
private noncomputable instance : Fintype UInt64 := Fintype.ofFinite _

/-- The concrete partition/ancestor coupling has no codec, freshness,
cache-correctness, or equal-distribution premise. The catalog is an immutable
input fixed before the experiment, never a function of the sampled table. -/
theorem distribution (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K)
    (payoff : R → ℚ) :
    average (fun table : RawKey Q → Digest32 => payoff (Sampling.eval table p)) =
      Sampling.expectation (fun result => payoff result.1) (compile ctx Q final p) := by
  unfold compile
  rw [relabelMemo_expectation]
  exact (partition ctx Q).raw_table_eq_packets (schedule ctx Q) _ _ p payoff

/-- Every payoff of both the adversary result and the actual final completed
cache is preserved. Final verification therefore need not trust a claimed
history carried in the adversary's return value. -/
theorem distribution_full (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K)
    (payoff : R × Cache (GroupKey ctx Q) (GroupAnswer ctx Q) → ℚ) :
    average (fun table : RawKey Q → Digest32 => payoff (tableExecution ctx Q final p table)) =
      Sampling.expectation payoff (compile ctx Q final p) := by
  unfold compile tableExecution
  rw [relabelMemo_expectation]
  calc
    _ = average (fun table => payoff (Sampling.eval table
        (memo ((partition ctx Q).program (schedule ctx Q)
          (callerPlan ctx Q) final p) (fun _ => none)))) :=
      average_equiv (partition ctx Q).tableEquiv _
    _ = _ := table_eq_memo_full _ (fun _ => none) payoff

theorem recorded (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K)
    {trace result} (run : Sampling.Runs (compile ctx Q final p) trace result) :
    (partition ctx Q).CachedKeys result.2 (terminalCompletion ctx Q (final result.1)) ∧
      Recorded (dependencyKeys ctx Q) result.2 trace := by
  have h := (partition ctx Q).program_recorded (schedule ctx Q) (callerPlan ctx Q)
    (schedule_ordered ctx Q) (caller_coherent ctx Q) final p run
  exact ⟨by simpa only [finishPackets_eq] using h.1.1,h.2⟩

theorem compile_trace_cached (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K)
    {trace result} (run : Sampling.Runs (compile ctx Q final p) trace result) :
    ∀ allocation ∈ trace, result.2 allocation.1.1 = some allocation.2 :=
  (dependencyMemo_runs_cache (dependencyKeys ctx Q) _ _ run).2

theorem compile_trace_history (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K)
    {trace result} (run : Sampling.Runs (compile ctx Q final p) trace result) :
    ∀ allocation ∈ trace,
      allocation.1.2 = dependencyHistory (dependencyKeys ctx Q) result.2 allocation.1.1 :=
  safe_runs_history (dependencyKeys ctx Q) _ _
    ((partition ctx Q).safe_program (schedule ctx Q) (callerPlan ctx Q) (schedule_ordered ctx Q)
      (caller_coherent ctx Q) final p (fun _ => none)) run

/-- Every prior caller-output block is already present in the current WHIR
allocation's private annotation, with exactly its immutable raw-cache value. -/
theorem compile_caller_history (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K)
    {trace result} (run : Sampling.Runs (compile ctx Q final p) trace result)
    (allocation : Sigma (AllocationAnswer ctx Q)) (member : allocation ∈ trace)
    (packet : Packet ctx Q) (key : allocation.1.1 = .inl packet)
    (raw : (partition ctx Q).Garbage) (caller : raw ∈ callerGroups ctx Q packet) :
    ∃ answer, (⟨.inr raw,answer⟩ : Sigma (GroupAnswer ctx Q)) ∈ allocation.1.2 ∧
      result.2 (.inr raw) = some answer := by
  have dependency : (.inr raw : GroupKey ctx Q) ∈ dependencyKeys ctx Q allocation.1.1 := by
    rw [key]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨raw,caller,rfl⟩)
  have ready := ((recorded ctx Q final p run).2 allocation.1.1 allocation.2
    (compile_trace_cached ctx Q final p run allocation member)).1
  obtain ⟨answer,hit⟩ := ready _ dependency
  refine ⟨answer,?_,hit⟩
  rw [compile_trace_history ctx Q final p run allocation member]
  exact List.mem_filterMap.mpr ⟨.inr raw,dependency,by rw [hit]; rfl⟩

/-- A deterministic total evaluator for replaying an already completed cache.
The zero value is irrelevant on every actual draw, as proved by persistence. -/
def cacheOracle (ctx : Context) (Q : Nat)
    (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q))
    (key : AllocationKey ctx Q) : AllocationAnswer ctx Q key :=
  match key with
  | (.inl packet,_) => (cache (.inl packet)).getD (fun _ _ => 0)
  | (.inr garbage,_) => (cache (.inr garbage)).getD (fun _ => 0)

theorem cacheOracle_hit (ctx : Context) (Q : Nat)
    (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q))
    (key : AllocationKey ctx Q) (answer : AllocationAnswer ctx Q key)
    (hit : cache key.1 = some answer) :
    cacheOracle ctx Q cache key = answer := by
  rcases key with ⟨key,history⟩
  cases key <;> simp_all [cacheOracle]

/-- Reconstruction recovers the exact original allocation trace and result.
It cannot choose a new label from final state: it reruns the original causal
program using only its immutable previously allocated answers. -/
theorem compile_reconstruct (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K)
    {trace result} (run : Sampling.Runs (compile ctx Q final p) trace result) :
    Sampling.execute (cacheOracle ctx Q result.2) (compile ctx Q final p) = (result,trace) := by
  apply execute_eq_of_runs _ run
  intro allocation member
  exact cacheOracle_hit ctx Q result.2 allocation.1 allocation.2
    (compile_trace_cached ctx Q final p run allocation member)

/-- Ancestor allocation, garbage, repeated blocks, early stops, and final
completion all share this worst-case bound on every operational branch. -/
theorem cap (ctx : Context) (Q : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (p : Sampling (RawKey Q) (fun _ => Digest32) R K)
    {trace result} (run : Sampling.Runs (compile ctx Q final p) trace result) :
    trace.length ≤ allocationBudget ctx*(K+1) := by
  simpa only [Nat.mul_add, Nat.mul_one] using run.length_le

end Concrete
end Whir.RawOracleCoupling
