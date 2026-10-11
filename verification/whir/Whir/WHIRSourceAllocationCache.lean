import Whir.WHIRSourceResolver
import Whir.WHIRSourceAllocationOrigin

namespace Whir.WHIRSourceAllocationCache
open FiatShamirGame DuplexModeGame RawOracleCoupling.Concrete
open WHIRCallerRegistry WHIRSourceChronology WHIRSourceResolver WHIRSourceRawCache
open WHIRObservableAllocations WHIRSourceAllocationOrigin

variable {cap : Nat} {R : Type}

private theorem recode_final_cons (registry : Public) (Q : Nat)
    (resolver : WHIRCausalRawROM.Resolver (context registry) Q cap)
    (state : CausalBindingState.State cap) (key : AllocationKey (context registry) Q)
    (answer : AllocationAnswer (context registry) Q key)
    (rest : List (Sigma (AllocationAnswer (context registry) Q))) :
    ((WHIRCausalRawROM.decorator (context registry) rfl Q cap resolver).traceRecode state
      (⟨key,answer⟩ :: rest)).2 =
    ((WHIRCausalRawROM.decorator (context registry) rfl Q cap resolver).traceRecode
      ((resolver.after (WHIRCausalRawROM.prepare (context registry) rfl Q cap resolver state key).1
        key answer).state) rest).2 := by
  rcases key with ⟨group,history⟩
  cases group <;> rfl

def traceEntries (registry : Public) (Q : Nat)
    (trace : List (Sigma (AllocationAnswer (context registry) Q))) : List (RawKey Q × Digest32) :=
  trace.reverse.flatMap (fun entry => groupEntries (context registry) Q entry.1.1 entry.2)

/-- The finite raw cache contains exactly allocated group cells, newest allocation first. Preparing roots and claims does not add any raw reply. -/
theorem recode_rawAnswers (registry : Public) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : Counts Q source) (state : CausalBindingState.State cap)
    (trace : List (Sigma (AllocationAnswer (context registry) Q))) :
    (((WHIRCausalRawROM.decorator (context registry) rfl Q cap
      (privateResolver registry Q seed source counted)).traceRecode state trace).2).rawAnswers Q =
      traceEntries registry Q trace ++ state.rawAnswers Q := by
  induction trace generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key,answer⟩
      rw [recode_final_cons,ih]
      change traceEntries registry Q rest ++
        (addGroup (context registry) Q
          (WHIRCausalRawROM.prepare (context registry) rfl Q cap
            (privateResolver registry Q seed source counted) state key).1 key.1 answer).rawAnswers Q = _
      rw [addGroup_entries,privatePrepare_raw]
      simp only [traceEntries,List.reverse_cons,List.flatMap_append,List.flatMap_cons,
        List.flatMap_nil,List.append_nil,List.append_assoc]

theorem traceEntries_agrees (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (trace : List (Sigma (AllocationAnswer (context registry) Q)))
    (agrees : TraceAgrees registry Q ro trace) : LogAgrees ro (traceEntries registry Q trace) := by
  intro raw member
  obtain ⟨entry,entryMember,member⟩ := List.mem_flatMap.mp member
  have answer := agrees entry (List.mem_reverse.mp entryMember)
  rw [answer] at member
  exact groupEntries_table (context registry) Q ro entry.1.1 raw member

theorem recode_agrees (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap) (old : LogAgrees ro (state.rawAnswers Q))
    (trace : List (Sigma (AllocationAnswer (context registry) Q)))
    (agrees : TraceAgrees registry Q ro trace) :
    LogAgrees ro (((WHIRCausalRawROM.decorator (context registry) rfl Q cap
      (privateResolver registry Q seed source counted)).traceRecode state trace).2.rawAnswers Q) := by
  rw [recode_rawAnswers]
  intro raw member
  rcases List.mem_append.mp member with fresh | prior
  · exact traceEntries_agrees registry Q ro trace agrees raw fresh
  · exact old raw prior

theorem recode_contains (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap) (old : LogAgrees ro (state.rawAnswers Q))
    (trace : List (Sigma (AllocationAnswer (context registry) Q)))
    (agrees : TraceAgrees registry Q ro trace)
    (entry : Sigma (AllocationAnswer (context registry) Q)) (member : entry ∈ trace)
    (raw : RawKey Q) (answer : Digest32)
    (cell : (raw,answer) ∈ groupEntries (context registry) Q entry.1.1 entry.2) :
    cache Q ((WHIRCausalRawROM.decorator (context registry) rfl Q cap
      (privateResolver registry Q seed source counted)).traceRecode state trace).2 raw = some answer := by
  apply (cache_hit_iff Q ro _ (recode_agrees registry Q ro seed source counted state old trace agrees)
    raw answer).mpr
  rw [recode_rawAnswers]
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨entry,List.mem_reverse.mpr member,cell⟩)

/-- Every answer emitted by a table replay is the actual allocated group value, independently of any inherited cache entries. -/
theorem replay_agrees (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (keys : List (GroupKey (context registry) Q)) (cache : WHIRPublicBackfill.PublicCache (context registry) Q) :
    TraceAgrees registry Q ro
      (tableReplay (dependencyKeys (context registry) Q) ((partition (context registry) Q).split ro) keys cache).2 := by
  induction keys generalizing cache with
  | nil => intro entry member; cases member
  | cons key rest ih =>
      cases hit : cache key with
      | some answer => simpa only [tableReplay,hit] using ih cache
      | none =>
          intro entry member
          simp only [tableReplay,hit,List.mem_cons] at member
          rcases member with equal | member
          · subst entry; rfl
          · exact ih _ entry member

/-- Coverage of a concrete replay prefix transports to the actual finite raw cache maintained by the causal resolver, not an arbitrary supplied oracle. -/
theorem covered_raw (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (keys : List (GroupKey (context registry) Q)) (raw : RawKey Q)
    (covered : RawCovered (context registry) Q
      (tableReplay (dependencyKeys (context registry) Q) ((partition (context registry) Q).split ro)
        keys (fun _ => none)).1 raw) :
    cache Q ((WHIRCausalRawROM.decorator (context registry) rfl Q cap
      (privateResolver registry Q seed source counted)).traceRecode (CausalBindingState.empty cap)
        (tableReplay (dependencyKeys (context registry) Q) ((partition (context registry) Q).split ro)
          keys (fun _ => none)).2).2 raw = some (ro raw) := by
  let trace := (tableReplay (dependencyKeys (context registry) Q)
    ((partition (context registry) Q).split ro) keys (fun _ => none)).2
  have agreed : TraceAgrees registry Q ro trace := replay_agrees registry Q ro keys _
  unfold RawCovered at covered
  split at covered
  · rename_i pos recognized
    obtain ⟨answer,hit⟩ := covered
    obtain ⟨history,member⟩ := replay_cached (dependencyKeys (context registry) Q)
      ((partition (context registry) Q).split ro) keys _ answer hit
    have value := agreed ⟨(.inl pos.1,history),answer⟩ member
    change answer = (partition (context registry) Q).split ro (.inl pos.1) at value
    have encoded := RawWHIRKeys.encode_recognize (context registry) Q raw pos recognized
    apply recode_contains registry Q ro seed source counted _ (by intro e h; cases h)
      trace agreed _ member raw (ro raw)
    change (raw,ro raw) ∈ List.ofFn (fun block =>
      (RawWHIRKeys.encode (context registry) Q ⟨pos.1,block⟩,answer block))
    apply List.mem_ofFn.mpr
    refine ⟨pos.2,?_⟩
    rw [value]
    change (RawWHIRKeys.encode (context registry) Q pos,
      ro (RawWHIRKeys.encode (context registry) Q pos)) = (raw,ro raw)
    rw [encoded]
  · rename_i recognized
    obtain ⟨answer,hit⟩ := covered
    obtain ⟨history,member⟩ := replay_cached (dependencyKeys (context registry) Q)
      ((partition (context registry) Q).split ro) keys _ answer hit
    have value := agreed ⟨(.inr ⟨raw,recognized⟩,history),answer⟩ member
    change answer = ro raw at value
    subst answer
    exact recode_contains registry Q ro seed source counted _ (by intro e h; cases h)
      trace agreed _ member raw (ro raw) (by simp [groupEntries])

end Whir.WHIRSourceAllocationCache
