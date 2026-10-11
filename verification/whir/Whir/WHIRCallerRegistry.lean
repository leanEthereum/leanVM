import Whir.WHIRCallerSource
import Whir.WHIRObservableAllocations

/-! Production stack-caller registry. A statement selects only fixed public
layout data. Profiles, frame boundaries, lanes and caller-output budgets are
computed by the concrete source interpreter. Allocation labels contribute only
actual garbage-key caller samples; absent samples never receive default bytes.
The table-backed compiler trace theorem derives their completeness and immutable
values from the shared allocation cache, including prequeries before the source
has announced its claims. `packetRoot` captures the initial physical root without
waiting for these samples; `packetRequest_root` follows from original source
semantics and exact framing, not an added root-agreement acceptance check.
Complete requests are stable under later allocation-history extension; arbitrary
future WHIR vectors also preserve malformed `none` results. -/
namespace Whir.WHIRCallerRegistry
open FiatShamirGame DuplexModeGame TypedOracleCompiler TypedFiatShamirGame
open RawOracleCoupling RawOracleCoupling.Concrete WHIRCallerClaims
open RawWHIRKeys (Packet Context)

local instance : DecidableEq Terminal := by
  intro a b
  cases a <;> cases b <;> simp <;> infer_instance

local instance : DecidableEq Coordinate := by
  intro a b
  cases a
  cases b
  simp only [Coordinate.mk.injEq]
  infer_instance

structure Public where
  iv : Digest32
  domain : Digest32
  layouts : Digest32 → Option CallerLayout
  callerOutputCap : Nat

/-- Unsupported opening geometry and oversized caller programs have no catalog
entry. In particular, no supplied profile or claim data is trusted. -/
def selection (registry : Public) (statement : Digest32) : Option (CallerLayout × ParameterBounds.Profile) := do
  let layout ← registry.layouts statement
  let profile ← callerProfile layout
  if callerOutputCap layout ≤ registry.callerOutputCap then some (layout,profile) else none

def context (registry : Public) : Context where
  mode := .stack
  iv := registry.iv
  domain := registry.domain
  catalog := fun statement => (selection registry statement).map Prod.snd
  entryLength := fun statement => ((selection registry statement).map (callerEntryLength ∘ Prod.fst)).getD 0
  callerOutputCap := registry.callerOutputCap

theorem selection_spec (registry : Public) (statement : Digest32)
    (layout : CallerLayout) (profile : ParameterBounds.Profile)
    (selected : selection registry statement = some (layout,profile)) :
    registry.layouts statement = some layout ∧ callerProfile layout = some profile ∧
      callerOutputCap layout ≤ registry.callerOutputCap := by
  unfold selection at selected
  cases hl : registry.layouts statement with
  | none => simp [hl] at selected
  | some l =>
    rw [hl] at selected
    change (Option.bind (callerProfile l) (fun p =>
      if callerOutputCap l ≤ registry.callerOutputCap then some (l,p) else none)) =
      some (layout,profile) at selected
    cases hp : callerProfile l with
    | none => simp [hp] at selected
    | some p =>
      rw [hp] at selected
      change (if callerOutputCap l ≤ registry.callerOutputCap then some (l,p) else none) =
        some (layout,profile) at selected
      split at selected
      next bound =>
        cases Option.some.inj selected
        exact ⟨rfl,hp,bound⟩
      next => simp at selected

/-- Every valid packet determines a concrete public source layout. -/
def packetLayout (registry : Public) (Q : Nat) (packet : Packet (context registry) Q) : CallerLayout :=
  match h : selection registry packet.val.statement with
  | some selected => selected.1
  | none => False.elim (by
      have catalog := packet.property.1
      simp [context,h] at catalog)

theorem packet_selection (registry : Public) (Q : Nat) (packet : Packet (context registry) Q) :
    selection registry packet.val.statement = some (packetLayout registry Q packet,packet.val.profile) := by
  have catalog := packet.property.1
  unfold packetLayout
  split
  next selected h =>
    simp only [context,h,Option.map_some] at catalog
    rw [h]
    exact congrArg (fun p => some (selected.1,p)) (Option.some.inj catalog)
  next h => simp [context,h] at catalog

theorem packet_geometry (registry : Public) (Q : Nat) (packet : Packet (context registry) Q) :
    registry.layouts packet.val.statement = some (packetLayout registry Q packet) ∧
    callerProfile (packetLayout registry Q packet) = some packet.val.profile ∧
    callerOutputCap (packetLayout registry Q packet) ≤ registry.callerOutputCap ∧
    openingMatches packet.val.profile (callerLanes (packetLayout registry Q packet))
      (packetLayout registry Q packet) = true ∧
    packet.val.entryFrames.length = callerEntryLength (packetLayout registry Q packet) := by
  have selected := packet_selection registry Q packet
  obtain ⟨layout,profile,bounded⟩ := selection_spec registry _ _ _ selected
  refine ⟨layout,profile,bounded,callerProfile_matches _ _ profile,?_⟩
  have frames := RawWHIRKeys.packet_entryLength (context registry) Q packet
  simpa only [context,selected,Option.map_some,Option.getD_some,Function.comp_apply] using frames

/-- Only garbage groups can supply caller bytes. WHIR group answers are skipped,
including later packets and current-packet sample vectors. -/
def garbageAnswer {ctx : Context} {Q : Nat} (raw : (partition ctx Q).Garbage) :
    List (Sigma (GroupAnswer ctx Q)) → Option Digest32
  | [] => none
  | ⟨.inl _,_⟩ :: rest => garbageAnswer raw rest
  | ⟨.inr key,value⟩ :: rest => if key = raw then some value else garbageAnswer raw rest

def callerAnswers (ctx : Context) (Q : Nat) (packet : Packet ctx Q)
    (history : List (Sigma (GroupAnswer ctx Q))) (q : Coordinate) : Option Digest32 :=
  if member : q ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val) then
    garbageAnswer (RawWHIRKeys.callerOutputKey ctx Q packet q member) history
  else none

def packetRequest (registry : Public) (Q cap : Nat) (packet : Packet (context registry) Q)
    (history : List (Sigma (GroupAnswer (context registry) Q))) :
    Option (CausalBindingState.ClaimRequest cap packet.val.profile) :=
  decodeAvailableRequest cap packet.val.profile (callerLanes (packetLayout registry Q packet))
    (packetLayout registry Q packet) (RawWHIRKeys.entry (context registry) packet.val)
    (callerAnswers (context registry) Q packet history)

/-- Cache consistency suffices even if the annotation contains repeated keys;
the first matching entry has the same immutable value as every other one. -/
theorem garbageAnswer_cache {ctx : Context} {Q : Nat}
    (raw : (partition ctx Q).Garbage) (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q))
    (history : List (Sigma (GroupAnswer ctx Q)))
    (consistent : ∀ item ∈ history, cache item.1 = some item.2)
    (complete : ∃ answer, (⟨.inr raw,answer⟩ : Sigma (GroupAnswer ctx Q)) ∈ history) :
    garbageAnswer raw history = cache (.inr raw) := by
  induction history with
  | nil => obtain ⟨a,h⟩ := complete; simp at h
  | cons item rest ih =>
    have tailConsistent : ∀ item ∈ rest, cache item.1 = some item.2 :=
      fun item member => consistent item (List.mem_cons_of_mem _ member)
    obtain ⟨key,value⟩ := item
    cases key with
    | inl packet =>
      apply ih tailConsistent
      obtain ⟨answer,member⟩ := complete
      refine ⟨answer,(List.mem_cons.mp member).resolve_left ?_⟩
      intro same
      have impossible := congrArg Sigma.fst same
      contradiction
    | inr key =>
      by_cases same : key = raw
      · subst key
        simp only [garbageAnswer,↓reduceIte]
        exact (consistent ⟨.inr raw,value⟩ (List.mem_cons_self)).symm
      · simp only [garbageAnswer,ite_eq_right same]
        apply ih tailConsistent
        obtain ⟨answer,member⟩ := complete
        refine ⟨answer,(List.mem_cons.mp member).resolve_left ?_⟩
        intro equal
        exact same (Sum.inr.inj (congrArg Sigma.fst equal)).symm

theorem dependencyHistory_consistent {ctx : Context} {Q : Nat}
    (cache : Cache (GroupKey ctx Q) (GroupAnswer ctx Q)) (key : GroupKey ctx Q) :
    ∀ item ∈ dependencyHistory (dependencyKeys ctx Q) cache key,
      cache item.1 = some item.2 := by
  intro item member
  obtain ⟨k,_,hit⟩ := List.mem_filterMap.mp member
  cases h : cache k with
  | none => simp [h] at hit
  | some value =>
    simp only [h,Option.map_some,Option.some.injEq] at hit
    cases hit
    exact h

theorem callerAnswers_compile {ctx : Context} {Q : Nat} {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (program : Sampling (RawKey Q) (fun _ => Digest32) R K)
    {trace result} (run : Sampling.Runs (compile ctx Q final program) trace result)
    (allocation : Sigma (AllocationAnswer ctx Q)) (member : allocation ∈ trace)
    (packet : Packet ctx Q) (key : allocation.1.1 = .inl packet)
    (q : Coordinate) (prior : q ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val)) :
    callerAnswers ctx Q packet allocation.1.2 q =
      result.2 (.inr (RawWHIRKeys.callerOutputKey ctx Q packet q prior)) := by
  let raw := RawWHIRKeys.callerOutputKey ctx Q packet q prior
  have caller : raw ∈ RawWHIRKeys.callerGroups ctx Q packet := by
    exact List.mem_map.mpr ⟨⟨q,prior⟩,List.mem_attach _ _,rfl⟩
  obtain ⟨answer,present,_⟩ := compile_caller_history ctx Q final program run allocation member packet key raw caller
  simp only [callerAnswers,dite_eq_left prior]
  apply garbageAnswer_cache _ result.2 allocation.1.2
  · rw [compile_trace_history ctx Q final program run allocation member]
    exact dependencyHistory_consistent result.2 allocation.1.1
  · exact ⟨answer,present⟩

/-- Raw-table values are read at the exact physical caller coordinates. -/
def tableCallerAnswers (ctx : Context) (Q : Nat) (packet : Packet ctx Q)
    (table : RawKey Q → Digest32) (q : Coordinate) : Option Digest32 :=
  if prior : q ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val) then
    some (table (RawWHIRKeys.callerOutputKey ctx Q packet q prior).val)
  else none

theorem callerAnswers_table_compile {ctx : Context} {Q : Nat} {R : Type} {K : Nat}
    (final : R → Option (Packet ctx Q)) (program : Sampling (RawKey Q) (fun _ => Digest32) R K)
    (table : RawKey Q → Digest32)
    (allocation : Sigma (AllocationAnswer ctx Q))
    (member : allocation ∈ (Sampling.execute
      (WHIRObservableAllocations.allocationOracle ctx Q table) (compile ctx Q final program)).2)
    (packet : Packet ctx Q) (key : allocation.1.1 = .inl packet) :
    callerAnswers ctx Q packet allocation.1.2 = tableCallerAnswers ctx Q packet table := by
  have run := Sampling.execute_runs (WHIRObservableAllocations.allocationOracle ctx Q table)
    (compile ctx Q final program)
  rw [WHIRObservableAllocations.compile_cache] at run
  funext q
  by_cases prior : q ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val)
  · rw [callerAnswers_compile final program run allocation member packet key q prior]
    let raw := RawWHIRKeys.callerOutputKey ctx Q packet q prior
    have caller : raw ∈ RawWHIRKeys.callerGroups ctx Q packet :=
      List.mem_map.mpr ⟨⟨q,prior⟩,List.mem_attach _ _,rfl⟩
    obtain ⟨answer,_,hit⟩ :=
      compile_caller_history ctx Q final program run allocation member packet key raw caller
    have value := tableExecution_cache ctx Q final program table (.inr raw) answer hit
    change table raw.val = answer at value
    simp only [tableCallerAnswers,dite_eq_left prior]
    change (tableExecution ctx Q final program table).2 (.inr raw) = some (table raw.val)
    rw [value]
    exact hit
  · simp only [callerAnswers,tableCallerAnswers,dite_eq_right prior]

theorem packetRequest_table_compile (registry : Public) (Q cap : Nat) {R : Type} {K : Nat}
    (final : R → Option (Packet (context registry) Q))
    (program : Sampling (RawKey Q) (fun _ => Digest32) R K) (table : RawKey Q → Digest32)
    (allocation : Sigma (AllocationAnswer (context registry) Q))
    (member : allocation ∈ (Sampling.execute
      (WHIRObservableAllocations.allocationOracle (context registry) Q table)
      (compile (context registry) Q final program)).2)
    (packet : Packet (context registry) Q) (key : allocation.1.1 = .inl packet) :
    packetRequest registry Q cap packet allocation.1.2 =
      decodeAvailableRequest cap packet.val.profile (callerLanes (packetLayout registry Q packet))
        (packetLayout registry Q packet) (RawWHIRKeys.entry (context registry) packet.val)
        (tableCallerAnswers (context registry) Q packet table) := by
  unfold packetRequest
  rw [callerAnswers_table_compile final program table allocation member packet key]

theorem garbageAnswer_missing {ctx : Context} {Q : Nat}
    (raw : (partition ctx Q).Garbage) (history : List (Sigma (GroupAnswer ctx Q)))
    (missing : ∀ item ∈ history, item.1 ≠ .inr raw) :
    garbageAnswer raw history = none := by
  induction history with
  | nil => rfl
  | cons item rest ih =>
    have tailMissing : ∀ item ∈ rest, item.1 ≠ .inr raw :=
      fun item member => missing item (List.mem_cons_of_mem _ member)
    obtain ⟨key,value⟩ := item
    cases key with
    | inl packet => exact ih tailMissing
    | inr key =>
      have different : key ≠ raw := fun equal =>
        missing ⟨.inr key,value⟩ List.mem_cons_self (congrArg Sum.inr equal)
      simpa only [garbageAnswer,ite_eq_right different] using ih tailMissing

theorem garbageAnswer_append_irrelevant {ctx : Context} {Q : Nat}
    (raw : (partition ctx Q).Garbage) (history extra : List (Sigma (GroupAnswer ctx Q)))
    (irrelevant : ∀ item ∈ extra, item.1 ≠ .inr raw) :
    garbageAnswer raw (history ++ extra) = garbageAnswer raw history := by
  induction history with
  | nil => exact garbageAnswer_missing raw extra irrelevant
  | cons item rest ih =>
    obtain ⟨key,value⟩ := item
    cases key with
    | inl packet => exact ih
    | inr key => simp only [List.cons_append,garbageAnswer,ih]

theorem packetRequest_prior_only (registry : Public) (Q cap : Nat)
    (packet : Packet (context registry) Q)
    (a b : List (Sigma (GroupAnswer (context registry) Q)))
    (agree : ∀ q ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry (context registry) packet.val),
      callerAnswers (context registry) Q packet a q = callerAnswers (context registry) Q packet b q) :
    packetRequest registry Q cap packet a = packetRequest registry Q cap packet b :=
  decodeAvailableRequest_prior_only _ _ _ _ _ _ _ agree

theorem packetRequest_append_irrelevant (registry : Public) (Q cap : Nat)
    (packet : Packet (context registry) Q)
    (history extra : List (Sigma (GroupAnswer (context registry) Q)))
    (irrelevant : ∀ q (prior : q ∈ WHIRCallerOutputs.callerOutputs
      (RawWHIRKeys.entry (context registry) packet.val)), ∀ item ∈ extra,
      item.1 ≠ .inr (RawWHIRKeys.callerOutputKey (context registry) Q packet q prior)) :
    packetRequest registry Q cap packet (history ++ extra) = packetRequest registry Q cap packet history := by
  apply packetRequest_prior_only
  intro q prior
  simp only [callerAnswers,dite_eq_left prior]
  exact garbageAnswer_append_irrelevant _ history extra (irrelevant q prior)

/-- In particular, appending any future WHIR vectors cannot affect a request,
including a malformed entry whose request is `none`. -/
theorem packetRequest_append_whir (registry : Public) (Q cap : Nat)
    (packet : Packet (context registry) Q)
    (history : List (Sigma (GroupAnswer (context registry) Q)))
    (extra : List ((p : Packet (context registry) Q) × (Fin (RawWHIRKeys.blocks (context registry) p.val) → Digest32))) :
    packetRequest registry Q cap packet
      (history ++ extra.map (fun item => ⟨.inl item.1,item.2⟩)) =
      packetRequest registry Q cap packet history := by
  apply packetRequest_append_irrelevant
  intro q prior item member
  obtain ⟨item,_,rfl⟩ := List.mem_map.mp member
  intro impossible
  contradiction

theorem packetRequest_missing (registry : Public) (Q cap : Nat)
    (packet : Packet (context registry) Q)
    (history : List (Sigma (GroupAnswer (context registry) Q)))
    (q : Coordinate) (prior : q ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry (context registry) packet.val))
    (missing : ∀ item ∈ history,
      item.1 ≠ .inr (RawWHIRKeys.callerOutputKey (context registry) Q packet q prior)) :
    packetRequest registry Q cap packet history = none := by
  apply decodeAvailableRequest_missing _ _ _ _ _ _ q prior
  simp only [callerAnswers,dite_eq_left prior]
  exact garbageAnswer_missing _ history missing

/-- Packet suffixes need not agree. Complete entry identity and the same prior
caller samples already determine the entire optional request, not merely its
successful cases. -/
theorem packetRequest_same_entry (registry : Public) (Q cap : Nat)
    (a b : Packet (context registry) Q)
    (ha hb : List (Sigma (GroupAnswer (context registry) Q)))
    (same : RawWHIRKeys.entry (context registry) a.val = RawWHIRKeys.entry (context registry) b.val)
    (answers : ∀ q ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry (context registry) a.val),
      callerAnswers (context registry) Q a ha q = callerAnswers (context registry) Q b hb q) :
    HEq (packetRequest registry Q cap a ha) (packetRequest registry Q cap b hb) := by
  have statement : a.val.statement = b.val.statement := congrArg FramedHistory.statement same
  have profile : a.val.profile = b.val.profile := by
    apply Option.some.inj
    exact a.property.1.symm.trans (statement.symm ▸ b.property.1)
  have layout : packetLayout registry Q a = packetLayout registry Q b := by
    have first := packet_selection registry Q a
    have second := packet_selection registry Q b
    rw [statement,second] at first
    exact (congrArg Prod.fst (Option.some.inj first)).symm
  unfold packetRequest
  rw [layout]
  rw [profile]
  apply heq_of_eq
  rw [← same]
  exact decodeAvailableRequest_prior_only _ _ _ _ _ _ _ answers

theorem garbageAnswer_append_hit {ctx : Context} {Q : Nat}
    (raw : (partition ctx Q).Garbage) (history extra : List (Sigma (GroupAnswer ctx Q)))
    (answer : Digest32) (hit : garbageAnswer raw history = some answer) :
    garbageAnswer raw (history ++ extra) = some answer := by
  induction history with
  | nil => cases hit
  | cons item rest ih =>
    obtain ⟨key,value⟩ := item
    cases key with
    | inl packet => exact ih hit
    | inr key =>
      by_cases same : key = raw
      · simpa only [List.cons_append,garbageAnswer,ite_eq_left same] using hit
      · simp only [garbageAnswer,ite_eq_right same] at hit
        simpa only [List.cons_append,garbageAnswer,ite_eq_right same] using ih hit

/-- Once a valid request is available, arbitrary later allocations cannot
overwrite its caller samples, even if a malformed supplied history repeats a
key with a different later value. The compiler's actual histories additionally
satisfy the stronger cache-consistency theorem above. -/
theorem packetRequest_append_of_some (registry : Public) (Q cap : Nat)
    (packet : Packet (context registry) Q)
    (history extra : List (Sigma (GroupAnswer (context registry) Q)))
    (request : CausalBindingState.ClaimRequest cap packet.val.profile)
    (accepted : packetRequest registry Q cap packet history = some request) :
    packetRequest registry Q cap packet (history ++ extra) = some request := by
  have available : ∀ q ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry (context registry) packet.val),
      (callerAnswers (context registry) Q packet history q).isSome = true := by
    unfold packetRequest decodeAvailableRequest at accepted
    split at accepted
    next complete => exact List.all_eq_true.mp complete
    next => simp at accepted
  rw [← accepted]
  apply packetRequest_prior_only
  intro q prior
  have present := available q prior
  simp only [callerAnswers,dite_eq_left prior] at present ⊢
  cases hit : garbageAnswer (RawWHIRKeys.callerOutputKey (context registry) Q packet q prior) history with
  | none => simp [hit] at present
  | some answer =>
    exact garbageAnswer_append_hit _ history extra answer hit

/-- Commitment capture is available before warming any caller-output groups. -/
def packetRoot (registry : Public) (Q : Nat) (packet : Packet (context registry) Q) : Option Digest32 :=
  initialRoot (packetLayout registry Q packet) (RawWHIRKeys.entry (context registry) packet.val)

theorem packetRequest_root (registry : Public) (Q cap : Nat)
    (packet : Packet (context registry) Q)
    (history : List (Sigma (GroupAnswer (context registry) Q)))
    (request : CausalBindingState.ClaimRequest cap packet.val.profile)
    (accepted : packetRequest registry Q cap packet history = some request) :
    packetRoot registry Q packet = some request.root :=
  decodeAvailableRequest_initialRoot _ _ _ _ _ _ request accepted

end Whir.WHIRCallerRegistry
