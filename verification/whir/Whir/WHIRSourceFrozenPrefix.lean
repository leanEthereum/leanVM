import Whir.WHIRSourceRootPolicy
import Whir.WHIRPhysicalSnapshots
import Whir.WHIRSourceResolver
import Whir.WHIRRealSimulator
import Whir.WHIRObservableAllocations
import Whir.WHIRSourcePartialMonotone
import Whir.WHIRSourceAllocationOrigin
import Whir.WHIRSourceAllocationCache
import Whir.WHIRSourceBackfill
import Whir.WHIRSourceRawProgram

/-! Actual-source first-freeze provenance for the shared compression experiment.

`actual_backfill_retained` constructs the historical/full-C-prefix, ordinary
tag-zero saturation, root-policy membership, retained-record authenticity and
table-domain fields needed by `PublicMerkleProbability.FrozenOpeningBad`.
No root-cover or verifier-correctness premise is introduced.

`allocationTrace_compiler` identifies the analyzed allocation path with the
source-budgeted raw compiler, including caller/ancestor warming and selected
final backfill. `public_replayState` identifies its chosen real seed/raw-table
resolver state with the public event-only resolver. The first-freeze induction
skips settled repeated prefixes before appending newly observed source events;
it never recaptures an old root at a later cursor. Pending roots come from input
headers and encoded footprints, never the fresh reply. Source errors remain
recorded but do not suppress later C observations.

Full-C expansion retains repeated calls and hidden construction internals.
Public-log transport uses membership, not equality with the observer log.
This is deterministic provenance, not an additional probability assumption. -/
namespace Whir.WHIRSourceFrozenPrefix
open FiatShamirGame DuplexModeGame DuplexFraming PublicCompressionProgram
open WHIRSourceChronology WHIRSourceRootPolicy WHIRCallerRegistry
open PublicMerkleLog

variable {cap : Nat} {R : Type}

/-- Every answered mode observation contributes its complete actual C execution. -/
def expand (C : PrimitiveOracle) (iv : Digest32) (seen : List Observation) : PublicLog :=
  seen.flatMap fun o => toLog (TypedOracleCompiler.Sampling.execute C (queryCalls iv o.query)).2

theorem expand_append (C : PrimitiveOracle) (iv : Digest32) (a b : List Observation) :
    expand C iv (a ++ b) = expand C iv a ++ expand C iv b := by
  simp [expand]

theorem expand_real (C : PrimitiveOracle) (iv : Digest32) (p : Program R)
    (Q : Nat) (counted : DuplexModeGame.Counts Q p) :
    expand C iv (runReal C iv p).view.observations = primitiveLog C iv p Q counted := by
  induction p generalizing Q with
  | done => rfl
  | ask q next ih =>
    simp only [runReal,DuplexModeGame.prepend,expand,List.flatMap_cons,
      primitiveLog,PublicCompressionProgram.compile,TypedOracleCompiler.Sampling.execute_pad,
      TypedOracleCompiler.Sampling.execute_bind,execute_mapResult,toLog,List.map_append,
      queryCalls_eval]
    exact congrArg (_ ++ ·) (ih (realAnswer C iv q) (Q-q.cost) (counted.2 _))

/-- An actual partial raw replay ends at a mode-query boundary, hence before
all C calls of the still unanswered mode query. No query answer is invented. -/
theorem observation_prefix (C : PrimitiveOracle) (iv : Digest32) (p : Program R)
    (Q : Nat) (counted : DuplexModeGame.Counts Q p) (seen : List Observation)
    (initial : seen.IsPrefix (runReal C iv p).view.observations) :
    (expand C iv seen).IsPrefix (primitiveLog C iv p Q counted) := by
  obtain ⟨suffix,eq⟩ := initial
  refine ⟨expand C iv suffix,?_⟩
  rw [← expand_append,eq,expand_real]

theorem private_observation_prefix (C : PrimitiveOracle) (iv : Digest32)
    (source : Source cap R) (Q : Nat) (counted : WHIRSourceChronology.Counts Q source)
    (cache : RawKey Q → Option Digest32)
    (agrees : DuplexPublicSimulator.CacheAgrees cache (WHIRRealSimulator.rawTable Q C)) :
    (DuplexPublicSimulator.runPartial cache iv
      ((DuplexPublicSimulator.simulator Q).initial C) (WHIRSourceChronology.compile source)
      Q (Nat.le_refl Q) ((compile_counted source Q).mpr counted)).observations.IsPrefix
      (runReal C iv (WHIRSourceChronology.compile source)).view.observations := by
  obtain ⟨suffix,eq⟩ := DuplexPublicSimulator.runPartial_prefix cache
    (WHIRRealSimulator.rawTable Q C) agrees iv ((DuplexPublicSimulator.simulator Q).initial C)
    (WHIRSourceChronology.compile source) Q (Nat.le_refl Q) ((compile_counted source Q).mpr counted)
  rw [WHIRRealSimulator.real_ideal_view C iv _ ((compile_counted source Q).mpr counted)]
  exact ⟨suffix,eq.symm⟩

theorem private_fullC_prefix (C : PrimitiveOracle) (iv : Digest32)
    (source : Source cap R) (Q : Nat) (counted : WHIRSourceChronology.Counts Q source)
    (cache : RawKey Q → Option Digest32)
    (agrees : DuplexPublicSimulator.CacheAgrees cache (WHIRRealSimulator.rawTable Q C)) :
    (expand C iv (DuplexPublicSimulator.runPartial cache iv
      ((DuplexPublicSimulator.simulator Q).initial C) (WHIRSourceChronology.compile source)
      Q (Nat.le_refl Q) ((compile_counted source Q).mpr counted)).observations).IsPrefix
      (primitiveLog C iv (WHIRSourceChronology.compile source) Q
        ((compile_counted source Q).mpr counted)) :=
  observation_prefix C iv _ Q _ _ (private_observation_prefix C iv source Q counted cache agrees)

/-- All tag-zero calls in the expanded prefix are actual visible primitive
observations. Hidden construction calls cannot contribute an ordinary node. -/
theorem ordinary_expand (C : PrimitiveOracle) (iv : Digest32) (seen : List Observation)
    (real : ∀ o ∈ seen, o.answer = realAnswer C iv o.query)
    (n : Node) (d : Digest32) (member : (n,d) ∈ expand C iv seen) (ordinary : tag n = 0) :
    ∃ purpose, (⟨.primitive purpose n,d⟩ : Observation) ∈ seen := by
  obtain ⟨o,ho,hm⟩ := List.mem_flatMap.mp member
  cases o with
  | mk q answer =>
    cases q with
    | primitive purpose input =>
      simp only [queryCalls,TypedOracleCompiler.Sampling.execute,toLog,List.map_cons,
        List.map_nil,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hm
      rcases hm with ⟨rfl,rfl⟩
      have ha := real ⟨.primitive purpose n,answer⟩ ho
      change answer = C n at ha
      subst answer
      exact ⟨purpose,ho⟩
    | construction q valid =>
      have positive := construction_tags C iv q valid n d hm
      omega

/-- Public observations are not fabricated by expansion, even with repeated inputs. -/
theorem primitive_expand (C : PrimitiveOracle) (iv : Digest32) (seen : List Observation)
    (real : ∀ o ∈ seen, o.answer = realAnswer C iv o.query)
    (purpose : Purpose) (n : Node) (d : Digest32)
    (member : (⟨.primitive purpose n,d⟩ : Observation) ∈ seen) :
    (n,d) ∈ expand C iv seen := by
  have hd := real ⟨.primitive purpose n,d⟩ member
  change d = C n at hd
  subst d
  apply List.mem_flatMap.mpr
  exact ⟨⟨.primitive purpose n,C n⟩,member,by simp [queryCalls,TypedOracleCompiler.Sampling.execute,toLog]⟩

/-- Finite C replay may run farther than a mode prefix when queries repeat.
Membership, unlike equality of recovered event lists, remains valid. -/
theorem recover_capture (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (seen : List Observation)
    (initial : seen.IsPrefix (runReal C registry.iv (WHIRSourceChronology.compile source)).view.observations)
    (log : PublicLog) (auth : AuthenticLog C log)
    (available : ∀ e ∈ expand C registry.iv seen, e ∈ log)
    (visible : PublicLog) :
    ∀ root ∈ capture registry Q select (recover source seen) visible,
      root ∈ scan registry Q select log source visible := by
  induction source generalizing seen visible with
  | done value =>
    simp [WHIRSourceChronology.recover,capture,eventRoots,visibleAfter,scan]
  | commit root next ih =>
    have initial' : seen.IsPrefix
        (runReal C registry.iv (WHIRSourceChronology.compile next)).view.observations := by
      simpa only [WHIRSourceChronology.compile,map_real,mapExecution] using initial
    intro r member
    simp only [WHIRSourceChronology.recover,prependPrefix,capture,eventRoots,visibleAfter,
      List.cons_append,List.mem_cons] at member
    change r ∈ root :: scan registry Q select log next visible
    rcases member with same | later
    · exact List.mem_cons.mpr (Or.inl same)
    · exact List.mem_cons_of_mem _ (ih seen initial' available visible r later)
  | claims p entry request next ih =>
    have initial' : seen.IsPrefix
        (runReal C registry.iv (WHIRSourceChronology.compile next)).view.observations := by
      simpa only [WHIRSourceChronology.compile,map_real,mapExecution] using initial
    simpa only [WHIRSourceChronology.recover,prependPrefix,capture,eventRoots,visibleAfter,scan] using
      ih seen initial' available visible
  | ask q next ih =>
    cases seen with
    | nil =>
      intro root member
      have hm : root ∈ queryRoots registry Q visible q := by
        simpa [WHIRSourceChronology.recover,capture,eventRoots,visibleAfter] using member
      simp only [scan]
      exact List.mem_append_left _ hm
    | cons o rest =>
      obtain ⟨suffix,eq⟩ := initial
      have split : o = ⟨q,realAnswer C registry.iv q⟩ ∧
          rest ++ suffix = (runReal C registry.iv
            (WHIRSourceChronology.compile (next (realAnswer C registry.iv q)))).view.observations := by
        simpa only [WHIRSourceChronology.compile,runReal,map_real,mapExecution,
          DuplexModeGame.prepend,List.cons_append,List.cons.injEq] using eq
      rcases split with ⟨rfl,tail⟩
      have answer : queryReply registry.iv log q = some (realAnswer C registry.iv q) := by
        rw [queryReply,← queryCalls_eval C registry.iv q]
        apply partialEval_complete C log auth
        intro e he
        exact available e (List.mem_append_left _ he)
      have recur := ih (realAnswer C registry.iv q) rest ⟨suffix,tail⟩
        (fun e he => available e (List.mem_append_right _ he))
        (advance visible q (realAnswer C registry.iv q))
      intro root member
      have hm : root ∈ queryRoots registry Q visible q ++
          capture registry Q select (recover (next (realAnswer C registry.iv q)) rest)
            (advance visible q (realAnswer C registry.iv q)) := by
        simpa only [WHIRSourceChronology.recover,prependPrefix,capture,eventRoots,visibleAfter,List.append_assoc] using member
      simp only [scan,answer]
      rcases List.mem_append.mp hm with first | later
      · exact List.mem_append_left _ first
      · exact List.mem_append_right _ (recur root later)

/-- Concrete root capture at the actual all-C prefix, including zero-cost
commits, the pending request input, and final selection before backfill. -/
theorem source_prefix_captured (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (seen : List Observation)
    (initial : seen.IsPrefix (runReal C registry.iv (WHIRSourceChronology.compile source)).view.observations)
    (root : Digest32) (member : root ∈ capture registry Q select (recover source seen) []) :
    root ∈ policy registry Q select source (expand C registry.iv seen).reverse := by
  have hp := observation_prefix C registry.iv _ Q ((compile_counted source Q).mpr counted) seen initial
  have authentic : AuthenticLog C (expand C registry.iv seen).reverse := by
    intro n d hd
    exact primitiveLog_authentic C registry.iv _ Q ((compile_counted source Q).mpr counted)
      n d (WHIRPhysicalSnapshots.prefix_mem hp (List.mem_reverse.mp hd))
  apply scan_captured
  exact recover_capture registry Q select C source seen initial _ authentic
    (fun _ he => List.mem_reverse.mpr he) [] root member

/-- A successfully parsed first header is unchanged by appending later frames. -/
theorem header_append (registry : Public) (entry : FramedHistory)
    (header : WHIRHeaderRoots.Header)
    (parsed : WHIRHeaderRoots.fromHistory registry entry = some header)
    (suffix : List Frame) :
    WHIRHeaderRoots.fromHistory registry {entry with frames := entry.frames ++ suffix} =
      some header := by
  obtain ⟨domain,statement,layout,selected,root⟩ :=
    WHIRHeaderRoots.fromHistory_sound registry entry header parsed
  have extended := WHIRHeaderRoots.initialRoot_append layout entry header.root root suffix
  simpa only [← statement] using WHIRHeaderRoots.fromHistory_selected registry
    {entry with frames := entry.frames ++ suffix} layout header.profile header.root domain selected extended

/-- Every warmed caller's parsed header was already present in the packet input,
not in the answer subsequently assigned to that caller group. -/
theorem caller_header_packet (registry : Public) (Q : Nat)
    (packet : RawWHIRKeys.Packet (context registry) Q)
    (raw : {raw : RawKey Q // RawWHIRKeys.Garbage (context registry) Q raw})
    (member : raw ∈ RawWHIRKeys.callerGroups (context registry) Q packet)
    (header : WHIRHeaderRoots.Header)
    (parsed : WHIRHeaderRoots.rawHeader registry raw.val = some header) :
    WHIRHeaderRoots.packetHeader registry Q packet = some header := by
  obtain ⟨⟨q,hq⟩,_,rfl⟩ := List.mem_map.mp member
  have decoded := WHIRHeaderRoots.decodeRaw_callerOutputKey (context registry) Q packet q hq
  change WHIRHeaderRoots.decodeRaw registry.iv
    (RawWHIRKeys.callerOutputKey (context registry) Q packet q hq).val = some q at decoded
  have first : WHIRHeaderRoots.fromHistory registry q.history = some header := by
    simpa only [WHIRHeaderRoots.rawHeader,decoded,Option.bind_some] using parsed
  obtain ⟨pre,f,suffix,block,split,_,rfl⟩ :=
    WHIRCallerOutputs.callerOutputs_mem (RawWHIRKeys.entry (context registry) packet.val) q hq
  have extended := header_append registry _ header first (f :: suffix)
  simpa only [WHIRHeaderRoots.packetHeader,← split] using extended

theorem ancestor_header_packet (registry : Public) (Q : Nat)
    (packet ancestor : RawWHIRKeys.Packet (context registry) Q)
    (member : ancestor ∈ RawWHIRKeys.ancestors (context registry) Q packet) :
    WHIRHeaderRoots.packetHeader registry Q ancestor = WHIRHeaderRoots.packetHeader registry Q packet := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
  rfl

/-- A header frozen by any dependency allocation is an input root of its initiating
packet, including caller-output and ancestor allocations. -/
theorem completion_header_member (registry : Public) (Q : Nat)
    (packet : RawWHIRKeys.Packet (context registry) Q)
    (key : RawOracleCoupling.Concrete.AllocationKey (context registry) Q)
    (member : key.1 ∈ WHIRPublicBackfill.completionKeys (context registry) Q packet)
    (root : Digest32) (captured : root ∈ WHIRHeaderRoots.allocationRoots registry Q key) :
    root ∈ packetRoots registry Q packet := by
  rcases key with ⟨group,history⟩
  cases group with
  | inl allocated =>
    have packets : allocated ∈ RawWHIRKeys.ancestors (context registry) Q packet ∨ allocated = packet := by
      let callers : List (RawOracleCoupling.Concrete.partition (context registry) Q).Garbage :=
        RawWHIRKeys.callerGroups (context registry) Q packet
      change Sum.inl allocated ∈
        (callers.map Sum.inr ++
          (RawWHIRKeys.ancestors (context registry) Q packet).map Sum.inl) ++ [Sum.inl packet] at member
      rcases List.mem_append.mp member with deps | self
      · rcases List.mem_append.mp deps with caller | ancestor
        · obtain ⟨raw,_,equal⟩ := List.mem_map.mp caller
          cases equal
        · obtain ⟨a,ha,equal⟩ := List.mem_map.mp ancestor
          cases Sum.inl.inj equal
          exact Or.inl ha
      · exact Or.inr (Sum.inl.inj (List.mem_singleton.mp self))
    have same : WHIRHeaderRoots.packetHeader registry Q allocated =
        WHIRHeaderRoots.packetHeader registry Q packet := by
      rcases packets with ancestor | rfl
      · exact ancestor_header_packet registry Q packet allocated ancestor
      · rfl
    apply List.mem_append_left
    simpa only [WHIRHeaderRoots.allocationRoots,WHIRHeaderRoots.allocationRoot,
      WHIRHeaderRoots.allocationHeader,same,Option.toList_map] using captured
  | inr raw =>
    have caller : raw ∈ RawWHIRKeys.callerGroups (context registry) Q packet := by
      let callers : List (RawOracleCoupling.Concrete.partition (context registry) Q).Garbage :=
        RawWHIRKeys.callerGroups (context registry) Q packet
      have hm : (Sum.inr raw : RawOracleCoupling.Concrete.GroupKey (context registry) Q) ∈
          callers.map Sum.inr := by
        simpa [WHIRPublicBackfill.completionKeys,RawOracleCoupling.Concrete.dependencyKeys,
          RawOracleCoupling.Partition.dependencies,RawOracleCoupling.Concrete.schedule,
          RawOracleCoupling.Concrete.callerPlan,callers,RawWHIRKeys.Garbage] using member
      obtain ⟨other,member,equal⟩ := List.mem_map.mp hm
      cases Sum.inr.inj equal
      exact member
    have parsed : ∃ header, WHIRHeaderRoots.rawHeader registry raw.val = some header ∧ header.root = root := by
      simpa [WHIRHeaderRoots.allocationRoots,WHIRHeaderRoots.allocationRoot,
        WHIRHeaderRoots.allocationHeader,Option.mem_toList,Option.map_eq_some_iff] using captured
    obtain ⟨header,parsed,rfl⟩ := parsed
    exact packet_header_member registry Q packet header
      (caller_header_packet registry Q packet raw caller header parsed)

/-- A recognized raw packet already contains its caller header before the raw
compression answer; completed dependencies never introduce a reply-derived root. -/
theorem recognized_header_member (registry : Public) (Q : Nat)
    (raw : RawKey Q) (pos : RawWHIRKeys.Position (context registry) Q)
    (recognized : RawWHIRKeys.recognize (context registry) Q raw = some pos)
    (header : WHIRHeaderRoots.Header)
    (parsed : WHIRHeaderRoots.packetHeader registry Q pos.1 = some header) :
    header.root ∈ rawRoots registry Q raw := by
  apply raw_header_member
  rw [← RawWHIRKeys.encode_recognize (context registry) Q raw pos recognized]
  have extended := header_append registry (RawWHIRKeys.entry (context registry) pos.1.val)
    header parsed (WHIRHistoryKey.canonicalFrames (RawWHIRKeys.width (context registry).mode pos.1.val.profile)
      pos.1.val.messages)
  have whole : WHIRHeaderRoots.fromHistory registry
      (RawWHIRKeys.coordinate (context registry) pos.1.val pos.2.val).history = some header := extended
  change Option.map WHIRHeaderRoots.Header.root
    (WHIRHeaderRoots.rawHeader registry
      (constructionKey Q registry.iv (RawWHIRKeys.coordinate (context registry) pos.1.val pos.2.val) _)) =
        some header.root
  rw [WHIRHeaderRoots.rawHeader_construction registry
    (RawWHIRKeys.coordinate (context registry) pos.1.val pos.2.val)
    (RawWHIRKeys.coordinate_admissible (context registry) Q pos) _ header whole]
  rfl

theorem observations_append (a b : List (Event cap)) :
    observations (a ++ b) = observations a ++ observations b := by
  induction a with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> simp only [List.cons_append,observations,ih,List.cons_append]

/-- Source commitments are captured at their own event position, not at the
end of the repeated observer replay that happens to discover them. -/
theorem commit_event_capture (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R)
    (past future : List (Event cap)) (root : Digest32)
    (split : (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.events =
      past ++ .commit root :: future) (visible : PublicLog) :
    root ∈ capture registry Q select (recover source (observations past)) visible := by
  induction source generalizing past visible with
  | done value =>
    have empty : ([] : List (Event cap)) = past ++ .commit root :: future := split
    have := congrArg List.length empty
    simp only [List.length_nil,List.length_append,List.length_cons] at this
    omega
  | commit announced next ih =>
    simp only [WHIRSourceChronology.compile,map_real,mapExecution,WHIRSourceChronology.prepend] at split
    cases past with
    | nil =>
      have head : (Event.commit announced : Event cap) = Event.commit root := by
        exact (List.cons.inj split).1
      cases Event.commit.inj head
      simp [WHIRSourceChronology.recover,prependPrefix,capture,eventRoots]
    | cons event past =>
      have head : Event.commit announced = event := (List.cons.inj split).1
      subst event
      have tail : (runReal C registry.iv (WHIRSourceChronology.compile next)).view.result.events =
          past ++ .commit root :: future := (List.cons.inj split).2
      have member := ih past tail visible
      simpa only [observations,WHIRSourceChronology.recover,prependPrefix,capture,eventRoots,
        visibleAfter,List.cons_append,List.mem_cons] using Or.inr member
  | claims profile entry request next ih =>
    simp only [WHIRSourceChronology.compile,map_real,mapExecution,WHIRSourceChronology.prepend] at split
    cases past with
    | nil => cases (List.cons.inj split).1
    | cons event past =>
      have head : Event.claims profile entry request = event := (List.cons.inj split).1
      subst event
      have tail : (runReal C registry.iv (WHIRSourceChronology.compile next)).view.result.events =
          past ++ .commit root :: future := (List.cons.inj split).2
      simpa only [observations,WHIRSourceChronology.recover,prependPrefix,capture,eventRoots,
        visibleAfter] using ih past tail visible
  | ask q next ih =>
    simp only [WHIRSourceChronology.compile,runReal,map_real,mapExecution,
      WHIRSourceChronology.prepend,DuplexModeGame.prepend] at split
    cases past with
    | nil => cases (List.cons.inj split).1
    | cons event past =>
      have head : Event.answer q (realAnswer C registry.iv q) = event := (List.cons.inj split).1
      subst event
      have tail : (runReal C registry.iv
          (WHIRSourceChronology.compile (next (realAnswer C registry.iv q)))).view.result.events =
          past ++ .commit root :: future := (List.cons.inj split).2
      have member := ih (realAnswer C registry.iv q) past tail
        (advance visible q (realAnswer C registry.iv q))
      simpa only [observations,WHIRSourceChronology.recover,prependPrefix,capture,eventRoots,
        visibleAfter,List.append_assoc,List.mem_append] using Or.inr member

theorem event_observation_prefix (C : PrimitiveOracle) (iv : Digest32)
    (source : Source cap R) (past : List (Event cap))
    (initial : past.IsPrefix (runReal C iv (WHIRSourceChronology.compile source)).view.result.events) :
    (observations past).IsPrefix (runReal C iv (WHIRSourceChronology.compile source)).view.observations := by
  obtain ⟨suffix,eq⟩ := initial
  refine ⟨observations suffix,?_⟩
  rw [← observations_append,eq,real_source_trace]

theorem commit_event_policy (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (past future : List (Event cap)) (root : Digest32)
    (split : (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.events =
      past ++ .commit root :: future) :
    root ∈ policy registry Q select source (expand C registry.iv (observations past)).reverse :=
  source_prefix_captured registry Q select C source counted (observations past)
    (event_observation_prefix C registry.iv source past ⟨.commit root :: future,split.symm⟩)
    root (commit_event_capture registry Q select C source past future root split [])

/-- Advancing the actual observer cursor never removes a pending input root:
it becomes the corresponding answered event's input root. -/
theorem capture_mono (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (source : Source cap R) (before after : List Observation)
    (initial : before.IsPrefix after) (visible : PublicLog) :
    ∀ root ∈ capture registry Q select (recover source before) visible,
      root ∈ capture registry Q select (recover source after) visible := by
  induction source generalizing before after visible with
  | done value => exact fun _ h => h
  | commit root next ih =>
    intro r member
    simp only [WHIRSourceChronology.recover,prependPrefix,capture,eventRoots,visibleAfter,
      List.cons_append,List.mem_cons] at member ⊢
    exact member.elim Or.inl (fun hm => Or.inr (ih before after initial visible r hm))
  | claims p entry request next ih =>
    simpa only [WHIRSourceChronology.recover,prependPrefix,capture,eventRoots,visibleAfter] using
      ih before after initial visible
  | ask q next ih =>
    cases before with
    | nil =>
      intro root member
      have hm : root ∈ queryRoots registry Q visible q := by
        simpa [WHIRSourceChronology.recover,capture,eventRoots,visibleAfter] using member
      cases after with
      | nil => exact member
      | cons o rest =>
        simp only [WHIRSourceChronology.recover,prependPrefix,capture,eventRoots,visibleAfter,
          List.append_assoc]
        exact List.mem_append_left _ hm
    | cons o rest =>
      obtain ⟨suffix,eq⟩ := initial
      subst after
      intro root member
      simp only [List.cons_append,WHIRSourceChronology.recover,prependPrefix,capture,eventRoots,
        visibleAfter,List.append_assoc,List.mem_append] at member ⊢
      have recur := ih o.answer rest (rest ++ suffix) ⟨suffix,rfl⟩ (advance visible q o.answer) root
      simp only [capture,List.mem_append] at recur
      exact member.elim Or.inl (fun hm => Or.inr (recur hm))

/-- All roots registered by preparation of a warmed ancestor are already in
the initiating packet's encoded history footprint. -/
theorem ancestor_footprint_member (registry : Public) (Q : Nat)
    (packet ancestor : RawWHIRKeys.Packet (context registry) Q)
    (ancestry : ancestor ∈ RawWHIRKeys.ancestors (context registry) Q packet)
    (ref : WHIRSnapshotReplay.RootRef)
    (member : ref ∈ WHIRSnapshotReplay.historyFootprint ancestor.val.profile
      ancestor.val.statement ancestor.val.messages) :
    ref ∈ WHIRSnapshotReplay.historyFootprint packet.val.profile packet.val.statement packet.val.messages := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ancestry
  exact WHIRSnapshotReplay.historyFootprint_drop _ _ _ _ ref member

/-- The historical prefix fields required by `FrozenOpeningBad`. This is an
internal induction invariant; concrete execution theorems construct it from empty. -/
def Frozen (roots : PublicMerkleProbability.RootPolicy) (trace : PublicLog)
    (state : CausalBindingState.State cap) : Prop :=
  ∀ root snap, MerkleTransport.Commitments.lookup root state.registry = some snap →
    ∃ oldLog before after,
      state.frozenLog root = some oldLog ∧ trace = before ++ after ∧
      (∀ e ∈ oldLog, e ∈ before) ∧
      (∀ n d, (n,d) ∈ before → tag n = 0 → (n,d) ∈ oldLog) ∧
      root ∈ roots before.reverse

def PublicAt (state : CausalBindingState.State cap) (events : List (Event cap)) : Prop :=
  ∀ n d, (n,d) ∈ state.publicLog ↔
    ∃ purpose, Event.answer (.primitive purpose n) d ∈ events

def Committed (state : CausalBindingState.State cap) (events : List (Event cap)) : Prop :=
  ∀ root, Event.commit root ∈ events →
    ∃ snap, MerkleTransport.Commitments.lookup root state.registry = some snap

theorem frozen_empty (roots : PublicMerkleProbability.RootPolicy) (trace : PublicLog) :
    Frozen roots trace (CausalBindingState.empty cap) := by
  intro root snap found
  simp [CausalBindingState.empty,MerkleTransport.Commitments.lookup] at found

theorem frozen_fields (roots : PublicMerkleProbability.RootPolicy) (trace : PublicLog)
    (state next : CausalBindingState.State cap) (old : Frozen roots trace state)
    (registry : next.registry = state.registry) (logs : next.frozenLog = state.frozenLog) :
    Frozen roots trace next := by
  intro root snap known
  obtain ⟨log,before,after,hlog,eq,sub,saturated,captured⟩ := old root snap (registry ▸ known)
  exact ⟨log,before,after,logs.symm ▸ hlog,eq,sub,saturated,captured⟩

theorem registerRoot_frozen (roots : PublicMerkleProbability.RootPolicy) (trace : PublicLog)
    (state : CausalBindingState.State cap) (old : Frozen roots trace state)
    (root : Digest32) (before after : PublicLog) (split : trace = before ++ after)
    (sub : ∀ e ∈ state.publicLog, e ∈ before)
    (saturated : ∀ n d, (n,d) ∈ before → tag n = 0 → (n,d) ∈ state.publicLog)
    (captured : root ∈ roots before.reverse) :
    Frozen roots trace (CausalBindingState.registerRoot state root) := by
  unfold CausalBindingState.registerRoot
  cases found : MerkleTransport.Commitments.lookup root state.registry with
  | some snap => exact old
  | none =>
    intro r snap known
    by_cases same : r = root
    · subst r
      exact ⟨state.publicLog,before,after,by simp,split,sub,saturated,captured⟩
    · have prior : MerkleTransport.Commitments.lookup r state.registry = some snap := by
        simpa [MerkleTransport.Commitments.register,found,MerkleTransport.Commitments.lookup,same] using known
      obtain ⟨log,earlier,later,hl,eq,hs,ht,hr⟩ := old r snap prior
      exact ⟨log,earlier,later,by simpa [Function.update_of_ne same] using hl,eq,hs,ht,hr⟩

theorem observation_mem_events (events : List (Event cap)) (q : Query) (d : Digest32) :
    (⟨q,d⟩ : Observation) ∈ observations events ↔ Event.answer q d ∈ events := by
  induction events with
  | nil => simp [observations]
  | cons event rest ih =>
    cases event <;> simp [observations,ih,Observation.mk.injEq]

theorem publicAt_fullC (C : PrimitiveOracle) (iv : Digest32)
    (state : CausalBindingState.State cap) (events : List (Event cap))
    (current : PublicAt state events) (real : ∀ e ∈ events, WHIRPhysicalSnapshots.RealEvent C iv e) :
    (∀ e ∈ state.publicLog, e ∈ expand C iv (observations events)) ∧
    (∀ n d, (n,d) ∈ expand C iv (observations events) → tag n = 0 → (n,d) ∈ state.publicLog) := by
  have answers : ∀ o ∈ observations events, o.answer = realAnswer C iv o.query := by
    intro o ho
    exact real (.answer o.query o.answer) ((observation_mem_events events o.query o.answer).mp ho)
  constructor
  · intro ⟨n,d⟩ member
    obtain ⟨purpose,he⟩ := (current n d).mp member
    exact primitive_expand C iv _ answers purpose n d
      ((observation_mem_events events _ _).mpr he)
  · intro n d member ordinary
    obtain ⟨purpose,ho⟩ := ordinary_expand C iv _ answers n d member ordinary
    exact (current n d).mpr ⟨purpose,(observation_mem_events events _ _).mp ho⟩

structure Cursor (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state : CausalBindingState.State cap) (past : List (Event cap)) : Prop where
  initial : past.IsPrefix (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.events
  physical : WHIRPhysicalSnapshots.Invariant C state
  publicAt : PublicAt state past
  committed : Committed state past
  frozen : Frozen (policy registry Q select source)
    (primitiveLog C registry.iv (WHIRSourceChronology.compile source) Q ((compile_counted source Q).mpr counted)) state

theorem cursor_empty (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source) :
    Cursor registry Q select C source counted (CausalBindingState.empty cap) [] := by
  refine ⟨⟨_,rfl⟩,WHIRPhysicalSnapshots.empty_invariant C cap,?_,?_,frozen_empty _ _⟩
  · intro n d; simp [CausalBindingState.empty]
  · intro root member; cases member

theorem cursor_registerRoot (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state : CausalBindingState.State cap) (past : List (Event cap))
    (old : Cursor registry Q select C source counted state past) (root : Digest32)
    (captured : root ∈ policy registry Q select source (expand C registry.iv (observations past)).reverse) :
    Cursor registry Q select C source counted (CausalBindingState.registerRoot state root) past := by
  have real : ∀ e ∈ past, WHIRPhysicalSnapshots.RealEvent C registry.iv e :=
    fun e he => WHIRPhysicalSnapshots.real_source_events C registry.iv source e
      (WHIRPhysicalSnapshots.prefix_mem old.initial he)
  have hp := observation_prefix C registry.iv (WHIRSourceChronology.compile source) Q
    ((compile_counted source Q).mpr counted) _ (event_observation_prefix C registry.iv source past old.initial)
  obtain ⟨after,eq⟩ := hp
  obtain ⟨sub,saturated⟩ := publicAt_fullC C registry.iv state past old.publicAt real
  refine ⟨old.initial,WHIRPhysicalSnapshots.registerRoot_invariant C state root old.physical,
    ?_,?_,registerRoot_frozen _ _ state old.frozen root _ after eq.symm sub saturated captured⟩
  · intro n d
    rw [WHIRPhysicalSnapshots.registerRoot_publicLog]
    exact old.publicAt n d
  · intro r member
    obtain ⟨snap,known⟩ := old.committed r member
    exact ⟨snap,(CausalBindingState.registerRoot_extends state root).registry r snap known⟩

theorem cursor_step (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state : CausalBindingState.State cap) (past : List (Event cap))
    (old : Cursor registry Q select C source counted state past) (event : Event cap)
    (initial : (past ++ [event]).IsPrefix
      (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.events) :
    Cursor registry Q select C source counted (WHIRSourceObserver.replayTracked state [event]) (past ++ [event]) := by
  have real : ∀ e ∈ [event], WHIRPhysicalSnapshots.RealEvent C registry.iv e :=
    fun e he => WHIRPhysicalSnapshots.real_source_events C registry.iv source e
      (WHIRPhysicalSnapshots.prefix_mem initial (List.mem_append_right _ he))
  have growth := WHIRSourceObserver.replayTracked_extends state [event]
  refine ⟨initial,WHIRPhysicalSnapshots.replayTracked_invariant C registry.iv state [event] old.physical real,
    ?_,?_,?_⟩
  · intro n d
    rw [WHIRPhysicalSnapshots.replayTracked_publicLog_mem_iff C registry.iv state [event]
      old.physical.logAuthentic real n d,old.publicAt]
    simp only [List.mem_append,exists_or]
  · intro root member
    rcases List.mem_append.mp member with prior | fresh
    · obtain ⟨snap,known⟩ := old.committed root prior
      exact ⟨snap,growth.registry root snap known⟩
    · have same : Event.commit root = event := List.mem_singleton.mp fresh
      subst event
      change ∃ snap, MerkleTransport.Commitments.lookup root
        (CausalBindingState.registerRoot state root).registry = some snap
      cases known : MerkleTransport.Commitments.lookup root state.registry with
      | some snap => exact ⟨snap,by simp only [CausalBindingState.registerRoot,known]⟩
      | none => exact ⟨CausalBindingState.snapshot state.records,
          (WHIRPhysicalSnapshots.first_capture state root known).1⟩
  · cases event with
    | answer q d =>
      cases q with
      | primitive purpose n =>
        apply frozen_fields _ _ state _ old.frozen
        · simp only [WHIRSourceObserver.replayTracked,step,observePublic,PublicMerkleLog.observe,
            WHIRPhysicalSnapshots.observeRecords_registry]
        · simp only [WHIRSourceObserver.replayTracked,step,observePublic,PublicMerkleLog.observe,
            WHIRPhysicalSnapshots.observeRecords_frozenLog]
      | construction coordinate valid => exact old.frozen
    | commit root =>
      obtain ⟨future,eq⟩ := initial
      have split : (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.events =
          past ++ .commit root :: future := by simpa only [List.append_assoc,List.singleton_append] using eq.symm
      exact (cursor_registerRoot registry Q select C source counted state past old root
        (commit_event_policy registry Q select C source counted past future root split)).frozen
    | claims profile entry request =>
      unfold WHIRSourceObserver.replayTracked step
      cases known : MerkleTransport.Commitments.lookup request.root state.registry <;>
        simp only [known,WHIRSourceObserver.replayTracked]
      · exact frozen_fields _ _ state _ old.frozen rfl rfl
      · exact old.frozen

theorem replayTracked_append (state : CausalBindingState.State cap) (a b : List (Event cap)) :
    WHIRSourceObserver.replayTracked state (a ++ b) =
      WHIRSourceObserver.replayTracked (WHIRSourceObserver.replayTracked state a) b := by
  induction a generalizing state with
  | nil => rfl
  | cons event rest ih =>
    simp only [List.cons_append,WHIRSourceObserver.replayTracked]
    cases step state event <;> exact ih _

/-- Fresh source events extend the chronological C cursor one event at a time;
an error annotation never suppresses the subsequent public observations. -/
theorem cursor_replay_suffix (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state : CausalBindingState.State cap) (past extra : List (Event cap))
    (old : Cursor registry Q select C source counted state past)
    (initial : (past ++ extra).IsPrefix
      (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.events) :
    Cursor registry Q select C source counted (WHIRSourceObserver.replayTracked state extra) (past ++ extra) := by
  induction extra generalizing state past with
  | nil => simpa only [WHIRSourceObserver.replayTracked,List.append_nil] using old
  | cons event rest ih =>
    have stepInitial : (past ++ [event]).IsPrefix
        (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.events :=
      (show (past ++ [event]).IsPrefix (past ++ event :: rest) from
        ⟨rest,by simp only [List.append_assoc,List.singleton_append]⟩).trans initial
    have next := cursor_step registry Q select C source counted state past old event stepInitial
    have more : ((past ++ [event]) ++ rest).IsPrefix
        (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.events := by
      simpa only [List.append_assoc,List.singleton_append] using initial
    have result := ih (WHIRSourceObserver.replayTracked state [event]) (past ++ [event]) next more
    rw [← replayTracked_append] at result
    simpa only [List.append_assoc,List.singleton_append] using result

/-- Replaying an already-observed source prefix cannot recapture a root. New
source events are therefore appended after the old cursor, not before it. -/
theorem cursor_replay (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state : CausalBindingState.State cap) (past events : List (Event cap))
    (old : Cursor registry Q select C source counted state past)
    (grows : past.IsPrefix events)
    (initial : events.IsPrefix
      (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.events) :
    Cursor registry Q select C source counted (WHIRSourceObserver.replayTracked state events) events := by
  have real : ∀ e ∈ past, WHIRPhysicalSnapshots.RealEvent C registry.iv e :=
    fun e he => WHIRPhysicalSnapshots.real_source_events C registry.iv source e
      (WHIRPhysicalSnapshots.prefix_mem old.initial he)
  have fields := WHIRPhysicalSnapshots.replayTracked_settled_fields state past
    (fun purpose n d he => (old.publicAt n d).mpr ⟨purpose,he⟩) old.committed
  have unchanged : Cursor registry Q select C source counted
      (WHIRSourceObserver.replayTracked state past) past := by
    refine ⟨old.initial,WHIRPhysicalSnapshots.replayTracked_invariant C registry.iv state past old.physical real,
      ?_,?_,frozen_fields _ _ state _ old.frozen fields.1 fields.2.2.1⟩
    · intro n d
      rw [fields.2.2.2]
      exact old.publicAt n d
    · intro root member
      rw [fields.1]
      exact old.committed root member
  obtain ⟨extra,rfl⟩ := grows
  rw [replayTracked_append]
  exact cursor_replay_suffix registry Q select C source counted _ past extra unchanged initial

theorem cursor_registerRoots (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state : CausalBindingState.State cap) (past : List (Event cap))
    (old : Cursor registry Q select C source counted state past) (roots : List Digest32)
    (captured : ∀ root ∈ roots,
      root ∈ policy registry Q select source (expand C registry.iv (observations past)).reverse) :
    Cursor registry Q select C source counted (CausalBindingState.registerRoots state roots) past := by
  induction roots generalizing state with
  | nil => exact old
  | cons root rest ih =>
    exact ih (CausalBindingState.registerRoot state root)
      (cursor_registerRoot registry Q select C source counted state past old root (captured root (by simp)))
      (fun r hr => captured r (List.mem_cons_of_mem _ hr))

/-- The consumer receives the exact retained records and frozen log from the
actual state, alongside a chronological full-C freeze witness. -/
theorem Cursor.retained (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state : CausalBindingState.State cap) (past : List (Event cap))
    (current : Cursor registry Q select C source counted state past)
    (root : Digest32) (snap : MerkleTransport.Commitments.Snapshot)
    (known : MerkleTransport.Commitments.lookup root state.registry = some snap) :
    ∃ retained oldLog before after,
      state.frozen root = some retained ∧ state.frozenLog root = some oldLog ∧
      primitiveLog C registry.iv (WHIRSourceChronology.compile source) Q
        ((compile_counted source Q).mpr counted) = before ++ after ∧
      (∀ e ∈ oldLog, e ∈ before) ∧
      (∀ n d, (n,d) ∈ before → tag n = 0 → (n,d) ∈ oldLog) ∧
      root ∈ policy registry Q select source before.reverse ∧
      AuthenticLog C oldLog ∧ WHIRPhysicalSnapshots.Historical oldLog retained ∧
      WHIRPhysicalSnapshots.Saturated oldLog retained ∧ snap.table = MerkleTransport.Commitments.recordDomain retained := by
  obtain ⟨oldLog,before,after,hl,eq,sub,saturated,captured⟩ := current.frozen root snap known
  obtain ⟨retained,log,hf,hl',auth,historical,complete,table,_⟩ := current.physical.snapshots root snap known
  have same : log = oldLog := Option.some.inj (hl'.symm.trans hl)
  subst log
  exact ⟨retained,oldLog,before,after,hf,hl,eq,sub,saturated,captured,auth,historical,complete,table⟩

theorem visible_observations (events : List (Event cap)) (visible : PublicLog) :
    visibleAfter events visible = DuplexPublicSimulator.finalLog visible (observations events) := by
  induction events generalizing visible with
  | nil => rfl
  | cons event rest ih =>
    cases event with
    | answer q d =>
      cases q <;> simpa only [visibleAfter,advance,observations,DuplexPublicSimulator.finalLog,
        DuplexPublicSimulator.observe] using ih _
    | commit => exact ih visible
    | claims => exact ih visible

theorem recover_observation_prefix (C : PrimitiveOracle) (iv : Digest32)
    (source : Source cap R) (seen : List Observation)
    (initial : seen.IsPrefix (runReal C iv (WHIRSourceChronology.compile source)).view.observations) :
    observations (recover source seen).events = seen := by
  induction source generalizing seen with
  | done value =>
    have empty : seen = [] := List.prefix_nil.mp initial
    subst seen
    rfl
  | commit root next ih =>
    apply ih
    simpa only [WHIRSourceChronology.compile,map_real,mapExecution] using initial
  | claims profile entry request next ih =>
    apply ih
    simpa only [WHIRSourceChronology.compile,map_real,mapExecution] using initial
  | ask q next ih =>
    cases seen with
    | nil => rfl
    | cons o rest =>
      have split : o = ⟨q,realAnswer C iv q⟩ ∧
          rest.IsPrefix (runReal C iv (WHIRSourceChronology.compile (next (realAnswer C iv q)))).view.observations := by
        simpa only [WHIRSourceChronology.compile,runReal,map_real,mapExecution,
          DuplexModeGame.prepend,List.cons_prefix_cons] using initial
      rcases split with ⟨rfl,tail⟩
      exact congrArg (List.cons _) (ih (realAnswer C iv q) rest tail)

theorem recover_pending (C : PrimitiveOracle) (iv : Digest32)
    (source : Source cap R) (before after : List Observation) (q : Query) (d : Digest32)
    (split : (runReal C iv (WHIRSourceChronology.compile source)).view.observations =
      before ++ ⟨q,d⟩ :: after) :
    (recover source before).pending = some q := by
  induction source generalizing before with
  | done value =>
    have empty : ([] : List Observation) = before ++ ⟨q,d⟩ :: after := split
    have := congrArg List.length empty
    simp only [List.length_nil,List.length_append,List.length_cons] at this
    omega
  | commit root next ih =>
    exact ih before (by simpa only [WHIRSourceChronology.compile,map_real,mapExecution] using split)
  | claims profile entry request next ih =>
    exact ih before (by simpa only [WHIRSourceChronology.compile,map_real,mapExecution] using split)
  | ask current next ih =>
    simp only [WHIRSourceChronology.compile,runReal,map_real,mapExecution,DuplexModeGame.prepend] at split
    cases before with
    | nil =>
      have same : current = q := congrArg Observation.query (List.cons.inj split).1
      subst q
      rfl
    | cons o rest =>
      have same := (List.cons.inj split).1
      subst o
      exact ih (realAnswer C iv current) rest (List.cons.inj split).2

theorem queryKey_roots (registry : Public) (Q : Nat) (visible : PublicLog)
    (q : Query) (raw : RawKey Q)
    (key : WHIRSourcePartialMonotone.queryKey Q registry.iv visible q = some raw) :
    queryRoots registry Q visible q = rawRoots registry Q raw := by
  cases q with
  | primitive purpose n => exact primitive_roots registry Q visible purpose n raw key
  | construction coordinate valid =>
    by_cases bounded : pathCost coordinate ≤ Q
    · have same : constructionKey Q registry.iv coordinate bounded = raw := by
        simpa only [WHIRSourcePartialMonotone.queryKey,bounded,↓reduceDIte,Option.some.injEq] using key
      subst raw
      exact construction_roots registry Q visible coordinate valid bounded
    · simp only [WHIRSourcePartialMonotone.queryKey,bounded,↓reduceDIte] at key
      cases key

/-- All earlier raw requests have already been allocated. The pending request's
input roots are therefore captured by the current replay, even if warming has
also made later source queries available. -/
theorem raw_request_captured (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (cache : RawKey Q → Option Digest32)
    (prior later : List (RawKey Q)) (raw : RawKey Q)
    (split : DuplexPublicSimulator.replay Q registry.iv []
      (runReal C registry.iv (WHIRSourceChronology.compile source)).view.observations = prior ++ raw :: later)
    (covered : ∀ key ∈ prior, cache key = some (WHIRRealSimulator.rawTable Q C key))
    (root : Digest32) (member : root ∈ rawRoots registry Q raw) :
    root ∈ capture registry Q select
      (recover source (DuplexPublicSimulator.runPartial cache registry.iv
        ((DuplexPublicSimulator.simulator Q).initial C) (WHIRSourceChronology.compile source)
        Q (by omega) ((compile_counted source Q).mpr counted)).observations) [] := by
  obtain ⟨before,observation,after,events,requests,key⟩ :=
    WHIRSourcePartialMonotone.replay_factor registry.iv []
      (runReal C registry.iv (WHIRSourceChronology.compile source)).view.observations prior raw later split
  have initial : before.IsPrefix
      (runReal C registry.iv (WHIRSourceChronology.compile source)).view.observations :=
    ⟨observation :: after,events.symm⟩
  have past : before.IsPrefix (DuplexPublicSimulator.runPartial cache registry.iv
      ((DuplexPublicSimulator.simulator Q).initial C) (WHIRSourceChronology.compile source)
      Q (by omega) ((compile_counted source Q).mpr counted)).observations := by
    apply WHIRSourcePartialMonotone.runPartial_covers_prefix cache (WHIRRealSimulator.rawTable Q C)
      registry.iv _ _ _ _ _ before
    · rw [← WHIRRealSimulator.real_ideal_view C registry.iv _ ((compile_counted source Q).mpr counted)]
      exact initial
    · change ∀ key ∈ DuplexPublicSimulator.replay Q registry.iv [] before, _
      rw [requests]
      exact covered
  apply capture_mono registry Q select source _ _ past [] root
  have pending := recover_pending C registry.iv source before after observation.query observation.answer events
  have visible : visibleAfter (recover source before).events [] = DuplexPublicSimulator.finalLog [] before := by
    rw [visible_observations,recover_observation_prefix C registry.iv source before initial]
  unfold capture
  apply List.mem_append_right
  apply List.mem_append_left
  simpa only [pending,Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    visible,queryKey_roots registry Q _ _ raw key] using member

/-- Exactly the roots which concrete header and packet-footprint preparation
may register; answers and ancestor answer annotations are not inspected. -/
def allocationRoots (registry : Public) (Q : Nat)
    (key : RawOracleCoupling.Concrete.AllocationKey (context registry) Q) : List Digest32 :=
  WHIRHeaderRoots.allocationRoots registry Q key ++
    match key.1 with
    | .inl packet => (WHIRSnapshotReplay.historyFootprint packet.val.profile
        packet.val.statement packet.val.messages).map Prod.fst
    | .inr _ => []

theorem completion_packet_member (registry : Public) (Q : Nat)
    (packet allocated : RawWHIRKeys.Packet (context registry) Q)
    (member : Sum.inl allocated ∈ WHIRPublicBackfill.completionKeys (context registry) Q packet) :
    allocated ∈ RawWHIRKeys.ancestors (context registry) Q packet ∨ allocated = packet := by
  let callers : List (RawOracleCoupling.Concrete.partition (context registry) Q).Garbage :=
    RawWHIRKeys.callerGroups (context registry) Q packet
  change Sum.inl allocated ∈ (callers.map Sum.inr ++
    (RawWHIRKeys.ancestors (context registry) Q packet).map Sum.inl) ++ [Sum.inl packet] at member
  rcases List.mem_append.mp member with deps | self
  · rcases List.mem_append.mp deps with caller | ancestor
    · obtain ⟨raw,_,equal⟩ := List.mem_map.mp caller
      cases equal
    · obtain ⟨a,ha,equal⟩ := List.mem_map.mp ancestor
      cases Sum.inl.inj equal
      exact Or.inl ha
  · exact Or.inr (Sum.inl.inj (List.mem_singleton.mp self))

theorem completion_roots (registry : Public) (Q : Nat)
    (packet : RawWHIRKeys.Packet (context registry) Q)
    (key : RawOracleCoupling.Concrete.AllocationKey (context registry) Q)
    (member : key.1 ∈ WHIRPublicBackfill.completionKeys (context registry) Q packet) :
    ∀ root ∈ allocationRoots registry Q key, root ∈ packetRoots registry Q packet := by
  intro root captured
  rcases List.mem_append.mp captured with header | footprint
  · exact completion_header_member registry Q packet key member root header
  · rcases key with ⟨group,history⟩
    cases group with
    | inr raw => cases footprint
    | inl allocated =>
      obtain ⟨ref,hm,rfl⟩ := List.mem_map.mp footprint
      apply packet_footprint_member
      rcases completion_packet_member registry Q packet allocated member with ancestor | rfl
      · exact ancestor_footprint_member registry Q packet allocated ancestor ref hm
      · exact hm

theorem packetRoots_raw (registry : Public) (Q : Nat)
    (raw : RawKey Q) (pos : RawWHIRKeys.Position (context registry) Q)
    (recognized : RawWHIRKeys.recognize (context registry) Q raw = some pos) :
    ∀ root ∈ packetRoots registry Q pos.1, root ∈ rawRoots registry Q raw := by
  intro root member
  rcases List.mem_append.mp member with headerMem | footprint
  · obtain ⟨header,hm,rfl⟩ := List.mem_map.mp headerMem
    exact recognized_header_member registry Q raw pos recognized header (Option.mem_toList.mp hm)
  · obtain ⟨ref,hm,rfl⟩ := List.mem_map.mp footprint
    exact raw_footprint_member registry Q raw pos recognized ref hm

theorem request_roots (registry : Public) (Q : Nat) (raw : RawKey Q)
    (key : RawOracleCoupling.Concrete.AllocationKey (context registry) Q)
    (member : key.1 ∈ WHIRObservableAllocations.requestKeys (context registry) Q raw) :
    ∀ root ∈ allocationRoots registry Q key, root ∈ rawRoots registry Q raw := by
  cases recognized : RawWHIRKeys.recognize (context registry) Q raw with
  | some pos =>
    rw [WHIRObservableAllocations.requestKeys_some (context registry) Q raw pos recognized] at member
    exact fun root hr => packetRoots_raw registry Q raw pos recognized root
      (completion_roots registry Q pos.1 key member root hr)
  | none =>
    rw [WHIRObservableAllocations.requestKeys_none (context registry) Q raw recognized] at member
    rcases key with ⟨group,history⟩
    have same : group = .inr ⟨raw,recognized⟩ := List.mem_singleton.mp member
    subst group
    intro root captured
    have header : WHIRHeaderRoots.rawRoot registry raw = some root := by
      simpa [allocationRoots,WHIRHeaderRoots.allocationRoots,WHIRHeaderRoots.allocationRoot,
        WHIRHeaderRoots.allocationHeader,WHIRHeaderRoots.rawRoot] using captured
    exact raw_header_member registry Q raw root header

theorem cursor_fields (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state next : CausalBindingState.State cap) (past : List (Event cap))
    (old : Cursor registry Q select C source counted state past)
    (records : next.records = state.records) (roots : next.registry = state.registry)
    (frozen : next.frozen = state.frozen) (logs : next.frozenLog = state.frozenLog)
    (publicLog : next.publicLog = state.publicLog) :
    Cursor registry Q select C source counted next past := by
  have physical : WHIRPhysicalSnapshots.Invariant C next := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa only [publicLog] using old.physical.logAuthentic
    · simpa only [publicLog,records] using old.physical.historical
    · simpa only [publicLog,records] using old.physical.saturated
    · simpa only [CausalBindingState.AuthenticState,records,frozen] using old.physical.authentic
    · intro root snap known
      simpa only [frozen,logs,publicLog] using old.physical.snapshots root snap (roots ▸ known)
  refine ⟨old.initial,physical,?_,?_,frozen_fields _ _ state next old.frozen roots logs⟩
  · intro n d; rw [publicLog]; exact old.publicAt n d
  · intro root member; rw [roots]; exact old.committed root member

theorem cursor_registerStatement (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state : CausalBindingState.State cap) (past : List (Event cap))
    (old : Cursor registry Q select C source counted state past)
    (profile : ParameterBounds.Profile) (entry : FramedHistory)
    (data : Option (WHIRFiatShamir.StackInitial profile cap)) :
    Cursor registry Q select C source counted (CausalBindingState.registerStatement state profile entry data) past := by
  unfold CausalBindingState.registerStatement
  split
  · exact old
  · exact cursor_fields registry Q select C source counted state _ past old rfl rfl rfl rfl rfl

theorem cursor_addGroup (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state : CausalBindingState.State cap) (past : List (Event cap))
    (old : Cursor registry Q select C source counted state past)
    (group : RawOracleCoupling.Concrete.GroupKey (context registry) Q)
    (answer : RawOracleCoupling.Concrete.GroupAnswer (context registry) Q group) :
    Cursor registry Q select C source counted (WHIRSourceRawCache.addGroup (context registry) Q state group answer) past :=
  cursor_fields registry Q select C source counted state _ past old rfl rfl rfl rfl rfl

theorem final_request_captured (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (cache : RawKey Q → Option Digest32)
    (covered : ∀ key ∈ DuplexPublicSimulator.replay Q registry.iv []
      (runReal C registry.iv (WHIRSourceChronology.compile source)).view.observations,
      cache key = some (WHIRRealSimulator.rawTable Q C key))
    (root : Digest32)
    (member : root ∈ finalRoots registry Q select
      (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.value) :
    root ∈ capture registry Q select
      (recover source (DuplexPublicSimulator.runPartial cache registry.iv
        ((DuplexPublicSimulator.simulator Q).initial C) (WHIRSourceChronology.compile source)
        Q (by omega) ((compile_counted source Q).mpr counted)).observations) [] := by
  have hits : ∀ key ∈ DuplexPublicSimulator.actualRequests (WHIRRealSimulator.rawTable Q C)
      registry.iv ((DuplexPublicSimulator.simulator Q).initial C) (WHIRSourceChronology.compile source)
      Q (by omega) ((compile_counted source Q).mpr counted),
      cache key = some (WHIRRealSimulator.rawTable Q C key) := by
    rw [← DuplexPublicSimulator.replay_actual]
    rw [← WHIRRealSimulator.real_ideal_view C registry.iv _ ((compile_counted source Q).mpr counted)]
    exact covered
  rw [WHIRSourcePartialMonotone.source_complete cache (WHIRRealSimulator.rawTable Q C) registry.iv C source counted hits]
  rw [← WHIRRealSimulator.real_ideal_view C registry.iv _ ((compile_counted source Q).mpr counted)]
  unfold capture completedPrefix
  apply List.mem_append_right
  simpa only [Option.toList_none,List.flatMap_nil,List.nil_append,Option.toList_some,
    List.flatMap_cons,List.append_nil] using member

theorem cursor_prepareClaims (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state : CausalBindingState.State cap) (past : List (Event cap))
    (old : Cursor registry Q select C source counted state past)
    (profile : ParameterBounds.Profile) (entry : FramedHistory) (key : StackWHIRReplay.Key profile)
    (request : Option (CausalBindingState.ClaimRequest cap profile))
    (footprint : ∀ ref ∈ WHIRSnapshotReplay.historyFootprint profile key.statement key.messages,
      ref.1 ∈ policy registry Q select source (expand C registry.iv (observations past)).reverse)
    (header : ∀ proposed, request = some proposed →
      proposed.root ∈ policy registry Q select source (expand C registry.iv (observations past)).reverse) :
    Cursor registry Q select C source counted (CausalBindingState.prepareClaims state profile entry key request).1 past := by
  have prepare (s : CausalBindingState.State cap)
      (h : Cursor registry Q select C source counted s past)
      (data : Option (WHIRFiatShamir.StackInitial profile cap)) :
      Cursor registry Q select C source counted (CausalBindingState.prepare s profile entry key data).1 past := by
    apply cursor_registerRoots registry Q select C source counted _ past
      (cursor_registerStatement registry Q select C source counted s past h profile entry data)
    intro root member
    obtain ⟨ref,hr,rfl⟩ := List.mem_map.mp member
    exact footprint ref hr
  cases request with
  | none => exact prepare state old none
  | some proposed =>
    exact prepare (CausalBindingState.registerRoot state proposed.root)
      (cursor_registerRoot registry Q select C source counted state past old proposed.root (header proposed rfl)) _

theorem private_events_initial (registry : Public) (Q : Nat) (C : PrimitiveOracle)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (cache : RawKey Q → Option Digest32)
    (agrees : DuplexPublicSimulator.CacheAgrees cache (WHIRRealSimulator.rawTable Q C)) :
    (WHIRSourceObserver.privateEvents Q registry.iv cache C source counted).IsPrefix
      (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.events := by
  have mono := WHIRSourcePartialMonotone.recover_mono source
    (private_observation_prefix C registry.iv source Q counted cache agrees)
  rw [recover_real] at mono
  exact mono

theorem private_prepare_cursor (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (state : CausalBindingState.State cap) (past : List (Event cap))
    (old : Cursor registry Q select C source counted state past)
    (agrees : WHIRSourceRawCache.LogAgrees (WHIRRealSimulator.rawTable Q C) (state.rawAnswers Q))
    (grows : past.IsPrefix (WHIRSourceObserver.privateEvents Q registry.iv (WHIRSourceRawCache.cache Q state)
      C source counted))
    (key : RawOracleCoupling.Concrete.AllocationKey (context registry) Q)
    (captured : ∀ root ∈ allocationRoots registry Q key,
      root ∈ capture registry Q select
        (recover source (DuplexPublicSimulator.runPartial (WHIRSourceRawCache.cache Q state) registry.iv
          ((DuplexPublicSimulator.simulator Q).initial C) (WHIRSourceChronology.compile source)
          Q (by omega) ((compile_counted source Q).mpr counted)).observations) []) :
    Cursor registry Q select C source counted
      (WHIRCausalRawROM.prepare (context registry) rfl Q cap
        (WHIRSourceResolver.privateResolver registry Q C source counted) state key).1
      (WHIRSourceObserver.privateEvents Q registry.iv (WHIRSourceRawCache.cache Q state) C source counted) := by
  let cache := WHIRSourceRawCache.cache Q state
  let seen := (DuplexPublicSimulator.runPartial cache registry.iv
    ((DuplexPublicSimulator.simulator Q).initial C) (WHIRSourceChronology.compile source)
    Q (by omega) ((compile_counted source Q).mpr counted)).observations
  let events := WHIRSourceObserver.privateEvents Q registry.iv cache C source counted
  have cacheAgrees : DuplexPublicSimulator.CacheAgrees cache (WHIRRealSimulator.rawTable Q C) :=
    WHIRSourceRawCache.lookup_agrees Q _ _ agrees
  have initial := private_observation_prefix C registry.iv source Q counted cache cacheAgrees
  have obs : observations events = seen := recover_observation_prefix C registry.iv source seen initial
  have roots : ∀ root ∈ allocationRoots registry Q key,
      root ∈ policy registry Q select source (expand C registry.iv (observations events)).reverse := by
    intro root member
    rw [obs]
    exact source_prefix_captured registry Q select C source counted seen initial root (captured root member)
  have replayed := cursor_replay registry Q select C source counted state past events old grows
    (private_events_initial registry Q C source counted cache cacheAgrees)
  have headed := cursor_registerRoots registry Q select C source counted _ events replayed
    (WHIRHeaderRoots.allocationRoots registry Q key)
    (fun root member => roots root (List.mem_append_left _ member))
  rcases key with ⟨group,history⟩
  cases group with
  | inr raw => exact headed
  | inl packet =>
    apply cursor_prepareClaims registry Q select C source counted _ events headed
    · intro ref member
      exact roots ref.1 (List.mem_append_right _ (List.mem_map.mpr ⟨ref,member,rfl⟩))
    · intro proposed decoded
      have parsed := WHIRHeaderRoots.allocation_packet_root registry Q cap packet history proposed decoded history
      apply roots proposed.root
      apply List.mem_append_left
      rw [parsed]
      exact List.mem_cons_self

/-- The exact allocation path of the actual source and its selected backfill.
`compile_execution` identifies this table replay with the allocation compiler. -/
noncomputable def allocationTrace (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) :
    List (Sigma (RawOracleCoupling.Concrete.AllocationAnswer (context registry) Q)) :=
  (WHIRObservableAllocations.tableReplay (RawOracleCoupling.Concrete.dependencyKeys (context registry) Q)
    ((RawOracleCoupling.Concrete.partition (context registry) Q).split (WHIRRealSimulator.rawTable Q C))
    (WHIRObservableAllocations.allocationRequests (context registry) Q
      (DuplexPublicSimulator.replay Q registry.iv []
        (runReal C registry.iv (WHIRSourceChronology.compile source)).view.observations)
      (select (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.value))
    (fun _ => none)).2

noncomputable def replayState (registry : Public) (Q : Nat) (C : PrimitiveOracle)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (trace : List (Sigma (RawOracleCoupling.Concrete.AllocationAnswer (context registry) Q))) :
    CausalBindingState.State cap :=
  ((WHIRCausalRawROM.decorator (context registry) rfl Q cap
    (WHIRSourceResolver.privateResolver registry Q C source counted)).traceRecode
    (CausalBindingState.empty cap) trace).2

theorem recode_final_append (registry : Public) (Q : Nat)
    (resolver : WHIRCausalRawROM.Resolver (context registry) Q cap)
    (state : CausalBindingState.State cap)
    (a b : List (Sigma (RawOracleCoupling.Concrete.AllocationAnswer (context registry) Q))) :
    ((WHIRCausalRawROM.decorator (context registry) rfl Q cap resolver).traceRecode state (a ++ b)).2 =
      ((WHIRCausalRawROM.decorator (context registry) rfl Q cap resolver).traceRecode
        ((WHIRCausalRawROM.decorator (context registry) rfl Q cap resolver).traceRecode state a).2 b).2 := by
  induction a generalizing state with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.cons_append,CausalAllocationLabels.Decorator.traceRecode]
    exact ih _

theorem replayState_snoc (registry : Public) (Q : Nat) (C : PrimitiveOracle)
    (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (trace : List (Sigma (RawOracleCoupling.Concrete.AllocationAnswer (context registry) Q)))
    (entry : Sigma (RawOracleCoupling.Concrete.AllocationAnswer (context registry) Q)) :
    replayState registry Q C source counted (trace ++ [entry]) =
      WHIRSourceRawCache.addGroup (context registry) Q
        (WHIRCausalRawROM.prepare (context registry) rfl Q cap
          (WHIRSourceResolver.privateResolver registry Q C source counted)
          (replayState registry Q C source counted trace) entry.1).1 entry.1.1 entry.2 := by
  unfold replayState
  rw [recode_final_append]
  rcases entry with ⟨⟨group,history⟩,answer⟩
  cases group <;> rfl

theorem allocationTrace_agrees (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) :
    WHIRSourceResolver.TraceAgrees registry Q (WHIRRealSimulator.rawTable Q C)
      (allocationTrace registry Q select C source) :=
  WHIRSourceAllocationCache.replay_agrees registry Q (WHIRRealSimulator.rawTable Q C) _ _

theorem replayState_agrees (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (trace : List (Sigma (RawOracleCoupling.Concrete.AllocationAnswer (context registry) Q)))
    (initial : trace.IsPrefix (allocationTrace registry Q select C source)) :
    WHIRSourceRawCache.LogAgrees (WHIRRealSimulator.rawTable Q C)
      ((replayState registry Q C source counted trace).rawAnswers Q) :=
  WHIRSourceAllocationCache.recode_agrees registry Q (WHIRRealSimulator.rawTable Q C) C source counted
    _ (by intro e h; cases h) trace
    (fun e he => allocationTrace_agrees registry Q select C source e (WHIRPhysicalSnapshots.prefix_mem initial he))

/-- Concrete allocation-stage provenance. No premise says that roots are covered:
the actual emitted key and the acquired earlier raw groups determine the root. -/
theorem allocation_captured (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (before after : List (Sigma (RawOracleCoupling.Concrete.AllocationAnswer (context registry) Q)))
    (entry : Sigma (RawOracleCoupling.Concrete.AllocationAnswer (context registry) Q))
    (split : allocationTrace registry Q select C source = before ++ entry :: after) :
    ∀ root ∈ allocationRoots registry Q entry.1,
      root ∈ capture registry Q select
        (recover source (DuplexPublicSimulator.runPartial
          (WHIRSourceRawCache.cache Q (replayState registry Q C source counted before)) registry.iv
          ((DuplexPublicSimulator.simulator Q).initial C) (WHIRSourceChronology.compile source)
          Q (by omega) ((compile_counted source Q).mpr counted)).observations) [] := by
  obtain ⟨keys,trace,_,_,_,origin⟩ :=
    WHIRSourceAllocationOrigin.allocation_origin (context registry) Q (WHIRRealSimulator.rawTable Q C)
      (DuplexPublicSimulator.replay Q registry.iv []
        (runReal C registry.iv (WHIRSourceChronology.compile source)).view.observations)
      (select (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.value)
      before after entry split
  have acquired (raw : RawKey Q)
      (covered : ∀ key ∈ WHIRObservableAllocations.requestKeys (context registry) Q raw,
        ∃ answer, (WHIRObservableAllocations.tableReplay
          (RawOracleCoupling.Concrete.dependencyKeys (context registry) Q)
          ((RawOracleCoupling.Concrete.partition (context registry) Q).split (WHIRRealSimulator.rawTable Q C))
          keys (fun _ => none)).1 key = some answer) :
      WHIRSourceRawCache.cache Q (replayState registry Q C source counted before) raw =
        some (WHIRRealSimulator.rawTable Q C raw) := by
    have hit := WHIRSourceAllocationCache.covered_raw registry Q (WHIRRealSimulator.rawTable Q C) C source counted
      keys raw (WHIRSourceAllocationOrigin.request_covered (context registry) Q _ raw covered)
    rw [trace] at hit
    exact hit
  intro root member
  rcases origin with sourceStage | finalStage
  · obtain ⟨prior,raw,later,path,key,covered⟩ := sourceStage
    exact raw_request_captured registry Q select C source counted _ prior later raw path
      (fun raw hr => acquired raw (covered raw hr)) root
      (request_roots registry Q raw entry.1 key root member)
  · obtain ⟨key,covered⟩ := finalStage
    apply final_request_captured registry Q select C source counted _
      (fun raw hr => acquired raw (covered raw hr)) root
    cases selected : select (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result.value with
    | none => simp only [selected,WHIRObservableAllocations.finalKeys,List.not_mem_nil] at key
    | some packet =>
      have kp : entry.1.1 ∈ WHIRPublicBackfill.completionKeys (context registry) Q packet := by
        simpa only [selected,WHIRObservableAllocations.finalKeys] using key
      simpa only [finalRoots,selected] using completion_roots registry Q packet entry.1 kp root member

/-- The first-freeze invariant is derived for every actual allocation prefix,
including all warmed dependencies and the selected final completion. -/
theorem allocation_prefix_cursor (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (before after : List (Sigma (RawOracleCoupling.Concrete.AllocationAnswer (context registry) Q)))
    (split : allocationTrace registry Q select C source = before ++ after) :
    ∃ past, Cursor registry Q select C source counted (replayState registry Q C source counted before) past ∧
      past.IsPrefix (WHIRSourceObserver.privateEvents Q registry.iv
        (WHIRSourceRawCache.cache Q (replayState registry Q C source counted before)) C source counted) := by
  induction before using List.reverseRecOn generalizing after with
  | nil =>
    exact ⟨[],cursor_empty registry Q select C source counted,List.nil_prefix⟩
  | append_singleton before entry ih =>
    have priorSplit : allocationTrace registry Q select C source = before ++ entry :: after := by
      simpa only [List.append_assoc,List.singleton_append] using split
    obtain ⟨past,old,grows⟩ := ih (entry :: after) priorSplit
    have agrees := replayState_agrees registry Q select C source counted before ⟨entry :: after,priorSplit.symm⟩
    have prepared := private_prepare_cursor registry Q select C source counted
      (replayState registry Q C source counted before) past old agrees grows entry.1
      (allocation_captured registry Q select C source counted before after entry priorSplit)
    have next := cursor_addGroup registry Q select C source counted _ _ prepared entry.1.1 entry.2
    have value := allocationTrace_agrees registry Q select C source entry
      (priorSplit.symm ▸ List.mem_append_right before (List.mem_cons_self))
    have monotone := WHIRSourcePartialMonotone.allocationEvents_mono registry
      (WHIRRealSimulator.rawTable Q C) C source counted
      (replayState registry Q C source counted before) agrees entry.1
    refine ⟨WHIRSourceObserver.privateEvents Q registry.iv
      (WHIRSourceRawCache.cache Q (replayState registry Q C source counted before)) C source counted,?_,?_⟩
    · rw [replayState_snoc]
      exact next
    · rw [replayState_snoc]
      simpa only [WHIRSourceResolver.after,value] using monotone

/-- Concrete resolver/decorator endpoint. Every retained root has an actual
full-C freeze witness; there is no root-cover or verifier-correctness premise. -/
theorem actual_retained (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (root : Digest32) (snap : MerkleTransport.Commitments.Snapshot)
    (known : MerkleTransport.Commitments.lookup root
      (replayState registry Q C source counted (allocationTrace registry Q select C source)).registry = some snap) :
    let state := replayState registry Q C source counted (allocationTrace registry Q select C source)
    ∃ retained oldLog before after,
      state.frozen root = some retained ∧ state.frozenLog root = some oldLog ∧
      primitiveLog C registry.iv (WHIRSourceChronology.compile source) Q
        ((compile_counted source Q).mpr counted) = before ++ after ∧
      (∀ e ∈ oldLog, e ∈ before) ∧
      (∀ n d, (n,d) ∈ before → tag n = 0 → (n,d) ∈ oldLog) ∧
      root ∈ policy registry Q select source before.reverse ∧
      AuthenticLog C oldLog ∧ WHIRPhysicalSnapshots.Historical oldLog retained ∧
      WHIRPhysicalSnapshots.Saturated oldLog retained ∧ snap.table = MerkleTransport.Commitments.recordDomain retained := by
  obtain ⟨past,current,_⟩ := allocation_prefix_cursor registry Q select C source counted
    (allocationTrace registry Q select C source) [] (List.append_nil _).symm
  exact current.retained registry Q select C source counted _ past root snap known

theorem bind_observation_prefix {S : Type} (C : PrimitiveOracle) (iv : Digest32)
    (program : Program R) (next : R → Program S) :
    (runReal C iv program).view.observations.IsPrefix
      (runReal C iv (WHIRModeFinal.bind program next)).view.observations := by
  induction program with
  | done => exact List.nil_prefix
  | ask q cont ih =>
    obtain ⟨suffix,eq⟩ := ih (realAnswer C iv q)
    refine ⟨suffix,?_⟩
    simpa only [WHIRModeFinal.bind,runReal,DuplexModeGame.prepend,List.cons_append] using
      congrArg (List.cons (⟨q,realAnswer C iv q⟩ : Observation)) eq

/-- The actual source full-C trace is a prefix of the actual physical
source/backfill execution, at any valid total budget. -/
theorem backfill_prefix (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (total : Nat) (whole : DuplexModeGame.Counts total
      (WHIRSourceBackfill.instrument (context registry) Q source select)) :
    (primitiveLog C registry.iv (WHIRSourceChronology.compile source) Q
      ((compile_counted source Q).mpr counted)).IsPrefix
    (primitiveLog C registry.iv (WHIRSourceBackfill.instrument (context registry) Q source select) total whole) := by
  rw [← expand_real C registry.iv (WHIRSourceChronology.compile source) Q
    ((compile_counted source Q).mpr counted)]
  exact observation_prefix C registry.iv _ total whole _
    (bind_observation_prefix C registry.iv (WHIRSourceChronology.compile source) _)

/-- End-to-end frozen provenance in the actual source/backfill all-C trace.
All retained/history/saturation fields are the final concrete resolver state. -/
theorem actual_backfill_retained (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (total : Nat) (whole : DuplexModeGame.Counts total
      (WHIRSourceBackfill.instrument (context registry) Q source select))
    (root : Digest32) (snap : MerkleTransport.Commitments.Snapshot)
    (known : MerkleTransport.Commitments.lookup root
      (replayState registry Q C source counted (allocationTrace registry Q select C source)).registry = some snap) :
    let state := replayState registry Q C source counted (allocationTrace registry Q select C source)
    ∃ retained oldLog before after,
      state.frozen root = some retained ∧ state.frozenLog root = some oldLog ∧
      primitiveLog C registry.iv (WHIRSourceBackfill.instrument (context registry) Q source select)
        total whole = before ++ after ∧
      (∀ e ∈ oldLog, e ∈ before) ∧
      (∀ n d, (n,d) ∈ before → tag n = 0 → (n,d) ∈ oldLog) ∧
      root ∈ policy registry Q select source before.reverse ∧
      AuthenticLog C oldLog ∧ WHIRPhysicalSnapshots.Historical oldLog retained ∧
      WHIRPhysicalSnapshots.Saturated oldLog retained ∧ snap.table = MerkleTransport.Commitments.recordDomain retained := by
  obtain ⟨retained,log,before,after,hf,hl,eq,sub,saturated,captured,auth,historical,complete,table⟩ :=
    actual_retained registry Q select C source counted root snap known
  obtain ⟨completion,physical⟩ := backfill_prefix registry Q select C source counted total whole
  refine ⟨retained,log,before,after ++ completion,hf,hl,?_,sub,saturated,captured,auth,historical,complete,table⟩
  rw [← physical,eq,List.append_assoc]

/-- The independently source-budgeted raw compiler executes exactly the
allocation path used above, including canonical dependency warming/backfill. -/
theorem allocationTrace_compiler (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source)
    (A : Nat) (sourceCounted : WHIRSourceChronology.Counts A source) :
    (TypedOracleCompiler.Sampling.execute
      (WHIRObservableAllocations.allocationOracle (context registry) Q (WHIRRealSimulator.rawTable Q C))
      (RawOracleCoupling.Concrete.compile (context registry) Q
        (fun result : Option (View (Result cap R)) => result.bind (fun view => select view.result.value))
        (WHIRSourceRawProgram.bounded Q registry.iv ((DuplexPublicSimulator.simulator Q).initial C)
          (WHIRSourceChronology.compile source) Q (by omega) ((compile_counted source Q).mpr counted)
          A ((compile_counted source A).mpr sourceCounted)))).2 =
      allocationTrace registry Q select C source := by
  rw [WHIRObservableAllocations.compile_execution,
    WHIRSourceRawProgram.bounded_eval,WHIRSourceRawProgram.bounded_rawAnswers]
  rw [← WHIRRealSimulator.real_ideal_view C registry.iv _ ((compile_counted source Q).mpr counted)]
  simp only [Option.bind_some,DuplexPublicSimulator.replayAnswers_keys]
  rfl

/-- Public event-only preparation and the chosen real seed/table execution
produce identical concrete final states. -/
theorem public_replayState (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (C : PrimitiveOracle) (source : Source cap R) (counted : WHIRSourceChronology.Counts Q source) :
    ((WHIRCausalRawROM.decorator (context registry) rfl Q cap
      (WHIRSourceResolver.publicResolver registry Q
        (runReal C registry.iv (WHIRSourceChronology.compile source)).view.result)).traceRecode
      (CausalBindingState.empty cap) (allocationTrace registry Q select C source)).2 =
      replayState registry Q C source counted (allocationTrace registry Q select C source) := by
  have eq := WHIRSourceResolver.traceRecode_actual registry Q (WHIRRealSimulator.rawTable Q C) C source counted
    (CausalBindingState.empty cap) (by intro e h; cases h) (allocationTrace registry Q select C source)
    (allocationTrace_agrees registry Q select C source)
  rw [← WHIRRealSimulator.real_ideal_view C registry.iv _ ((compile_counted source Q).mpr counted)] at eq
  exact congrArg Prod.snd eq

/-- Exercises the chosen real seed/raw table, actual partial source recovery,
immutable first-freeze logs, duplicate replay, and ordinary/hidden C tags. -/
def smoke : IO Unit := do
  let iv := DuplexCompression.parameterIV
  let early : Digest32 := fun _ => 17
  let registry : Public := ⟨iv,iv,fun _ => none,0⟩
  let ordinary := PublicMerkleLog.node iv 0 [] true
  let coordinate : Coordinate := ⟨⟨iv,iv,[]⟩,.output 0⟩
  have valid : DuplexEncoding.Admissible coordinate := by
    constructor
    · simp [coordinate]
    · decide
  let source : Source 0 Unit := .commit early (.ask (.primitive .direct ordinary) fun reply =>
    .commit reply (.ask (.construction coordinate valid) fun _ =>
      .ask (.primitive .direct ordinary) fun _ => .done ()))
  have counted : WHIRSourceChronology.Counts 4 source := by
    simp [source,WHIRSourceChronology.Counts,Query.cost,pathCost,DuplexEncoding.plan,coordinate]
  let missing : RawKey 4 → Option Digest32 := fun _ => none
  let first := DuplexPublicSimulator.runPartial missing iv
    ((DuplexPublicSimulator.simulator 4).initial blake2sOracle) (WHIRSourceChronology.compile source)
    4 (by omega) ((compile_counted source 4).mpr counted)
  let state := WHIRSourceObserver.privateReplay 4 iv missing blake2sOracle source counted (CausalBindingState.empty 0)
  let reply := blake2sOracle ordinary
  unless decide (reply ≠ early) do throw (IO.userError "smoke needs distinct announced and reply roots")
  unless decide (state.frozenLog early = some []) do
    throw (IO.userError "input root was not frozen before first C answer")
  unless decide (state.frozenLog reply = some [(ordinary,reply)]) do
    throw (IO.userError "reply-derived root was captured before its producing answer")
  unless decide (expand blake2sOracle iv first.observations = [(ordinary,reply)]) do
    throw (IO.userError "partial raw replay crossed the unanswered construction")
  let raw := constructionKey 4 iv coordinate (by decide)
  let acquired : RawKey 4 → Option Digest32 := fun key =>
    if key = raw then some (WHIRRealSimulator.rawTable 4 blake2sOracle key) else none
  let next := WHIRSourceObserver.privateReplay 4 iv acquired blake2sOracle source counted state
  unless decide (next.frozenLog early = state.frozenLog early ∧ next.frozenLog reply = state.frozenLog reply) do
    throw (IO.userError "replaying the source prefix replaced a first freeze")
  unless decide (next.publicLog = [(ordinary,reply)]) do
    throw (IO.userError "duplicate source replay changed public compression membership")
  let calls := primitiveLog blake2sOracle iv (WHIRSourceChronology.compile source) 4
    ((compile_counted source 4).mpr counted)
  unless decide (calls.map (fun e => tag e.1) = [0,1,6,0]) do
    throw (IO.userError "ordinary tag-zero / hidden construction-tag separation failed")
  let select : Unit → Option (RawWHIRKeys.Packet (context registry) 4) := fun _ => none
  unless (rootList registry 4 select source []).contains early &&
      !((rootList registry 4 select source []).contains reply) &&
      (rootList registry 4 select source [(ordinary,reply)]).contains reply do
    throw (IO.userError "policy did not preserve fixed-before-answer root timing")
  IO.println "source-frozen-prefix smoke: input root before answer; reply root after answer; finite raw cutoff; immutable repeated replay; full C tags [0,1,6,0]"

#print axioms actual_retained
#print axioms actual_backfill_retained
#print axioms allocation_captured
#print axioms cursor_replay
#print axioms allocationTrace_compiler
#print axioms public_replayState

end Whir.WHIRSourceFrozenPrefix
