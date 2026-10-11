import Whir.WHIRSourceObserver
import Whir.PublicMerkleBinding
import Whir.PrunedMerkleCoverage

namespace Whir.WHIRPhysicalSnapshots
open FiatShamirGame DuplexModeGame WHIRSourceChronology WHIRSourceObserver
open MerkleTransport.Commitments CausalBindingState

variable {cap : Nat}

/-- A retained whole-hash record was parsed at an actual earlier log prefix.
It need not remain parseable after an output collision changes a predecessor. -/
def Historical (log : PublicMerkleLog.PublicLog) (retained : Records) : Prop :=
  ∀ e ∈ retained, ∃ earlier : PublicMerkleLog.PublicLog,
    earlier.IsPrefix log ∧ e ∈ PublicMerkleLog.records earlier

/-- Collection keeps a first answer for every currently recognized input. -/
def Saturated (log : PublicMerkleLog.PublicLog) (retained : Records) : Prop :=
  ∀ bytes d, (bytes,d) ∈ PublicMerkleLog.records log → ∃ first, (bytes,first) ∈ retained

structure Invariant (C : PrimitiveOracle) (state : CausalBindingState.State cap) : Prop where
  logAuthentic : PublicMerkleLog.AuthenticLog C state.publicLog
  historical : Historical state.publicLog state.records
  saturated : Saturated state.publicLog state.records
  authentic : AuthenticState (PublicMerkleLog.hash C) state
  snapshots : ∀ root snap, lookup root state.registry = some snap →
    ∃ retained log, state.frozen root = some retained ∧ state.frozenLog root = some log ∧
      PublicMerkleLog.AuthenticLog C log ∧ Historical log retained ∧ Saturated log retained ∧
      snap.table = recordDomain retained ∧ log.IsPrefix state.publicLog

theorem prefix_mem {A : Type} {a b : List A} (hp : a.IsPrefix b) {e : A} (member : e ∈ a) : e ∈ b := by
  obtain ⟨suffix,rfl⟩ := hp
  exact List.mem_append_left _ member

theorem Historical.weaken {old next : PublicMerkleLog.PublicLog} {retained : Records}
    (history : Historical old retained) (hp : old.IsPrefix next) : Historical next retained := by
  intro e member
  obtain ⟨earlier,he,hm⟩ := history e member
  exact ⟨earlier,he.trans hp,hm⟩

theorem insert_prefix (log : PublicMerkleLog.PublicLog) (node : DuplexFraming.Node) (answer : Digest32) :
    log.IsPrefix (PublicMerkleLog.insert log node answer) := by
  unfold PublicMerkleLog.insert
  split
  · exact ⟨[],by simp⟩
  · exact ⟨[(node,answer)],rfl⟩

theorem empty_invariant (C : PrimitiveOracle) (cap : Nat) : Invariant C (empty cap) := by
  refine ⟨?_,?_,?_,empty_authentic _ _,?_⟩
  · simp [PublicMerkleLog.AuthenticLog,empty]
  · simp [Historical,empty]
  · simp [Saturated,empty,PublicMerkleLog.records]
  · intro root snap found
    simp [empty,lookup] at found

theorem observeRecords_fields (state : CausalBindingState.State cap) (added : Records) :
    (observeRecords state added).registry = state.registry ∧
    (observeRecords state added).frozen = state.frozen ∧
    (observeRecords state added).frozenLog = state.frozenLog ∧
    (observeRecords state added).publicLog = state.publicLog := by
  induction added generalizing state with
  | nil => exact ⟨rfl,rfl,rfl,rfl⟩
  | cons record rest ih =>
    have h := ih (CausalBindingState.observe state record.1 record.2)
    cases found : recordLookup record.1 state.records <;>
      simpa only [observeRecords,List.foldl_cons,CausalBindingState.observe,found] using h

theorem observeRecords_registry (state : CausalBindingState.State cap) (added : Records) :
    (observeRecords state added).registry = state.registry := (observeRecords_fields state added).1

theorem observeRecords_frozen (state : CausalBindingState.State cap) (added : Records) :
    (observeRecords state added).frozen = state.frozen := (observeRecords_fields state added).2.1

theorem observeRecords_frozenLog (state : CausalBindingState.State cap) (added : Records) :
    (observeRecords state added).frozenLog = state.frozenLog := (observeRecords_fields state added).2.2.1

theorem observeRecords_publicLog (state : CausalBindingState.State cap) (added : Records) :
    (observeRecords state added).publicLog = state.publicLog := (observeRecords_fields state added).2.2.2

theorem observe_record_origin (state : CausalBindingState.State cap) (bytes : List Byte) (digest : Digest32)
    (e : List Byte × Digest32) (member : e ∈ (CausalBindingState.observe state bytes digest).records) :
    e ∈ state.records ∨ e = (bytes,digest) := by
  unfold CausalBindingState.observe at member
  cases found : recordLookup bytes state.records with
  | some first => exact Or.inl (by simpa only [found] using member)
  | none =>
    simp only [found,List.mem_cons] at member
    exact member.symm

theorem observeRecords_origin (state : CausalBindingState.State cap) (added : Records)
    (e : List Byte × Digest32) (member : e ∈ (observeRecords state added).records) :
    e ∈ state.records ∨ e ∈ added := by
  induction added generalizing state with
  | nil => exact Or.inl member
  | cons record rest ih =>
    change e ∈ (observeRecords (CausalBindingState.observe state record.1 record.2) rest).records at member
    rcases ih _ member with old | new
    · rcases observe_record_origin state record.1 record.2 e old with old | same
      · exact Or.inl old
      · exact Or.inr (List.mem_cons.mpr (Or.inl (by simpa using same)))
    · exact Or.inr (List.mem_cons_of_mem _ new)

theorem observe_has (state : CausalBindingState.State cap) (bytes : List Byte) (digest : Digest32) :
    ∃ first, recordLookup bytes (CausalBindingState.observe state bytes digest).records = some first := by
  unfold CausalBindingState.observe
  cases found : recordLookup bytes state.records with
  | some first => exact ⟨first,found⟩
  | none => exact ⟨digest,by simp [recordLookup]⟩

theorem observeRecords_contains (state : CausalBindingState.State cap) (added : Records)
    (bytes : List Byte) (digest : Digest32) (member : (bytes,digest) ∈ added) :
    ∃ first, (bytes,first) ∈ (observeRecords state added).records := by
  induction added generalizing state with
  | nil => simp at member
  | cons record rest ih =>
    rcases List.mem_cons.mp member with same | tail
    · cases same
      obtain ⟨first,hfirst⟩ := observe_has state bytes digest
      exact ⟨first,recordLookup_mem _ bytes first ((observeRecords_extends _ rest).records bytes first hfirst)⟩
    · exact ih (CausalBindingState.observe state record.1 record.2) tail

theorem observePublic_invariant (C : PrimitiveOracle) (state : CausalBindingState.State cap)
    (node : DuplexFraming.Node) (old : Invariant C state) :
    Invariant C (observePublic state node (C node)) := by
  let log := PublicMerkleLog.insert state.publicLog node (C node)
  have hp : state.publicLog.IsPrefix log := insert_prefix _ _ _
  have auth : PublicMerkleLog.AuthenticLog C log := PublicMerkleLog.insert_authentic C _ old.logAuthentic node
  refine ⟨?_,?_,?_,observePublic_authentic C state node old.authentic old.logAuthentic,?_⟩
  · simpa only [observePublic,PublicMerkleLog.observe,observeRecords_publicLog] using auth
  · change Historical (observeRecords _ _).publicLog (observeRecords _ _).records
    rw [observeRecords_publicLog]
    intro e member
    rcases observeRecords_origin _ _ e member with prior | fresh
    · exact old.historical.weaken hp e prior
    · exact ⟨log,⟨[],by simp [log,PublicMerkleLog.observe]⟩,fresh⟩
  · change Saturated (observeRecords _ _).publicLog (observeRecords _ _).records
    rw [observeRecords_publicLog]
    exact observeRecords_contains _ _
  · intro root snap found
    have prior : lookup root state.registry = some snap := by
      simpa only [observePublic,PublicMerkleLog.observe,observeRecords_registry] using found
    obtain ⟨retained,frozen,hf,hl,ha,hh,hs,ht,hprefix⟩ := old.snapshots root snap prior
    refine ⟨retained,frozen,?_,?_,ha,hh,hs,ht,?_⟩
    · simpa only [observePublic,PublicMerkleLog.observe,observeRecords_frozen] using hf
    · simpa only [observePublic,PublicMerkleLog.observe,observeRecords_frozenLog] using hl
    · simpa only [observePublic,PublicMerkleLog.observe,observeRecords_publicLog] using hprefix.trans hp

theorem registerRoot_invariant (C : PrimitiveOracle) (state : CausalBindingState.State cap)
    (root : Digest32) (old : Invariant C state) : Invariant C (registerRoot state root) := by
  unfold registerRoot
  cases found : lookup root state.registry with
  | some snap => exact old
  | none =>
    refine ⟨old.logAuthentic,old.historical,old.saturated,?_,?_⟩
    · simpa only [registerRoot,found] using registerRoot_authentic (PublicMerkleLog.hash C) state root old.authentic
    · intro r snap known
      by_cases same : r = root
      · subst r
        have hs : snap = snapshot state.records := by
          simpa [register,found,lookup] using known.symm
        subst snap
        exact ⟨state.records,state.publicLog,by simp,by simp,old.logAuthentic,
          old.historical,old.saturated,rfl,⟨[],by simp⟩⟩
      · have prior : lookup r state.registry = some snap := by
          simpa [register,found,lookup,same] using known
        obtain ⟨retained,log,hf,hl,ha,hh,hs,ht,hprefix⟩ := old.snapshots r snap prior
        exact ⟨retained,log,by simpa [Function.update_of_ne same] using hf,
          by simpa [Function.update_of_ne same] using hl,ha,hh,hs,ht,hprefix⟩

theorem Invariant.covered {C : PrimitiveOracle} {state : CausalBindingState.State cap}
    (sound : Invariant C state) : Covered state := by
  intro root snap known
  obtain ⟨retained,log,hf,hl,ha,hh,hs,ht,hprefix⟩ := sound.snapshots root snap known
  simp only [hf,Option.getD_some,ht]
  exact Finset.Subset.refl _

def RealEvent (C : PrimitiveOracle) (iv : Digest32) : Event cap → Prop
  | .answer query value => value = realAnswer C iv query
  | .commit _ => True
  | .claims _ _ _ => True

theorem step_invariant (C : PrimitiveOracle) (iv : Digest32)
    (state next : CausalBindingState.State cap) (event : Event cap)
    (old : Invariant C state) (real : RealEvent C iv event) (stepped : step state event = .ok next) :
    Invariant C next := by
  cases event with
  | answer query value =>
    cases query with
    | primitive purpose node =>
      change value = C node at real
      subst value
      cases stepped
      exact observePublic_invariant C state node old
    | construction coordinate valid => cases stepped; exact old
  | commit root => cases stepped; exact registerRoot_invariant C state root old
  | claims profile entry request =>
    unfold step at stepped
    cases known : lookup request.root state.registry <;> simp only [known] at stepped
    · cases stepped
    · cases stepped; exact old

theorem error_invariant (C : PrimitiveOracle) (state : CausalBindingState.State cap)
    (error : Option Digest32) (old : Invariant C state) : Invariant C {state with sourceError := error} :=
  ⟨old.logAuthentic,old.historical,old.saturated,old.authentic,old.snapshots⟩

theorem replayTracked_invariant (C : PrimitiveOracle) (iv : Digest32)
    (state : CausalBindingState.State cap) (events : List (Event cap)) (old : Invariant C state)
    (real : ∀ e ∈ events, RealEvent C iv e) : Invariant C (replayTracked state events) := by
  induction events generalizing state with
  | nil => exact old
  | cons event rest ih =>
    unfold replayTracked
    cases progress : step state event with
    | error root =>
      exact ih _ (error_invariant C state (state.sourceError.or (some root)) old)
        (fun e he => real e (List.mem_cons_of_mem _ he))
    | ok next =>
      exact ih next (step_invariant C iv state next event old (real event (by simp)) progress)
        (fun e he => real e (List.mem_cons_of_mem _ he))

theorem replayTracked_empty_invariant (C : PrimitiveOracle) (iv : Digest32)
    (events : List (Event cap)) (real : ∀ e ∈ events, RealEvent C iv e) :
    Invariant C (replayTracked (empty cap) events) :=
  replayTracked_invariant C iv _ events (empty_invariant C cap) real

theorem answer_mem_observations (events : List (Event cap)) (q : Query) (d : Digest32)
    (member : Event.answer q d ∈ events) : (⟨q,d⟩ : Observation) ∈ WHIRSourceChronology.observations events := by
  induction events with
  | nil => simp at member
  | cons event rest ih =>
    rcases List.mem_cons.mp member with same | tail
    · cases same; exact List.mem_cons_self
    · cases event <;> simp only [WHIRSourceChronology.observations]
      · exact List.mem_cons_of_mem _ (ih tail)
      · exact ih tail
      · exact ih tail

theorem real_source_events (C : PrimitiveOracle) (iv : Digest32) (source : Source cap R) :
    ∀ e ∈ (runReal C iv (compile source)).view.result.events, RealEvent C iv e := by
  intro e member
  cases e with
  | commit => trivial
  | claims => trivial
  | answer q d =>
    have observed := answer_mem_observations _ q d member
    rw [real_source_trace] at observed
    exact PublicMerkleProgram.runReal_answers C iv (compile source) ⟨q,d⟩ observed

theorem real_source_invariant (C : PrimitiveOracle) (iv : Digest32) (source : Source cap R) :
    Invariant C (replayTracked (empty cap) (runReal C iv (compile source)).view.result.events) :=
  replayTracked_empty_invariant C iv _ (real_source_events C iv source)

/-- The exact retained-table hypotheses consumed by `openQuery_retained`,
including provenance and saturation derived from source transitions. -/
theorem Invariant.retained {C : PrimitiveOracle} {state : CausalBindingState.State cap}
    (sound : Invariant C state) (root : Digest32) (snap : Snapshot)
    (known : lookup root state.registry = some snap) :
    ∃ retained log, state.frozen root = some retained ∧ state.frozenLog root = some log ∧
      PublicMerkleLog.AuthenticLog C log ∧
      (∀ e ∈ retained, ∃ earlier : PublicMerkleLog.PublicLog,
        (∀ q ∈ earlier, q ∈ log) ∧ e ∈ PublicMerkleLog.records earlier) ∧
      Saturated log retained ∧ snap.table = recordDomain retained := by
  obtain ⟨retained,log,hf,hl,ha,hh,hs,ht,hprefix⟩ := sound.snapshots root snap known
  refine ⟨retained,log,hf,hl,ha,?_,hs,ht⟩
  intro e member
  obtain ⟨earlier,he,hm⟩ := hh e member
  exact ⟨earlier,fun _ hq => prefix_mem he hq,hm⟩

theorem first_capture_immutable (state : CausalBindingState.State cap) (root : Digest32) (snap : Snapshot)
    (known : lookup root state.registry = some snap) (events : List (Event cap)) :
    lookup root (replayTracked state events).registry = some snap ∧
      (replayTracked state events).frozen root = state.frozen root ∧
      (replayTracked state events).frozenLog root = state.frozenLog root := by
  have growth := replayTracked_extends state events
  exact ⟨growth.registry root snap known,(growth.frozen root snap known).symm,
    (growth.frozenLog root snap known).symm⟩

theorem first_capture (state : CausalBindingState.State cap) (root : Digest32)
    (unknown : lookup root state.registry = none) :
    lookup root (registerRoot state root).registry = some (snapshot state.records) ∧
      (registerRoot state root).frozen root = some state.records ∧
      (registerRoot state root).frozenLog root = some state.publicLog := by
  simp [registerRoot,unknown,register,lookup]

theorem missing_claim_sticky (state : CausalBindingState.State cap) (profile : ParameterBounds.Profile)
    (entry : FramedHistory) (request : ClaimRequest cap profile) (rest : List (Event cap))
    (ready : state.sourceError = none) (unknown : lookup request.root state.registry = none) :
    (replayTracked state (.claims profile entry request :: rest)).sourceError = some request.root := by
  simp only [replayTracked,step,unknown]
  apply replayTracked_error_sticky
  simp [ready]

theorem insert_mem_iff (C : PrimitiveOracle) (log : PublicMerkleLog.PublicLog)
    (auth : PublicMerkleLog.AuthenticLog C log) (node : DuplexFraming.Node)
    (e : DuplexFraming.Node × Digest32) :
    e ∈ PublicMerkleLog.insert log node (C node) ↔ e ∈ log ∨ e = (node,C node) := by
  cases found : PublicMerkleLog.lookup log node with
  | none => simp [PublicMerkleLog.insert,found]
  | some d =>
    have present := PublicMerkleLog.lookup_mem found
    have same := auth node d present
    have current : (node,C node) ∈ log := by simpa only [same] using present
    simp only [PublicMerkleLog.insert,found,Option.isSome_some,ite_true]
    constructor
    · exact Or.inl
    · rintro (old | rfl)
      · exact old
      · exact current

theorem registerRoot_publicLog (state : CausalBindingState.State cap) (root : Digest32) :
    (registerRoot state root).publicLog = state.publicLog := by
  unfold registerRoot
  split <;> rfl

theorem step_publicLog (state next : CausalBindingState.State cap) (event : Event cap)
    (progress : step state event = .ok next) :
    next.publicLog = match event with
      | .answer (.primitive _ node) value => PublicMerkleLog.insert state.publicLog node value
      | _ => state.publicLog := by
  cases event with
  | answer query value =>
    cases query with
    | primitive purpose node =>
      cases progress
      simp only [observePublic,PublicMerkleLog.observe,observeRecords_publicLog]
    | construction coordinate valid => cases progress; rfl
  | commit root => cases progress; exact registerRoot_publicLog state root
  | claims profile entry request =>
    unfold step at progress
    cases known : lookup request.root state.registry <;> simp only [known] at progress
    · cases progress
    · cases progress; rfl

theorem step_publicLog_prefix (state next : CausalBindingState.State cap) (event : Event cap)
    (progress : step state event = .ok next) : state.publicLog.IsPrefix next.publicLog := by
  rw [step_publicLog state next event progress]
  cases event with
  | answer query value =>
    cases query with
    | primitive purpose node => exact insert_prefix _ _ _
    | construction coordinate valid => exact ⟨[],by simp⟩
  | commit => exact ⟨[],by simp⟩
  | claims => exact ⟨[],by simp⟩

theorem replayTracked_publicLog_prefix (state : CausalBindingState.State cap) (events : List (Event cap)) :
    state.publicLog.IsPrefix (replayTracked state events).publicLog := by
  induction events generalizing state with
  | nil => exact ⟨[],by simp [replayTracked]⟩
  | cons event rest ih =>
    unfold replayTracked
    cases progress : step state event with
    | error root => exact ih {state with sourceError := state.sourceError.or (some root)}
    | ok next => exact (step_publicLog_prefix state next event progress).trans (ih next)

theorem step_publicLog_authentic (C : PrimitiveOracle) (iv : Digest32)
    (state next : CausalBindingState.State cap) (event : Event cap)
    (auth : PublicMerkleLog.AuthenticLog C state.publicLog) (real : RealEvent C iv event)
    (progress : step state event = .ok next) : PublicMerkleLog.AuthenticLog C next.publicLog := by
  rw [step_publicLog state next event progress]
  cases event with
  | answer query value =>
    cases query with
    | primitive purpose node =>
      change value = C node at real
      subst value
      exact PublicMerkleLog.insert_authentic C _ auth node
    | construction => exact auth
  | commit => exact auth
  | claims => exact auth

theorem step_publicLog_mem_iff (C : PrimitiveOracle) (iv : Digest32)
    (state next : CausalBindingState.State cap) (event : Event cap)
    (auth : PublicMerkleLog.AuthenticLog C state.publicLog) (real : RealEvent C iv event)
    (progress : step state event = .ok next) (node : DuplexFraming.Node) (digest : Digest32) :
    (node,digest) ∈ next.publicLog ↔ (node,digest) ∈ state.publicLog ∨
      ∃ purpose, event = .answer (.primitive purpose node) digest := by
  rw [step_publicLog state next event progress]
  cases event with
  | answer query value =>
    cases query with
    | primitive purpose input =>
      change value = C input at real
      subst value
      rw [insert_mem_iff C _ auth input]
      constructor
      · rintro (old | same)
        · exact Or.inl old
        · obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
          exact Or.inr ⟨purpose,rfl⟩
      · rintro (old | ⟨p,same⟩)
        · exact Or.inl old
        · cases same
          exact Or.inr rfl
    | construction coordinate valid => simp
  | commit => simp
  | claims => simp

theorem step_error_not_primitive (state : CausalBindingState.State cap) (event : Event cap)
    (root : Digest32) (progress : step state event = .error root)
    (purpose : Purpose) (node : DuplexFraming.Node) (digest : Digest32) :
    event ≠ .answer (.primitive purpose node) digest := by
  intro same
  cases same
  cases progress

/-- Exact membership, including after chronology errors. First-answer
deduplication is harmless here because state and event answers are authentic.
No saturation or all-C-prefix coverage hypothesis is supplied. -/
theorem replayTracked_publicLog_mem_iff (C : PrimitiveOracle) (iv : Digest32)
    (state : CausalBindingState.State cap) (events : List (Event cap))
    (auth : PublicMerkleLog.AuthenticLog C state.publicLog)
    (real : ∀ e ∈ events, RealEvent C iv e) (node : DuplexFraming.Node) (digest : Digest32) :
    (node,digest) ∈ (replayTracked state events).publicLog ↔
      (node,digest) ∈ state.publicLog ∨ ∃ purpose, Event.answer (.primitive purpose node) digest ∈ events := by
  induction events generalizing state with
  | nil => simp [replayTracked]
  | cons event rest ih =>
    have tailReal : ∀ e ∈ rest, RealEvent C iv e := fun e he => real e (List.mem_cons_of_mem _ he)
    unfold replayTracked
    cases progress : step state event with
    | error root =>
      rw [ih {state with sourceError := state.sourceError.or (some root)} auth tailReal]
      constructor
      · rintro (old | ⟨purpose,member⟩)
        · exact Or.inl old
        · exact Or.inr ⟨purpose,List.mem_cons_of_mem _ member⟩
      · rintro (old | ⟨purpose,member⟩)
        · exact Or.inl old
        · rcases List.mem_cons.mp member with same | tail
          · exact False.elim (step_error_not_primitive state event root progress purpose node digest same.symm)
          · exact Or.inr ⟨purpose,tail⟩
    | ok next =>
      rw [ih next (step_publicLog_authentic C iv state next event auth (real event (by simp)) progress) tailReal,
        step_publicLog_mem_iff C iv state next event auth (real event (by simp)) progress node digest]
      simp only [List.mem_cons,exists_or,or_assoc,eq_comm]

theorem observePublic_settled_fields (state : CausalBindingState.State cap)
    (node : DuplexFraming.Node) (digest : Digest32) (known : (node,digest) ∈ state.publicLog) :
    (observePublic state node digest).registry = state.registry ∧
    (observePublic state node digest).frozen = state.frozen ∧
    (observePublic state node digest).frozenLog = state.frozenLog ∧
    (observePublic state node digest).publicLog = state.publicLog := by
  obtain ⟨first,found⟩ := PublicMerkleLog.lookup_exists known
  have unchanged : PublicMerkleLog.insert state.publicLog node digest = state.publicLog := by
    simp [PublicMerkleLog.insert,found]
  simpa only [observePublic,PublicMerkleLog.observe,unchanged] using
    observeRecords_fields state (PublicMerkleLog.records state.publicLog)

/-- Replaying an already settled prefix cannot move a root's first capture.
No authenticity premise is needed for these four fields. The error flag may
change, and this theorem deliberately makes no equality claim about records. -/
theorem replayTracked_settled_fields (state : CausalBindingState.State cap) (events : List (Event cap))
    (answers : ∀ purpose node digest, Event.answer (.primitive purpose node) digest ∈ events →
      (node,digest) ∈ state.publicLog)
    (commits : ∀ root, Event.commit root ∈ events → ∃ snap, lookup root state.registry = some snap) :
    (replayTracked state events).registry = state.registry ∧
    (replayTracked state events).frozen = state.frozen ∧
    (replayTracked state events).frozenLog = state.frozenLog ∧
    (replayTracked state events).publicLog = state.publicLog := by
  induction events generalizing state with
  | nil => exact ⟨rfl,rfl,rfl,rfl⟩
  | cons event rest ih =>
    have resume (next : CausalBindingState.State cap)
        (fields : next.registry = state.registry ∧ next.frozen = state.frozen ∧
          next.frozenLog = state.frozenLog ∧ next.publicLog = state.publicLog) :
        (replayTracked next rest).registry = state.registry ∧
        (replayTracked next rest).frozen = state.frozen ∧
        (replayTracked next rest).frozenLog = state.frozenLog ∧
        (replayTracked next rest).publicLog = state.publicLog := by
      have ha : ∀ purpose node digest, Event.answer (.primitive purpose node) digest ∈ rest →
          (node,digest) ∈ next.publicLog := by
        intro purpose node digest member
        rw [fields.2.2.2]
        exact answers purpose node digest (List.mem_cons_of_mem _ member)
      have hc : ∀ root, Event.commit root ∈ rest → ∃ snap, lookup root next.registry = some snap := by
        intro root member
        rw [fields.1]
        exact commits root (List.mem_cons_of_mem _ member)
      have done := ih next ha hc
      exact ⟨done.1.trans fields.1,done.2.1.trans fields.2.1,
        done.2.2.1.trans fields.2.2.1,done.2.2.2.trans fields.2.2.2⟩
    unfold replayTracked
    cases event with
    | answer query digest =>
      cases query with
      | primitive purpose node =>
        exact resume _ (observePublic_settled_fields state node digest (answers purpose node digest (by simp)))
      | construction coordinate valid => exact resume state ⟨rfl,rfl,rfl,rfl⟩
    | commit root =>
      obtain ⟨snap,known⟩ := commits root (by simp)
      simpa only [step,registerRoot,known] using resume state ⟨rfl,rfl,rfl,rfl⟩
    | claims profile entry request =>
      simp only [step]
      cases known : lookup request.root state.registry with
      | none => exact resume {state with sourceError := state.sourceError.or (some request.root)} ⟨rfl,rfl,rfl,rfl⟩
      | some snap => exact resume state ⟨rfl,rfl,rfl,rfl⟩

end Whir.WHIRPhysicalSnapshots
