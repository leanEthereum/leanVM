import Whir.WHIRPhysicalVerifier
import Whir.WHIRSourceResolver

/-! Operational caller-input provenance for the actual physical verifier.
Only the source-owned `Result.events` observations are used; mode-completion
queries are not part of this prefix. The caller reader's finite answers are
exactly its latest matching construction observations, and are transported to
the concrete public-layout registry without a decoder-correctness premise.

`callerHistory` is a finite provenance projection, not a replacement decoder.
`packetRequest_compiled_prefix` connects the original source prefix to the
actual raw allocation compiler's dependency history, even for early prequeries.
Production resolver claims continue to use `packetRequest` on that history:
neither source announcements nor future WHIR samples enter its decoder. -/
namespace Whir.WHIRPhysicalCaller
open Concrete Protocol FiatShamirGame DuplexModeGame PublicMerkleProgram
open RawOracleCoupling RawOracleCoupling.Concrete WHIRPhysicalVerifier
open WHIRCallerClaims WHIRCallerRegistry
open RawWHIRKeys (Context Packet)
set_option maxHeartbeats 800000

local instance : DecidableEq Terminal := by
  intro a b
  cases a <;> cases b <;> simp <;> infer_instance
local instance : DecidableEq Coordinate := by
  intro a b
  cases a
  cases b
  simp only [Coordinate.mk.injEq]
  infer_instance

/-- One observed construction updates only its literal full coordinate. Public
primitive calls and different caller-entry clones cannot supply its answer. -/
def observeAt (wanted : Coordinate) (previous : Option Digest32) (observation : Observation) : Option Digest32 :=
  match observation.query with
  | .primitive _ _ => previous
  | .construction coordinate _ => if wanted = coordinate then some observation.answer else previous

def observedAnswers (trace : List Observation) (initial : Coordinate → Option Digest32) :
    Coordinate → Option Digest32 :=
  fun wanted => trace.foldl (observeAt wanted) (initial wanted)

def latestAnswers (trace : List Observation) : Coordinate → Option Digest32 :=
  observedAnswers trace (fun _ => none)

theorem observedAnswers_cons (observation : Observation) (rest : List Observation)
    (initial : Coordinate → Option Digest32) :
    observedAnswers (observation :: rest) initial =
      observedAnswers rest (fun wanted => observeAt wanted (initial wanted) observation) := rfl

theorem observedAnswers_append (before after : List Observation) (initial : Coordinate → Option Digest32) :
    observedAnswers (before ++ after) initial = observedAnswers after (observedAnswers before initial) := by
  funext wanted
  simp only [observedAnswers,List.foldl_append]

theorem observedAnswers_unchanged (trace : List Observation) (initial : Coordinate → Option Digest32)
    (wanted : Coordinate)
    (absent : ∀ observation ∈ trace, ∀ valid,
      observation.query ≠ .construction wanted valid) :
    observedAnswers trace initial wanted = initial wanted := by
  induction trace generalizing initial with
  | nil => rfl
  | cons observation rest ih =>
    rw [observedAnswers_cons,ih _ (fun observation member => absent observation (List.mem_cons_of_mem _ member))]
    cases observation with
    | mk query answer =>
      cases query with
      | primitive => rfl
      | construction coordinate valid =>
        have different : wanted ≠ coordinate := by
          intro same
          subst coordinate
          exact absent ⟨.construction wanted valid,answer⟩ List.mem_cons_self valid rfl
        exact ite_eq_right different

/-- This characterizes the answer by the latest matching construction, rather
than merely asserting membership in an unstructured list of replies. -/
theorem observedAnswers_latest (before after : List Observation)
    (initial : Coordinate → Option Digest32) (wanted : Coordinate)
    (valid : DuplexEncoding.Admissible wanted) (answer : Digest32)
    (last : ∀ observation ∈ after, ∀ proof,
      observation.query ≠ .construction wanted proof) :
    observedAnswers (before ++ ⟨.construction wanted valid,answer⟩ :: after) initial wanted = some answer := by
  rw [observedAnswers_append,observedAnswers_cons,observedAnswers_unchanged _ _ wanted last]
  simp [observeAt]

/-- Exact continuation inversion for arbitrary operational runs. Queries are
not inferred from a claimed transcript: they are forced by `readCallerInputs`. -/
theorem readCallerInputs_run {cap : Nat} {R : Type} (ctx : Context) (Q : Nat)
    (packet : Packet ctx Q) (positions : List (WHIRModeFinal.CallerPosition ctx Q packet))
    (initial : Coordinate → Option Digest32)
    (next : (Coordinate → Option Digest32) → WHIRSourceChronology.Source cap R)
    (trace : List Observation) (result : R)
    (run : Runs (WHIRSourceChronology.erase (readCallerInputs ctx Q packet positions initial next)) trace result) :
    ∃ before after, trace = before ++ after ∧ before.length = positions.length ∧
      before.map Observation.query = positions.map (fun q => Query.construction q.val
        (RawWHIRKeys.callerOutput_admissible ctx Q packet q.val q.property)) ∧
      Runs (WHIRSourceChronology.erase (next (observedAnswers before initial))) after result := by
  induction positions generalizing initial trace with
  | nil => exact ⟨[],trace,rfl,rfl,rfl,run⟩
  | cons q qs ih =>
    change Runs (.ask (.construction q.val (RawWHIRKeys.callerOutput_admissible ctx Q packet q.val q.property))
      (fun answer => WHIRSourceChronology.erase (readCallerInputs ctx Q packet qs
        (fun key => if key = q.val then some answer else initial key) next))) trace result at run
    cases run with
    | ask answer continued =>
      obtain ⟨before,after,traceEq,count,queries,last⟩ := ih _ _ continued
      refine ⟨⟨.construction q.val (RawWHIRKeys.callerOutput_admissible ctx Q packet q.val q.property),answer⟩ :: before,
        after,by simp [traceEq],by simp [count],by simp [queries],?_⟩
      exact last

private theorem map_run {R S : Type} (f : R → S) (program : Program R)
    (trace : List Observation) (result : S)
    (run : Runs (WHIRSourceChronology.map f program) trace result) :
    ∃ value, Runs program trace value ∧ f value = result := by
  induction program generalizing trace result with
  | done value =>
    cases run
    exact ⟨value,.done value,rfl⟩
  | ask query next ih =>
    cases run with
    | ask answer continued =>
      obtain ⟨value,run,equal⟩ := ih answer _ _ continued
      exact ⟨value,.ask answer run,equal⟩

/-- Compiling source annotations neither invents observations nor changes the
operational result. This applies to arbitrary finite runs, including ideal
executions, without referring to a simulator's backfilled mode view. -/
theorem compile_run {cap : Nat} {R : Type} (source : WHIRSourceChronology.Source cap R)
    (trace : List Observation) (result : WHIRSourceChronology.Result cap R)
    (run : Runs (WHIRSourceChronology.compile source) trace result) :
    Runs (WHIRSourceChronology.erase source) trace result.value ∧
      WHIRSourceChronology.observations result.events = trace := by
  induction source generalizing trace result with
  | done value =>
    cases run
    exact ⟨.done value,rfl⟩
  | ask query next ih =>
    cases run with
    | ask answer continued =>
      obtain ⟨value,continuedRun,rfl⟩ := map_run
        (WHIRSourceChronology.prepend (.answer query answer)) (WHIRSourceChronology.compile (next answer)) _ _ continued
      obtain ⟨erased,observed⟩ := ih answer _ _ continuedRun
      exact ⟨.ask answer erased,congrArg (List.cons (⟨query,answer⟩ : Observation)) observed⟩
  | commit root next ih =>
    obtain ⟨value,continuedRun,rfl⟩ := map_run
      (WHIRSourceChronology.prepend (.commit root)) (WHIRSourceChronology.compile next) _ _ run
    exact ih trace value continuedRun
  | claims profile entry request next ih =>
    obtain ⟨value,continuedRun,rfl⟩ := map_run
      (WHIRSourceChronology.prepend (.claims profile entry request)) (WHIRSourceChronology.compile next) _ _ run
    exact ih trace value continuedRun

theorem ideal_source_runs {Q cap : Nat} {Seed State R : Type} (sim : Simulator Q Seed State)
    (table : RawKey Q → Digest32) (iv : Digest32) (state : State)
    (source : WHIRSourceChronology.Source cap R) (remaining : Nat) (limit : remaining ≤ Q)
    (counted : WHIRSourceChronology.Counts remaining source) :
    let result := (runIdeal sim table iv state (WHIRSourceChronology.compile source) remaining limit
      ((WHIRSourceChronology.compile_counted source remaining).mpr counted)).view.result
    Runs (WHIRSourceChronology.erase source) (WHIRSourceChronology.observations result.events) result.value := by
  dsimp only
  obtain ⟨run,observed⟩ := compile_run source _ _
    (runIdeal_runs sim table iv state (WHIRSourceChronology.compile source) remaining limit
      ((WHIRSourceChronology.compile_counted source remaining).mpr counted))
  rw [observed]
  exact run

/-- Runs of the source-owned result use precisely `Result.events`, excluding
any backfilled completion records appended by an outer mode experiment. -/
theorem real_source_runs {cap : Nat} {R : Type} (oracle : PrimitiveOracle) (iv : Digest32)
    (source : WHIRSourceChronology.Source cap R) :
    Runs (WHIRSourceChronology.erase source)
      (WHIRSourceChronology.observations (runReal oracle iv (WHIRSourceChronology.compile source)).view.result.events)
      (runReal oracle iv (WHIRSourceChronology.compile source)).view.result.value := by
  have erase := congrArg Execution.view (WHIRSourceChronology.real_source_erasure oracle iv source)
  have observations := congrArg View.observations erase
  have value := congrArg View.result erase
  change (runReal oracle iv (WHIRSourceChronology.compile source)).view.observations = _ at observations
  change (runReal oracle iv (WHIRSourceChronology.compile source)).view.result.value = _ at value
  rw [WHIRSourceChronology.real_source_trace,observations,value]
  exact runReal_runs oracle iv (WHIRSourceChronology.erase source)

/-- Concrete keys for distinct prior caller coordinates cannot alias. -/
theorem caller_key_injective (ctx : Context) (Q : Nat) (packet : Packet ctx Q)
    (a b : WHIRModeFinal.CallerPosition ctx Q packet)
    (same : RawWHIRKeys.callerOutputKey ctx Q packet a.val a.property =
      RawWHIRKeys.callerOutputKey ctx Q packet b.val b.property) : a.val = b.val := by
  apply constructionKey_injective Q ctx.iv
    (RawWHIRKeys.callerOutput_admissible ctx Q packet a.val a.property)
    (RawWHIRKeys.callerOutput_admissible ctx Q packet b.val b.property)
    (RawWHIRKeys.callerOutput_pathBound ctx Q packet a.val a.property)
    (RawWHIRKeys.callerOutput_pathBound ctx Q packet b.val b.property)
  exact congrArg Subtype.val same

/-- The finite caller history recovered from actual observations is newest
first, matching the last-write semantics of the source reader. -/
def addCallerObservation (ctx : Context) (Q : Nat) (packet : Packet ctx Q)
    (history : List (Sigma (GroupAnswer ctx Q))) (observation : Observation) :
    List (Sigma (GroupAnswer ctx Q)) :=
  match observation.query with
  | .primitive _ _ => history
  | .construction coordinate _ =>
    if prior : coordinate ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val) then
      ⟨.inr (RawWHIRKeys.callerOutputKey ctx Q packet coordinate prior),observation.answer⟩ :: history
    else history

def callerHistory (ctx : Context) (Q : Nat) (packet : Packet ctx Q) (trace : List Observation) :
    List (Sigma (GroupAnswer ctx Q)) :=
  trace.foldl (addCallerObservation ctx Q packet) []

theorem callerAnswers_addObservation (ctx : Context) (Q : Nat) (packet : Packet ctx Q)
    (history : List (Sigma (GroupAnswer ctx Q))) (observation : Observation)
    (wanted : Coordinate) (prior : wanted ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val)) :
    callerAnswers ctx Q packet (addCallerObservation ctx Q packet history observation) wanted =
      observeAt wanted (callerAnswers ctx Q packet history wanted) observation := by
  cases observation with
  | mk query answer =>
    cases query with
    | primitive => rfl
    | construction coordinate valid =>
      by_cases known : coordinate ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val)
      · simp only [addCallerObservation,dite_eq_left known,callerAnswers,dite_eq_left prior,garbageAnswer,observeAt]
        by_cases same : wanted = coordinate
        · subst coordinate
          split
          · simp
          · rename_i different
            exact False.elim (different rfl)
        · have keys : RawWHIRKeys.callerOutputKey ctx Q packet coordinate known ≠
              RawWHIRKeys.callerOutputKey ctx Q packet wanted prior := by
            intro equal
            exact same (caller_key_injective ctx Q packet ⟨coordinate,known⟩ ⟨wanted,prior⟩ equal).symm
          split
          · rename_i equal
            exact False.elim (keys equal)
          · rfl
      · have different : wanted ≠ coordinate := fun equal => known (equal ▸ prior)
        simp only [addCallerObservation,dite_eq_right known,observeAt,ite_eq_right different]

theorem callerAnswers_foldObservations (ctx : Context) (Q : Nat) (packet : Packet ctx Q)
    (trace : List Observation) (history : List (Sigma (GroupAnswer ctx Q)))
    (wanted : Coordinate) (prior : wanted ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val)) :
    callerAnswers ctx Q packet (trace.foldl (addCallerObservation ctx Q packet) history) wanted =
      observedAnswers trace (callerAnswers ctx Q packet history) wanted := by
  induction trace generalizing history with
  | nil => rfl
  | cons observation rest ih =>
    rw [List.foldl_cons,ih]
    change rest.foldl (observeAt wanted)
      (callerAnswers ctx Q packet (addCallerObservation ctx Q packet history observation) wanted) = _
    rw [callerAnswers_addObservation ctx Q packet history observation wanted prior]
    rfl

theorem callerAnswers_history (ctx : Context) (Q : Nat) (packet : Packet ctx Q)
    (trace : List Observation) (wanted : Coordinate)
    (prior : wanted ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val)) :
    callerAnswers ctx Q packet (callerHistory ctx Q packet trace) wanted = latestAnswers trace wanted := by
  rw [callerHistory,callerAnswers_foldObservations ctx Q packet trace [] wanted prior]
  change trace.foldl (observeAt wanted) (callerAnswers ctx Q packet [] wanted) = _
  simp only [callerAnswers,dite_eq_left prior,garbageAnswer]
  rfl

theorem packetRequest_observations (registry : Public) (Q cap : Nat)
    (packet : Packet (context registry) Q) (trace : List Observation) :
    packetRequest registry Q cap packet (callerHistory (context registry) Q packet trace) =
      decodeAvailableRequest cap packet.val.profile (callerLanes (packetLayout registry Q packet))
        (packetLayout registry Q packet) (RawWHIRKeys.entry (context registry) packet.val) (latestAnswers trace) := by
  apply decodeAvailableRequest_prior_only
  exact callerAnswers_history (context registry) Q packet trace

/-- Accepted physical decoding fixes lanes from the same public source layout. -/
theorem decoded_lanes (cap : Nat) (profile : ParameterBounds.Profile) (lanes : Nat)
    (layout : CallerLayout) (entry : FramedHistory) (answers : Coordinate → Option Digest32)
    (request : CausalBindingState.ClaimRequest cap profile)
    (accepted : decodeAvailableRequest cap profile lanes layout entry answers = some request) :
    lanes = callerLanes layout := by
  have metadata : openingMatches profile lanes layout = true := by
    cases h : openingMatches profile lanes layout with
    | false =>
      simp [decodeAvailableRequest,decodeRequest_wrong_metadata cap profile lanes layout entry
        (fun q => (answers q).getD DuplexRefinement.zeroDigest) h] at accepted
    | true => rfl
  simp only [openingMatches,Bool.and_eq_true,beq_iff_eq] at metadata
  exact metadata.1.1

/-- The physical caller's decoder is the concrete registry decoder for this
publicly registered production model; no future source announcement is read. -/
theorem decoded_packetRequest (registry : Public) (Q cap lanes : Nat)
    (model : WHIRCallerSupport.ProductionLayout) (packet : Packet (context registry) Q)
    (registered : registry.layouts packet.val.statement = some model.layout)
    (trace : List Observation) (request : CausalBindingState.ClaimRequest cap packet.val.profile)
    (accepted : decodeAvailableRequest cap packet.val.profile lanes model.layout
      (RawWHIRKeys.entry (context registry) packet.val) (latestAnswers trace) = some request) :
    packetRequest registry Q cap packet (callerHistory (context registry) Q packet trace) = some request := by
  have layout : model.layout = packetLayout registry Q packet :=
    Option.some.inj (registered.symm.trans (packet_geometry registry Q packet).1)
  have lanesEq := decoded_lanes cap packet.val.profile lanes model.layout
    (RawWHIRKeys.entry (context registry) packet.val) (latestAnswers trace) request accepted
  rw [packetRequest_observations,← layout,← lanesEq]
  exact accepted

/-- Successful arithmetic completion preserves exactly the computed request,
wire state and packet-answer history supplied to `finish`. -/
theorem finish_success (ctx : Context) (Q cap : Nat) (packet : Packet ctx Q)
    (request : CausalBindingState.ClaimRequest cap packet.val.profile) (state : WireState packet.val.profile)
    (history : List (Sigma (GroupAnswer ctx Q)))
    (nativeShapes : SuccinctRingWeight.FamilyShape (ParameterBounds.config packet.val.profile).logN request.claims.family ∧
      ∀ point ∈ request.claims.points.toList, SuccinctPointWeight.Shape (ParameterBounds.config packet.val.profile).logN point)
    (claimShapes : ∀ (seed : RingPCSGame.Prefix) (lambda : E),
      let c := ParameterBounds.config packet.val.profile
      let claims := RingPCSGame.transformedClaims (2^c.logN) request.claims.family request.claims.points seed
      (claims.all (fun claim => Protocol.shapeValid c request.lanes claim.weight) = true) ∧
        Protocol.shapeValid c request.lanes (CausalGame.batchClaims (2^c.logN) claims lambda).weight = true)
    (verified : Verified ctx Q cap packet)
    (accepted : finish ctx Q cap packet request state history nativeShapes claimShapes = some verified) :
    verified.request = request ∧ verified.wire = state ∧ verified.history = history := by
  unfold finish at accepted
  split at accepted
  · cases accepted
  · dsimp only at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · cases Option.some.inj accepted
        exact ⟨rfl,rfl,rfl⟩

/-- Success in the actual source forces its initial-root read, the complete
caller query prefix, original source decoding, and the actual physical reader.
The shape witnesses below are computed from the decoder equation, not premises. -/
theorem verifySource_success (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : Context) (stack : ctx.mode = .stack) (Q lanes : Nat)
    (packet : Packet ctx Q) (proofs : Array MerkleTransport.PrunedMerklePaths)
    (trace : List Observation) (verified : Verified ctx Q cap packet)
    (run : Runs (WHIRSourceChronology.erase (verifySource cap model ctx stack Q lanes packet proofs))
      trace (some verified)) :
    ∃ (root : Digest32) (before after : List Observation) (request : CausalBindingState.ClaimRequest cap packet.val.profile),
      initialRoot model.layout (RawWHIRKeys.entry ctx packet.val) = some root ∧
      root = request.root ∧ trace = before ++ after ∧
      before.length = (WHIRModeFinal.callerPositions ctx Q packet).length ∧
      before.map Observation.query = (WHIRModeFinal.callerPositions ctx Q packet).map
        (fun q => Query.construction q.val (RawWHIRKeys.callerOutput_admissible ctx Q packet q.val q.property)) ∧
      ∃ decoded : decodeAvailableRequest cap packet.val.profile lanes model.layout
          (RawWHIRKeys.entry ctx packet.val) (latestAnswers before) = some request,
        Runs (WHIRSourceChronology.erase
          (readPhysicalPackets (cap := cap) ctx stack Q packet.val.profile request.lanes proofs none
            (completion ctx Q packet) (completion_profiles ctx Q packet)
            (initialWireState packet.val.profile root)
            (fun state history => .done (finish ctx Q cap packet request state history
              (WHIRCallerSupport.decodeAvailableRequest_nativeShapes model cap packet.val.profile lanes
                (RawWHIRKeys.entry ctx packet.val) (latestAnswers before) request decoded)
              (WHIRCallerSupport.decodeAvailableRequest_shapes model cap packet.val.profile lanes
                (RawWHIRKeys.entry ctx packet.val) (latestAnswers before) request decoded)))))
          after (some verified) := by
  unfold verifySource at run
  cases rootRead : initialRoot model.layout (RawWHIRKeys.entry ctx packet.val) with
  | none =>
    simp only [rootRead,WHIRSourceChronology.erase] at run
    cases run
  | some root =>
    simp only [rootRead,WHIRSourceChronology.erase] at run
    obtain ⟨before,after,traceEq,count,queries,continued⟩ := readCallerInputs_run ctx Q packet
      (WHIRModeFinal.callerPositions ctx Q packet) (fun _ => none) _ trace (some verified) run
    split at continued
    · cases continued
    · rename_i request decoded
      have rootEq : root = request.root := Option.some.inj (rootRead.symm.trans
        (decodeAvailableRequest_initialRoot cap packet.val.profile lanes model.layout
          (RawWHIRKeys.entry ctx packet.val) (latestAnswers before) request decoded))
      exact ⟨root,before,after,request,rfl,rootEq,traceEq,count,queries,decoded,continued⟩

/-- The concrete public resolver uses the same decoded claims, independently
of its source annotations and pre-registration state. -/
theorem publicResolver_observations {R : Type} (registry : Public) (Q cap : Nat)
    (result : WHIRSourceChronology.Result cap R) (state : CausalBindingState.State cap)
    (packet : Packet (context registry) Q) (trace : List Observation) :
    (WHIRSourceResolver.publicResolver registry Q result).claims state packet
        (callerHistory (context registry) Q packet trace) =
      decodeAvailableRequest cap packet.val.profile (callerLanes (packetLayout registry Q packet))
        (packetLayout registry Q packet) (RawWHIRKeys.entry (context registry) packet.val) (latestAnswers trace) :=
  packetRequest_observations registry Q cap packet trace

theorem privateResolver_observations {R : Type} (registry : Public) (Q cap : Nat)
    (seed : DuplexPublicSimulator.Seed) (source : WHIRSourceChronology.Source cap R)
    (counted : WHIRSourceChronology.Counts Q source) (state : CausalBindingState.State cap)
    (packet : Packet (context registry) Q) (trace : List Observation) :
    (WHIRSourceResolver.privateResolver registry Q seed source counted).claims state packet
        (callerHistory (context registry) Q packet trace) =
      decodeAvailableRequest cap packet.val.profile (callerLanes (packetLayout registry Q packet))
        (packetLayout registry Q packet) (RawWHIRKeys.entry (context registry) packet.val) (latestAnswers trace) :=
  packetRequest_observations registry Q cap packet trace

/-- Construction observations in a genuine ideal execution have their literal
raw-table values, even when arbitrary primitive simulator calls intervene. -/
theorem ideal_construction_answers {Q : Nat} {Seed State R : Type} (sim : Simulator Q Seed State)
    (table : RawKey Q → Digest32) (iv : Digest32) (state : State) (program : Program R)
    (remaining : Nat) (limit : remaining ≤ Q) (counted : DuplexModeGame.Counts remaining program) :
    ∀ observation ∈ (runIdeal sim table iv state program remaining limit counted).view.observations,
      ∀ (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate)
        (bound : DuplexFraming.pathCost coordinate ≤ Q),
      observation.query = .construction coordinate valid →
        observation.answer = table (constructionKey Q iv coordinate bound) := by
  induction program generalizing state remaining with
  | done value => simp only [runIdeal,List.not_mem_nil,false_implies,implies_true]
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      intro observation member coordinate valid bound equal
      simp only [runIdeal,DuplexModeGame.prepend,List.mem_cons] at member
      rcases member with head | member
      · subst observation
        cases equal
      · exact ih (runRO table (sim.answer state input)).1.2
          (runRO table (sim.answer state input)).1.1 (remaining-1) (by omega)
          (counted.2 _) observation member coordinate valid bound equal
    | construction query validQuery =>
      intro observation member coordinate valid bound equal
      simp only [runIdeal,DuplexModeGame.prepend,List.mem_cons] at member
      rcases member with head | member
      · subst observation
        cases equal
        rfl
      · exact ih (table (constructionKey Q iv query (counted.1.trans limit))) state
          (remaining-DuplexFraming.pathCost query) (by omega)
          (counted.2 _) observation member coordinate valid bound equal

private theorem observedAnswers_stable (trace : List Observation) (wanted : Coordinate)
    (answer : Digest32)
    (consistent : ∀ observation ∈ trace, ∀ valid,
      observation.query = .construction wanted valid → observation.answer = answer) :
    trace.foldl (observeAt wanted) (some answer) = some answer := by
  induction trace with
  | nil => rfl
  | cons observation rest ih =>
    have stable : observeAt wanted (some answer) observation = some answer := by
      cases observation with
      | mk query value =>
        cases query with
        | primitive => rfl
        | construction coordinate valid =>
          by_cases equal : wanted = coordinate
          · subst coordinate
            have valueEq : value = answer :=
              consistent ⟨.construction wanted valid,value⟩ List.mem_cons_self valid rfl
            subst value
            simp [observeAt]
          · simp only [observeAt,ite_eq_right equal]
    rw [List.foldl_cons,stable]
    exact ih (fun observation member => consistent observation (List.mem_cons_of_mem _ member))

theorem latestAnswers_consistent (trace : List Observation) (wanted : Coordinate)
    (valid : DuplexEncoding.Admissible wanted) (answer : Digest32)
    (present : ∃ observation ∈ trace, observation.query = .construction wanted valid)
    (consistent : ∀ observation ∈ trace, ∀ proof,
      observation.query = .construction wanted proof → observation.answer = answer) :
    latestAnswers trace wanted = some answer := by
  obtain ⟨observation,member,query⟩ := present
  have value := consistent observation member valid query
  obtain ⟨before,after,traceEq⟩ := List.append_of_mem member
  subst trace
  unfold latestAnswers
  rw [observedAnswers_append,observedAnswers_cons]
  change after.foldl (observeAt wanted) (observeAt wanted _ observation) = _
  have observed : observeAt wanted (observedAnswers before (fun _ => none) wanted) observation = some answer := by
    simp [observeAt,query,value]
  rw [observed]
  exact observedAnswers_stable after wanted answer
    (fun observation member => consistent observation (List.mem_append_right _ (List.mem_cons_of_mem _ member)))

/-- The source-owned ideal prefix gives all and only the earlier caller table
answers needed by the production decoder. The full source's future observations
are used only to prove consistency of this already-fixed finite prefix. -/
theorem ideal_caller_prefix {Q cap : Nat} {Seed State R : Type}
    (ctx : Context) (packet : Packet ctx Q) (sim : Simulator Q Seed State)
    (table : RawKey Q → Digest32) (state : State)
    (source : WHIRSourceChronology.Source cap R) (remaining : Nat) (limit : remaining ≤ Q)
    (counted : WHIRSourceChronology.Counts remaining source)
    (before after : List Observation)
    (sourcePrefix : WHIRSourceChronology.observations
      (runIdeal sim table ctx.iv state (WHIRSourceChronology.compile source) remaining limit
        ((WHIRSourceChronology.compile_counted source remaining).mpr counted)).view.result.events = before ++ after)
    (queries : before.map Observation.query = (WHIRModeFinal.callerPositions ctx Q packet).map
      (fun q => Query.construction q.val (RawWHIRKeys.callerOutput_admissible ctx Q packet q.val q.property))) :
    ∀ wanted ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val),
      latestAnswers before wanted = tableCallerAnswers ctx Q packet table wanted := by
  intro wanted prior
  have queried : Query.construction wanted (RawWHIRKeys.callerOutput_admissible ctx Q packet wanted prior) ∈
      before.map Observation.query := by
    rw [queries]
    exact List.mem_map.mpr ⟨⟨wanted,prior⟩,List.mem_attach _ _,rfl⟩
  obtain ⟨observation,member,equal⟩ := List.mem_map.mp queried
  simp only [tableCallerAnswers,dite_eq_left prior]
  apply latestAnswers_consistent before wanted
    (RawWHIRKeys.callerOutput_admissible ctx Q packet wanted prior) _
    ⟨observation,member,equal⟩
  intro observation member valid equal
  have inRun : observation ∈
      (runIdeal sim table ctx.iv state (WHIRSourceChronology.compile source) remaining limit
        ((WHIRSourceChronology.compile_counted source remaining).mpr counted)).view.observations := by
    rw [← WHIRSourceResolver.ideal_source_trace sim table ctx.iv state source remaining limit counted,sourcePrefix]
    exact List.mem_append_left _ member
  exact ideal_construction_answers sim table ctx.iv state (WHIRSourceChronology.compile source) remaining limit
    ((WHIRSourceChronology.compile_counted source remaining).mpr counted) observation inRun wanted valid
    (RawWHIRKeys.callerOutput_pathBound ctx Q packet wanted prior) equal

/-- The *actual allocation compiler dependency history*, including early raw
prequeries before source claim announcements, decodes the same request as the
actual caller's source-owned prefix. Both provenances are obtained from their
executions against the same immutable table, not assumed decoder agreement. -/
theorem packetRequest_compiled_prefix {R S Seed State : Type} {K : Nat}
    (registry : Public) (Q cap : Nat) (packet : Packet (context registry) Q)
    (final : R → Option (Packet (context registry) Q))
    (program : TypedOracleCompiler.Sampling (RawKey Q) (fun _ => Digest32) R K)
    (table : RawKey Q → Digest32) (allocation : Sigma (AllocationAnswer (context registry) Q))
    (member : allocation ∈ (TypedOracleCompiler.Sampling.execute
      (WHIRObservableAllocations.allocationOracle (context registry) Q table)
      (RawOracleCoupling.Concrete.compile (context registry) Q final program)).2)
    (key : allocation.1.1 = .inl packet)
    (sim : Simulator Q Seed State) (state : State) (source : WHIRSourceChronology.Source cap S)
    (remaining : Nat) (limit : remaining ≤ Q) (counted : WHIRSourceChronology.Counts remaining source)
    (before after : List Observation)
    (sourcePrefix : WHIRSourceChronology.observations
      (runIdeal sim table (context registry).iv state (WHIRSourceChronology.compile source) remaining limit
        ((WHIRSourceChronology.compile_counted source remaining).mpr counted)).view.result.events = before ++ after)
    (queries : before.map Observation.query = (WHIRModeFinal.callerPositions (context registry) Q packet).map
      (fun q => Query.construction q.val (RawWHIRKeys.callerOutput_admissible (context registry) Q packet q.val q.property))) :
    packetRequest registry Q cap packet allocation.1.2 =
      decodeAvailableRequest cap packet.val.profile (callerLanes (packetLayout registry Q packet))
        (packetLayout registry Q packet) (RawWHIRKeys.entry (context registry) packet.val) (latestAnswers before) := by
  rw [packetRequest_table_compile registry Q cap final program table allocation member packet key]
  apply decodeAvailableRequest_prior_only
  intro wanted prior
  exact (ideal_caller_prefix (context registry) packet sim table state source remaining limit counted
    before after sourcePrefix queries wanted prior).symm

end Whir.WHIRPhysicalCaller
