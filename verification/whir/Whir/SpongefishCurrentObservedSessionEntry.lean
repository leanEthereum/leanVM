import Whir.SpongefishCurrentPrimitiveEventCompiler

/-! Ordinary-source initialized session entry for current #607 at
75d4562bde1efe296b4e32d2a195fdfc232b3ead. SessionId derivation, the literal
session/zero32 seed, instance absorption, and every reached replay call share
one observed primitive interaction. No live CV, session ID, successful replay,
or mode-equivalence certificate is an input.

The Rust constructor panics on empty instance bytes. Here `none` denotes an
invalid constructor input; correspondence to its ordinary initialized state is
claimed only for nonempty instance bytes, not as Rust panic/error equality.
This is an executable mathematical hand-port, not Aeneas equivalence, the
current mixed-mode compiler, or a whole deployed Fiat-Shamir knowledge claim.
-/
namespace Whir.SpongefishCurrentObservedSessionEntry
open FiatShamirGame Concrete DuplexRefinement DuplexModeGame
open SpongefishSessionAdapter SpongefishOrdinarySession SpongefishPCSRoundFrames
open SpongefishCurrentPrimitiveEventCompiler
set_option autoImplicit false

/-- The seed CV is the observed answer to the literal native initialization node. -/
def initProgram (parameter session : Digest32) : Program State :=
  seq (primitive parameter (ByteCodec.pairBytes (session,zeroDigest))
    (UInt64.ofNat (2^56)) true) (fun cv => .done {cv := cv})

@[simp] theorem initProgram_real (C : PrimitiveOracle) (iv parameter session : Digest32) :
    (runReal C iv (initProgram parameter session)).view.result =
      init (compressionOf C) parameter session := by
  simp [initProgram,seq,WHIRModeFinal.bind_real_result,runReal,init,seed]

theorem initProgram_certified (parameter session : Digest32) :
    Counts 1 (initProgram parameter session) ∧ OnlyPrimitive (initProgram parameter session) :=
  ⟨seq_done_counted _ _ (primitive_certified _ _ _ _).1,
    onlyPrimitive_seq _ _ (primitive_certified _ _ _ _).2 (fun _ => trivial)⟩

/-- Public instance absorption is recorded separately from proof-transport reads.
The counters start at zero; neither narg nor hints are consumed at construction. -/
def cursor (session : Digest32) (instanceBytes narg : List Byte)
    (hints : List (List Byte)) (s : State) : Cursor :=
  {state := s, pending := bind {domain := session} instanceBytes,
   narg := narg, hints := hints, events := [.publicBytes instanceBytes]}

/-- Continuation from an actually derived ID; no caller supplies the session seed. -/
def sessionProgram (parameter session : Digest32) (instanceBytes narg : List Byte)
    (hints : List (List Byte)) : Program Cursor :=
  seq (initProgram parameter session) (fun s =>
    seq (absorbProgram s instanceBytes) (fun t =>
      .done (cursor session instanceBytes narg hints t)))

@[simp] theorem sessionProgram_real (C : PrimitiveOracle) (iv parameter session : Digest32)
    (instanceBytes narg : List Byte) (hints : List (List Byte)) :
    (runReal C iv (sessionProgram parameter session instanceBytes narg hints)).view.result =
      cursor session instanceBytes narg hints
        (absorb (compressionOf C) (init (compressionOf C) parameter session) instanceBytes) := by
  simp [sessionProgram,seq,WHIRModeFinal.bind_real_result,runReal]

/-- Empty instance bytes are outside the source constructor's valid input domain. -/
def setupProgram (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) : Program (Option Cursor) :=
  if instanceBytes = [] then .done none else
    afterDerive parameter tag (fun session =>
      seq (sessionProgram parameter session instanceBytes narg hints) (fun cur => .done (some cur)))

/-- Reference construction uses the existing derive/init/newSession adapters. -/
def actualSetup (c : Compression) (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) : Option Cursor :=
  let session := derive c parameter tag
  (newSession c parameter session instanceBytes).map (cursor session instanceBytes narg hints)

/-- The reference adapter bypasses runReal. Share its derived session across
the initialization node and pending-frame domain at the Option boundary.
The existing constructor guard still rejects before any derived work. -/
private def actualSetupStored (c : Compression) (parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) : Option Cursor :=
  if instanceBytes = [] then none else
    withDerived c parameter tag (fun session =>
      (newSession c parameter session instanceBytes).map (cursor session instanceBytes narg hints))

@[csimp] private theorem actualSetup_stored : actualSetup = actualSetupStored := by
  funext c parameter tag instanceBytes narg hints
  simp only [actualSetup,actualSetupStored,withDerived_eq]
  by_cases empty : instanceBytes = [] <;> simp [newSession,empty]

@[simp] theorem setupProgram_real (C : PrimitiveOracle) (iv parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) :
    (runReal C iv (setupProgram parameter tag instanceBytes narg hints)).view.result =
      actualSetup (compressionOf C) parameter tag instanceBytes narg hints := by
  by_cases empty : instanceBytes = []
  · simp [setupProgram,actualSetup,newSession,empty,runReal]
  · simp [setupProgram,actualSetup,newSession,empty,afterDerive_real,
      seq,WHIRModeFinal.bind_real_result,runReal]

/-- Valid-input source correspondence; the session and every CV are computed. -/
theorem setupProgram_nonempty (C : PrimitiveOracle) (iv parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (nonempty : instanceBytes ≠ []) :
    (runReal C iv (setupProgram parameter tag instanceBytes narg hints)).view.result =
      some (cursor (derive (compressionOf C) parameter tag) instanceBytes narg hints
        (absorb (compressionOf C)
          (init (compressionOf C) parameter (derive (compressionOf C) parameter tag)) instanceBytes)) := by
  rw [setupProgram_real]
  simp [actualSetup,newSession_nonempty _ _ _ _ nonempty]

theorem setupProgram_empty (parameter : Digest32) (tag narg : List Byte)
    (hints : List (List Byte)) : setupProgram parameter tag [] narg hints = .done none := by
  simp [setupProgram]

/-- The initialized current frame relation is derived internally, not assumed. -/
theorem setupProgram_bridge (C : PrimitiveOracle) (iv parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (nonempty : instanceBytes ≠ []) :
    ∃ cur, (runReal C iv (setupProgram parameter tag instanceBytes narg hints)).view.result = some cur ∧
      RepresentsCurrent (compressionOf C) parameter cur.pending cur.state := by
  refine ⟨_,setupProgram_nonempty C iv parameter tag instanceBytes narg hints nonempty,?_⟩
  exact session_bridge (compressionOf C) parameter _ instanceBytes

/-- Invalid construction and rejected replay are distinct result boundaries.
A replay error retains the entire actually reached cursor. -/
def entryProgram (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (calls : List Call) : Program (Option ReplayResult) :=
  seq (setupProgram parameter tag instanceBytes narg hints) (fun result => match result with
    | none => .done none
    | some cur => seq (replayProgram cur calls) (fun result => .done (some result)))

def actualEntry (c : Compression) (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (calls : List Call) : Option ReplayResult :=
  (actualSetup c parameter tag instanceBytes narg hints).map (fun cur => actualReplay c cur calls)

@[simp] theorem entryProgram_real (C : PrimitiveOracle) (iv parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (calls : List Call) :
    (runReal C iv (entryProgram parameter tag instanceBytes narg hints calls)).view.result =
      actualEntry (compressionOf C) parameter tag instanceBytes narg hints calls := by
  simp only [entryProgram,seq,WHIRModeFinal.bind_real_result,setupProgram_real,actualEntry]
  cases actualSetup (compressionOf C) parameter tag instanceBytes narg hints <;>
    simp [WHIRModeFinal.bind_real_result,runReal]

/-- Erasure agrees with the source adapter on both accepted and rejected replay. -/
theorem entryProgram_source (C : PrimitiveOracle) (iv parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (calls : List Call) :
    ((runReal C iv (entryProgram parameter tag instanceBytes narg hints calls)).view.result.bind erase) =
      (actualSetup (compressionOf C) parameter tag instanceBytes narg hints).bind
        (fun cur => replayCalls (compressionOf C) cur calls) := by
  rw [entryProgram_real]
  unfold actualEntry
  cases actualSetup (compressionOf C) parameter tag instanceBytes narg hints <;>
    simp [actualReplay_erases]

/-- Every reply-dependent continuation is charged, not just successful replay. -/
def setupBudget (tag instanceBytes : List Byte) : Nat :=
  derivationPrimitiveCost tag + (1 + instanceBytes.length)

def entryBudget (tag instanceBytes : List Byte) (calls : List Call) : Nat :=
  setupBudget tag instanceBytes + sourceBudget calls

theorem instructions_onlyPrimitive (cv : Digest32) (xs : List DuplexEncoding.Instruction) :
    OnlyPrimitive (instructions cv xs) := by
  induction xs generalizing cv with
  | nil => trivial
  | cons i rest ih => exact ⟨⟨_,rfl⟩,fun answer => ih answer⟩

theorem sessionProgram_certified (parameter session : Digest32) (instanceBytes narg : List Byte)
    (hints : List (List Byte)) :
    Counts (1+instanceBytes.length) (sessionProgram parameter session instanceBytes narg hints) ∧
      OnlyPrimitive (sessionProgram parameter session instanceBytes narg hints) := by
  refine ⟨WHIRModeFinal.bind_counted _ _ 1 instanceBytes.length
    (initProgram_certified parameter session).1 (fun s =>
      seq_done_counted _ _ (absorbProgram_certified s instanceBytes).1),?_⟩
  exact onlyPrimitive_seq _ _ (initProgram_certified parameter session).2 (fun s =>
    onlyPrimitive_seq _ _ (absorbProgram_certified s instanceBytes).2 (fun _ => trivial))

theorem setupProgram_certified (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) :
    Counts (setupBudget tag instanceBytes) (setupProgram parameter tag instanceBytes narg hints) ∧
      OnlyPrimitive (setupProgram parameter tag instanceBytes narg hints) := by
  unfold setupProgram
  split
  · exact ⟨trivial,trivial⟩
  · refine ⟨afterDerive_counted parameter tag _ (1+instanceBytes.length) (fun session =>
      seq_done_counted _ _ (sessionProgram_certified parameter session instanceBytes narg hints).1),?_⟩
    exact onlyPrimitive_seq _ _ (instructions_onlyPrimitive parameter (derivationPlan tag)) (fun session =>
      onlyPrimitive_seq _ _ (sessionProgram_certified parameter session instanceBytes narg hints).2
        (fun _ => trivial))

theorem entryProgram_certified (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (calls : List Call) :
    Counts (entryBudget tag instanceBytes calls) (entryProgram parameter tag instanceBytes narg hints calls) ∧
      OnlyPrimitive (entryProgram parameter tag instanceBytes narg hints calls) := by
  refine ⟨WHIRModeFinal.bind_counted _ _ (setupBudget tag instanceBytes) (sourceBudget calls)
    (setupProgram_certified parameter tag instanceBytes narg hints).1 (fun result => ?_),
    onlyPrimitive_seq _ _ (setupProgram_certified parameter tag instanceBytes narg hints).2
      (fun result => ?_)⟩
  · cases result with
    | none => trivial
    | some cur => exact seq_done_counted _ _ (replayProgram_certified cur calls).1
  · cases result with
    | none => trivial
    | some cur => exact onlyPrimitive_seq _ _ (replayProgram_certified cur calls).2 (fun _ => trivial)

theorem entryBudget_closed (tag instanceBytes : List Byte) (calls : List Call) :
    entryBudget tag instanceBytes calls =
      3 + (tag.length+63)/64 + instanceBytes.length + sourceBudget calls := by
  unfold entryBudget setupBudget
  rw [derivation_cost_closed]
  omega

/-- Repeated nodes remain repeated observations, even for a cached oracle answer. -/
def instructionsTrace (C : PrimitiveOracle) : Digest32 → List DuplexEncoding.Instruction → List Observation
  | _, [] => []
  | cv, i :: rest => record C ⟨cv,i.1,i.2,true⟩ ++ instructionsTrace C (C ⟨cv,i.1,i.2,true⟩) rest

theorem instructions_trace (C : PrimitiveOracle) (iv cv : Digest32)
    (xs : List DuplexEncoding.Instruction) :
    (runReal C iv (instructions cv xs)).view.observations = instructionsTrace C cv xs := by
  induction xs generalizing cv with
  | nil => rfl
  | cons i rest ih =>
    simpa only [instructions,runReal,realAnswer,prepend,instructionsTrace,record,List.singleton_append]
      using congrArg (Observation.mk (.primitive .auxiliary ⟨cv,i.1,i.2,true⟩)
        (C ⟨cv,i.1,i.2,true⟩) :: ·) (ih (C ⟨cv,i.1,i.2,true⟩))

def sessionTrace (C : PrimitiveOracle) (parameter session : Digest32)
    (instanceBytes : List Byte) : List Observation :=
  record C ⟨parameter,ByteCodec.pairBytes (session,zeroDigest),UInt64.ofNat (2^56),true⟩ ++
    absorbTrace C (init (compressionOf C) parameter session) instanceBytes

theorem initProgram_trace (C : PrimitiveOracle) (iv parameter session : Digest32) :
    (runReal C iv (initProgram parameter session)).view.observations =
      record C ⟨parameter,ByteCodec.pairBytes (session,zeroDigest),UInt64.ofNat (2^56),true⟩ := rfl

theorem sessionProgram_trace (C : PrimitiveOracle) (iv parameter session : Digest32)
    (instanceBytes narg : List Byte) (hints : List (List Byte)) :
    (runReal C iv (sessionProgram parameter session instanceBytes narg hints)).view.observations =
      sessionTrace C parameter session instanceBytes := by
  simp only [sessionProgram,seq_observations,initProgram_trace,initProgram_real,
    absorbProgram_trace,runReal,List.append_nil,sessionTrace]

def setupTrace (C : PrimitiveOracle) (parameter : Digest32) (tag instanceBytes : List Byte) :
    List Observation :=
  if instanceBytes = [] then [] else
    instructionsTrace C parameter (derivationPlan tag) ++
      sessionTrace C parameter (derive (compressionOf C) parameter tag) instanceBytes

theorem setupProgram_trace (C : PrimitiveOracle) (iv parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) :
    (runReal C iv (setupProgram parameter tag instanceBytes narg hints)).view.observations =
      setupTrace C parameter tag instanceBytes := by
  unfold setupProgram setupTrace
  split
  · rfl
  · simp only [afterDerive,seq_observations,deriveProgram_real,
      sessionProgram_trace,runReal,List.append_nil]
    rw [deriveProgram,instructions_trace]

def entryTrace (C : PrimitiveOracle) (parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (calls : List Call) : List Observation :=
  setupTrace C parameter tag instanceBytes ++
    match actualSetup (compressionOf C) parameter tag instanceBytes narg hints with
    | none => [] | some cur => replayTrace C cur calls

theorem entryProgram_trace (C : PrimitiveOracle) (iv parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (calls : List Call) :
    (runReal C iv (entryProgram parameter tag instanceBytes narg hints calls)).view.observations =
      entryTrace C parameter tag instanceBytes narg hints calls := by
  simp only [entryProgram,seq_observations,setupProgram_trace,setupProgram_real,entryTrace]
  cases actualSetup (compressionOf C) parameter tag instanceBytes narg hints <;>
    simp only [seq_observations,replayProgram_trace,runReal,List.append_nil]

/-- Reference provenance adapters replay one metered execution rather than
computing a separate reply chain beside each stored observation. -/
private def instructionsTraceStored (C : PrimitiveOracle) (cv : Digest32)
    (xs : List DuplexEncoding.Instruction) : List Observation :=
  (runReal C zeroDigest (instructions cv xs)).view.observations

@[csimp] private theorem instructionsTrace_stored : instructionsTrace = instructionsTraceStored := by
  funext C cv xs
  exact (instructions_trace C zeroDigest cv xs).symm

private def sessionTraceStored (C : PrimitiveOracle) (parameter session : Digest32)
    (instanceBytes : List Byte) : List Observation :=
  (runReal C zeroDigest (sessionProgram parameter session instanceBytes [] [])).view.observations

@[csimp] private theorem sessionTrace_stored : sessionTrace = sessionTraceStored := by
  funext C parameter session instanceBytes
  exact (sessionProgram_trace C zeroDigest parameter session instanceBytes [] []).symm

private def setupTraceStored (C : PrimitiveOracle) (parameter : Digest32)
    (tag instanceBytes : List Byte) : List Observation :=
  (runReal C zeroDigest (setupProgram parameter tag instanceBytes [] [])).view.observations

@[csimp] private theorem setupTrace_stored : setupTrace = setupTraceStored := by
  funext C parameter tag instanceBytes
  exact (setupProgram_trace C zeroDigest parameter tag instanceBytes [] []).symm

private def entryTraceStored (C : PrimitiveOracle) (parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (calls : List Call) :
    List Observation :=
  (runReal C zeroDigest (entryProgram parameter tag instanceBytes narg hints calls)).view.observations

@[csimp] private theorem entryTrace_stored : entryTrace = entryTraceStored := by
  funext C parameter tag instanceBytes narg hints calls
  exact (entryProgram_trace C zeroDigest parameter tag instanceBytes narg hints calls).symm

theorem setupProgram_observation_count (C : PrimitiveOracle) (iv parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (nonempty : instanceBytes ≠ []) :
    (runReal C iv (setupProgram parameter tag instanceBytes narg hints)).view.observations.length =
      3 + (tag.length+63)/64 +
        (absorbTrace C (init (compressionOf C) parameter (derive (compressionOf C) parameter tag))
          instanceBytes).length := by
  rw [setupProgram_trace]
  simp only [setupTrace,nonempty,↓reduceIte,sessionTrace,List.length_append,record,
    List.length_cons,List.length_nil]
  rw [← instructions_trace C iv,← deriveProgram,deriveProgram_observation_count]
  omega

/-- Exact reached trace/cost and a worst-case bound including all calls, with no
success or externally supplied counting premise. -/
theorem entryProgram_observed_work (C : PrimitiveOracle) (iv parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (calls : List Call) :
    (∀ o ∈ (runReal C iv (entryProgram parameter tag instanceBytes narg hints calls)).view.observations,
      ∃ n, o.query = .primitive .auxiliary n ∧ o.answer = C n) ∧
    (runReal C iv (entryProgram parameter tag instanceBytes narg hints calls)).primitiveCost =
      (entryTrace C parameter tag instanceBytes narg hints calls).length ∧
    (runReal C iv (entryProgram parameter tag instanceBytes narg hints calls)).primitiveCost ≤
      entryBudget tag instanceBytes calls := by
  have provenance := observed_provenance C iv _
    (entryProgram_certified parameter tag instanceBytes narg hints calls).2
  refine ⟨provenance.1,?_,runReal_counts C iv _ _
    (entryProgram_certified parameter tag instanceBytes narg hints calls).1⟩
  rw [← entryProgram_trace]
  exact provenance.2.symm

/-- Existing executable public-compression backend; its Counts proof is internal. -/
def compiledEntry (iv parameter : Digest32) (tag instanceBytes narg : List Byte)
    (hints : List (List Byte)) (calls : List Call) :
    PublicCompressionProgram.Computation (Execution (Option ReplayResult)) (entryBudget tag instanceBytes calls) :=
  PublicCompressionProgram.compile iv (entryProgram parameter tag instanceBytes narg hints calls)
    (entryBudget tag instanceBytes calls) (entryProgram_certified parameter tag instanceBytes narg hints calls).1

theorem compiledEntry_real (C : PrimitiveOracle) (iv parameter : Digest32)
    (tag instanceBytes narg : List Byte) (hints : List (List Byte)) (calls : List Call) :
    TypedOracleCompiler.Sampling.eval C (compiledEntry iv parameter tag instanceBytes narg hints calls) =
      runReal C iv (entryProgram parameter tag instanceBytes narg hints calls) :=
  PublicCompressionProgram.compile_eval C iv _ _ _

#print axioms actualSetup_stored
#print axioms instructionsTrace_stored
#print axioms sessionTrace_stored
#print axioms setupTrace_stored
#print axioms entryTrace_stored
#print axioms initProgram_real
#print axioms setupProgram_nonempty
#print axioms setupProgram_bridge
#print axioms entryProgram_real
#print axioms entryProgram_source
#print axioms entryProgram_certified
#print axioms setupProgram_trace
#print axioms setupProgram_observation_count
#print axioms entryProgram_trace
#print axioms entryProgram_observed_work
#print axioms compiledEntry_real
end Whir.SpongefishCurrentObservedSessionEntry
