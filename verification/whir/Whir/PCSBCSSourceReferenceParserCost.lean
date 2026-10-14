import Whir.PCSBCSPublicLogParserCost
import Whir.PCSBCSCallerPayloadCost

/-! Actual scheduled opening-role parser instrumentation. Charges include
public schedule construction/indexing, scalar encoding, ghost-model framing,
whole-history equality and every checked phase role. No parser cost oracle is
an input. CpuLayout.output remains an explicitly costed metadata getter. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceReferenceParserCost
open Concrete Protocol FiatShamirGame DuplexRefinement WHIRHistory WHIRHistoryKey
open WHIRCallerClaims PCSBCSSourceRootReferences PCSBCSPublicLogParserCost

local instance : DecidableEq Terminal := by
  intro a b
  cases a <;> cases b <;> simp <;> infer_instance
local instance : DecidableEq Coordinate := by
  intro a b
  cases a
  cases b
  simp only [Coordinate.mk.injEq]
  infer_instance

/-- The schedule is finite public geometry. List constructors, all per-phase
array reads, both fold sums and the invisible tail are included. This volume
charge deliberately includes failed indices, not only accepted coordinates. -/
def scheduleWork (c : Config) : Nat :=
  32*(c.folds.size+(schedule c).length+c.logN+1)

def scalarCountWork (c : Config) : Nat := 32*(c.folds.size+c.logN+1)

def stackWidthCount (c : Config) (n : Nat) : Nat × Nat :=
  (stackWidth c n,scheduleWork c+min n (schedule c).length+scalarCountWork c+8)

/-- The protocol recurrence materializes scalar bytes, not a hash. -/
def pendingModelCount (m : Model) (p : Pending) : Model × Nat :=
  let bytes := scalarBytes p.scalars
  let absorbed := operationCount m (.absorb bytes)
  match p.nonce with
  | none => (absorbed.1,absorbed.2+900*p.scalars.length+2)
  | some (bits,nonce) =>
    let ground := operationCount absorbed.1 (.nonce bits (ByteCodec.encodeE nonce))
    (ground.1,absorbed.2+ground.2+900*(p.scalars.length+1)+2)

theorem pendingModelCount_value (m : Model) (p : Pending) :
    (pendingModelCount m p).1 = pendingModel m p := by
  simp only [pendingModelCount,pendingModel,operationCount_value,WHIRCallerShape.applyOperation]
  cases p.nonce <;> rfl

def completedModelCount (c : Config) (domain statement : Digest32) : List Pending → Model × Nat
  | [] => (⟨⟨domain,statement,[]⟩,[],0,0⟩,1)
  | p::ps =>
    let previous := completedModelCount c domain statement ps
    let absorbed := pendingModelCount previous.1 p
    let width := stackWidthCount c ps.length
    let output := operationCount absorbed.1 (.squeeze width.1)
    (output.1,previous.2+absorbed.2+width.2+output.2+ps.length+4)

theorem completedModelCount_value (c : Config) (domain statement : Digest32) (ps : List Pending) :
    (completedModelCount c domain statement ps).1 = completedModel (stackWidth c) domain statement ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [completedModelCount,completedModel,operationCount_value,
      WHIRCallerShape.applyOperation,pendingModelCount_value,ih,stackWidthCount]

def beforeModelCount (c : Config) (domain statement : Digest32) : List Pending → Model × Nat
  | [] => completedModelCount c domain statement []
  | p::ps =>
    let previous := completedModelCount c domain statement ps
    let absorbed := pendingModelCount previous.1 p
    (absorbed.1,previous.2+absorbed.2+1)

theorem beforeModelCount_value (c : Config) (domain statement : Digest32) (ps : List Pending) :
    (beforeModelCount c domain statement ps).1 = beforeModel (stackWidth c) domain statement ps := by
  cases ps <;> simp only [beforeModelCount,beforeModel,completedModelCount_value,pendingModelCount_value]

def outputKeyCount (c : Config) (entry : FramedHistory) (ps : List Pending) (block : Nat) : Coordinate × Nat :=
  let before := beforeModelCount c entry.domain entry.statement ps
  let prefixed := WHIRCallerPrefix.prepend entry.frames before.1
  let closed := closeRunCount prefixed
  (⟨closed.1.history,.output block⟩,before.2+closed.2+entry.frames.length+4)

theorem outputKeyCount_value (c : Config) (entry : FramedHistory) (ps : List Pending) (block : Nat) :
    (outputKeyCount c entry ps block).1 = WHIRCallerPrefix.outputKeyFrom (stackWidth c) entry ps block := by
  simp only [outputKeyCount,WHIRCallerPrefix.outputKeyFrom,WHIRCallerPrefix.beforeModelFrom,
    closeRunCount_value,beforeModelCount_value]

/-- Reverse/zipIdx, two schedule constructions per visited position, two list
indices, scalar-list length, reply geometry and nonce checks. A full stopping-
prefix reservation is charged even if Bool.all rejects an earlier position. -/
def scheduleGuardWork (c : Config) (messages : List Pending) : Nat :=
  messages.length*(2*scheduleWork c+2*(schedule c).length+scalarCountWork c+32)+
    ((messages.map (fun m => m.scalars.length)).sum)+4*messages.length+scheduleWork c+8

/-- Both the root-pair scalar codec and the complete phase-position lookup are
included, along with reverse/zip/filter/all list construction. -/
def phaseWork (c : Config) (messages : List Pending) : Nat :=
  messages.length*(2*scheduleWork c+2*(schedule c).length+scalarCountWork c+4096)+
    2*((messages.map (fun m => m.scalars.length)).sum)+8*messages.length+8

/-- The complete literal output key, including the initial unabsorbed Pending,
is reconstructed once and checked against all framed input bytes. -/
def parsePendingKeyCount (p : ParameterBounds.Profile) (entry : FramedHistory) (key : Coordinate) :
    Option (List Pending) × Nat :=
  let steps := parseStepsCount (key.history.frames.drop entry.frames.length)
  match steps.1 with
  | none => (none,steps.2+entry.frames.length+min entry.frames.length key.history.frames.length+2)
  | some chronological =>
    let messages := chronological.reverse++[initialPending]
    match key.terminal with
    | .output block =>
      let rebuilt := outputKeyCount (ParameterBounds.config p) entry messages block
      (if scheduledAdmissible (ParameterBounds.config p) messages = true ∧ key = rebuilt.1
        then some messages else none,
        steps.2+entry.frames.length+min entry.frames.length key.history.frames.length+
          3*chronological.length+scheduleGuardWork (ParameterBounds.config p) messages+
          rebuilt.2+coordinateEqWork key rebuilt.1+4)
    | _ => (none,steps.2+entry.frames.length+min entry.frames.length key.history.frames.length+3*chronological.length+4)

theorem parsePendingKeyCount_value (p : ParameterBounds.Profile) (entry : FramedHistory) (key : Coordinate) :
    (parsePendingKeyCount p entry key).1 = parsePendingKey p entry key := by
  simp only [parsePendingKeyCount,parsePendingKey,parseStepsCount_value]
  cases parseSteps (key.history.frames.drop entry.frames.length) with
  | none => rfl
  | some chronological =>
    cases key.terminal <;> simp only [outputKeyCount_value] <;> rfl

/-- Exactly the ascending, short-circuit finite validity getter loop. Costs
are per evaluation of Context.pending, not part of savedAt materialization. -/
def pendingValidityCount (context : AnchoredHeaderCodec.Context)
    (cost : PCSBCSCallerPayloadCost.OutputCosts) : List (Fin 8) → Bool × List (Fin 8) × Nat
  | [] => (true,[],1)
  | i::is =>
    let ok := (context.pending i).isSome == decide (i.val < (context.pendingBytes+7)/8)
    if ok then
      let later := pendingValidityCount context cost is
      (later.1,i::later.2.1,cost.pending i+later.2.2+8)
    else (false,[i],cost.pending i+8)

theorem pendingValidityCount_value (context : AnchoredHeaderCodec.Context)
    (cost : PCSBCSCallerPayloadCost.OutputCosts) (indices : List (Fin 8)) :
    (pendingValidityCount context cost indices).1 =
      indices.all (fun i => (context.pending i).isSome ==
        decide (i.val < (context.pendingBytes+7)/8)) := by
  induction indices with
  | nil => rfl
  | cons i is ih =>
    simp only [pendingValidityCount,List.all_cons]
    split <;> simp_all

/-- The trace records the actual reached indices and is independent of prices. -/
theorem pendingValidityCount_trace (context : AnchoredHeaderCodec.Context)
    (a b : PCSBCSCallerPayloadCost.OutputCosts) (indices : List (Fin 8)) :
    (pendingValidityCount context a indices).2.1 =
      (pendingValidityCount context b indices).2.1 := by
  induction indices with
  | nil => rfl
  | cons i is ih =>
    simp only [pendingValidityCount]
    split <;> simp_all

theorem pendingValidityCount_price_exact (context : AnchoredHeaderCodec.Context)
    (cost : PCSBCSCallerPayloadCost.OutputCosts) (indices : List (Fin 8)) :
    (pendingValidityCount context cost indices).2.2 =
      (pendingValidityCount context PCSBCSCallerPayloadCost.OutputCosts.zero indices).2.2+
        (((pendingValidityCount context cost indices).2.1).map cost.pending).sum := by
  induction indices with
  | nil => rfl
  | cons i is ih =>
    simp only [pendingValidityCount]
    split
    · dsimp only
      simp only [List.map_cons,List.sum_cons,PCSBCSCallerPayloadCost.OutputCosts.zero] at ih ⊢
      omega
    · simp [PCSBCSCallerPayloadCost.OutputCosts.zero,Nat.add_comm]

def recordValidityCount (saved : AnchoredHeaderCodec.Record)
    (cost : PCSBCSCallerPayloadCost.OutputCosts) : Bool × List (Fin 8) × Nat :=
  if saved.shape.Valid then
    if saved.context.pendingBytes ≤ 64 then
      let slots := pendingValidityCount saved.context cost (List.ofFn (fun i : Fin 8 => i))
      (slots.1 && decide (saved.point.length = saved.shape.logN),
        slots.2.1,slots.2.2+saved.point.length+PCSBCSCallerPayloadCost.shapeValidWork saved.shape+8)
    else (false,[],PCSBCSCallerPayloadCost.shapeValidWork saved.shape+4)
  else (false,[],PCSBCSCallerPayloadCost.shapeValidWork saved.shape+2)

theorem recordValidityCount_value (saved : AnchoredHeaderCodec.Record)
    (cost : PCSBCSCallerPayloadCost.OutputCosts) :
    (recordValidityCount saved cost).1 = true ↔ saved.Valid := by
  unfold recordValidityCount AnchoredHeaderCodec.Record.Valid AnchoredHeaderCodec.Context.Valid
  split
  · split
    · simp only [pendingValidityCount_value,Bool.and_eq_true,decide_eq_true_eq,
        List.all_eq_true,List.forall_mem_ofFn_iff]
      simp_all
    · simp_all
  · simp_all

/-- Counted caller+scheduled source parser. Opening guards and fixed-size saved
record validation are charged explicitly; failed captures return none, never
an authenticated default word. -/
def parseReferencesCount (p : ParameterBounds.Profile) (layout : CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory) (answers : Coordinate → Digest32)
    (key : Coordinate) (outputCosts : PCSBCSCallerPayloadCost.OutputCosts) :
    Option (List Reference) × Nat × Nat :=
  let valid := recordValidityCount saved outputCosts
  if valid.1 = true ∧ profileShape p saved.shape then
    let tokens := PCSBCSPublicLogParserCost.entryTokensCount entry answers
    match tokens.1 with
    | none => (none,tokens.2.1,tokens.2.2+valid.2.2+128)
    | some ts =>
      let caller := PCSBCSCallerPayloadCost.freshInterpret layout saved outputCosts ts
      match caller.value with
      | none => (none,tokens.2.1,tokens.2.2+caller.work+valid.2.2+128)
      | some _ =>
        let pending := parsePendingKeyCount p entry key
        match pending.1 with
        | none => (none,tokens.2.1,tokens.2.2+caller.work+pending.2+valid.2.2+128)
        | some messages =>
          (if phaseRolesAdmitted (ParameterBounds.config p) messages then
            some (⟨saved.root,initialShape saved.shape⟩::phaseReferences (ParameterBounds.config p) messages)
          else none,
            tokens.2.1,tokens.2.2+caller.work+pending.2+phaseWork (ParameterBounds.config p) messages+valid.2.2+128)
  else (none,0,valid.2.2+128)

theorem parseReferencesCount_value (p : ParameterBounds.Profile) (layout : CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory) (answers : Coordinate → Digest32)
    (key : Coordinate) (outputCosts : PCSBCSCallerPayloadCost.OutputCosts) :
    (parseReferencesCount p layout saved entry answers key outputCosts).1 =
      parseReferences p layout saved entry answers key := by
  simp only [parseReferencesCount,parseReferences,recordValidityCount_value]
  split
  · simp only [PCSBCSPublicLogParserCost.entryTokensCount_value,AnchoredSourceFreshCaller.decode]
    cases WHIRCallerClaims.entryTokens entry answers with
    | none => rfl
    | some tokens =>
      dsimp only [Bind.bind,Option.bind]
      rw [PCSBCSCallerPayloadCost.freshInterpret_erasure]
      cases AnchoredSourceFreshCaller.interpret layout saved tokens with
      | none => rfl
      | some claims =>
        rw [parsePendingKeyCount_value]
        cases parsePendingKey p entry key <;> rfl
  · rfl

theorem pendingValidityCount_calls (context : AnchoredHeaderCodec.Context)
    (cost : PCSBCSCallerPayloadCost.OutputCosts) (indices : List (Fin 8)) :
    (pendingValidityCount context cost indices).2.1.length ≤ indices.length := by
  induction indices with
  | nil => simp [pendingValidityCount]
  | cons i indices ih =>
    simp only [pendingValidityCount,List.length_cons]
    split <;> dsimp only <;> simp only [List.length_cons,List.length_nil] <;> omega

theorem recordValidityCount_calls (saved : AnchoredHeaderCodec.Record)
    (cost : PCSBCSCallerPayloadCost.OutputCosts) :
    (recordValidityCount saved cost).2.1.length ≤ 8 := by
  have bound := pendingValidityCount_calls saved.context cost (List.ofFn (fun i : Fin 8 => i))
  simp only [List.length_ofFn] at bound
  unfold recordValidityCount
  split
  · split
    · exact bound
    · simp
  · simp

/-- Exact per-byte answer count; source guards can suppress it but cannot
replace it by one callback per block. The metadata price is supplied outside
the internal parser-operation counter. -/
theorem parseReferencesCount_answerCalls (p : ParameterBounds.Profile) (layout : CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory) (answers : Coordinate → Digest32)
    (key : Coordinate) (cost : PCSBCSCallerPayloadCost.OutputCosts) (P : Nat)
    (entryCap : framesSize entry.frames ≤ P) :
    (parseReferencesCount p layout saved entry answers key cost).2.1 ≤ P*P := by
  have bound := (PCSBCSPublicLogParserCost.entryTokensCount_bound entry answers P entryCap).1
  unfold parseReferencesCount
  dsimp only
  split
  · split
    · exact bound
    · try dsimp only
      split
      · exact bound
      · try dsimp only
        split <;> exact bound
  · exact Nat.zero_le _


#print axioms recordValidityCount_value
#print axioms parseReferencesCount_value

#print axioms pendingModelCount_value
#print axioms completedModelCount_value
#print axioms outputKeyCount_value
#print axioms parsePendingKeyCount_value
end Whir.PCSBCSSourceReferenceParserCost
