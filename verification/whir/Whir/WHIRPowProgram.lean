import Whir.PublicMerkleProgram

/-! Source-pinned #552 nonce verification as metered public primitive requests.
Finishing and nonce binding occur on zero-difficulty and rejecting branches.
Packet entry replays the complete framed prefix conservatively; no live CV is
supplied by a decoder premise. No grinding amplification is claimed. -/
namespace Whir.WHIRPowProgram
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicMerkleProgram (Runs runReal_runs runIdeal_runs)
open RawWHIRKeys (Context Packet)
open WHIRHistory (Pending scalarBytes)
open WHIRHistoryKey (Normal initialPending canonicalFrames)

variable {R S : Type}

def askPow (n : Node) (next : Digest32 → Program R) : Program R := .ask (.primitive .pow n) next

private def askPowStored (n : Node) (next : Digest32 → Program R) : Program R :=
  .ask (.primitive .pow n) fun answer =>
    let bytes := Array.ofFn answer
    next (fun i => bytes[i.val]'(by simp only [bytes,Array.size_ofFn]; exact i.isLt))

@[csimp] theorem askPow_stored : @askPow = @askPowStored := by
  funext R n next
  simp [askPow,askPowStored]

theorem askPow_counted (n : Node) (next : Digest32 → Program R) (budget : Nat)
    (after : ∀ d, Counts budget (next d)) : Counts (1+budget) (askPow n next) := by
  simpa [askPow,Counts,Query.cost] using And.intro (by omega : 1 ≤ 1+budget) after

def payload (base : Digest32) (nonce : Scalar24) : List Byte :=
  List.ofFn base ++ List.ofFn nonce ++ littleWord 0x31574f502d534646

theorem payload_length (base : Digest32) (nonce : Scalar24) : (payload base nonce).length = 64 := by
  simp [payload,littleWord]

def powNode (base : Digest32) (nonce : Scalar24) : Node :=
  PublicMerkleLog.node DuplexCompression.parameterIV 0 (payload base nonce) true

def passed (digest : Digest32) (bits : Nat) : Bool :=
  ByteCodec.decodeNat 8 (fun i => digest ⟨i.val,by omega⟩) % 2^bits == 0

def powOK (C : PrimitiveOracle) (base : Digest32) (nonce : Scalar24) (bits : Nat) : Bool :=
  passed (C (powNode base nonce)) bits

theorem powOK_blake (base : Digest32) (nonce : Scalar24) (bits : Nat) :
    powOK blake2sOracle base nonce bits = DuplexCompression.powOK base nonce bits := by
  simp [powOK,passed,powNode,payload,PublicMerkleLog.node,blake2sOracle,
    DuplexCompression.powOK,DuplexCompression.hashBlock]

def finishNode (s : State) : Node :=
  ⟨s.cv,padded s.pending,absorbTweak s.first true s.pending.size s.previous,true⟩

def baseNode (cv : Digest32) (consumed bits : Nat) : Node :=
  ⟨cv,wordsBlock [consumed,bits],UInt64.ofNat (8*2^56),true⟩

def bindNode (cv : Digest32) (consumed : Nat) (nonce : Scalar24) (bits : Nat) : Node :=
  ⟨cv,nonceBlock nonce consumed bits,UInt64.ofNat (9*2^56),true⟩

def finishProgram (s : State) : Program State :=
  if s.pending.isEmpty then .done s else
    askPow (finishNode s) (fun cv => .done {s with cv := cv,pending := #[],first := true,previous := 0})

def finishCost (s : State) : Nat := if s.pending.isEmpty then 0 else 1

/-- The native order is base, ordinary PoW predicate, then mandatory nonce
binding. The zero-bit branch still makes the binding query. -/
def verifyClosed (cv : Digest32) (consumed : Nat) (nonce : Scalar24) (bits : Nat) : Program (Digest32 × Bool) :=
  if bits = 0 then
    askPow (bindNode cv consumed nonce bits) (fun updated => .done (updated,decide (nonce = fun _ => 0)))
  else
    askPow (baseNode cv consumed bits) fun base =>
      askPow (powNode base nonce) fun digest =>
        askPow (bindNode cv consumed nonce bits) (fun updated => .done (updated,passed digest bits))

def closedCost (bits : Nat) : Nat := if bits = 0 then 1 else 3

def verifyBounded (s : State) (nonce : Scalar24) (bits : Nat) : Program (State × Bool) :=
  WHIRModeFinal.bind (finishProgram s) fun finished =>
    WHIRModeFinal.bind (verifyClosed finished.cv finished.consumed nonce bits) fun result =>
      .done ({finished with cv := result.1,consumed := 0},result.2)

def verifyState (s : State) (nonce : Scalar24) (bits : Nat) : Program (Except Error (State × Bool)) :=
  if bits ≤ 63 then WHIRModeFinal.bind (verifyBounded s nonce bits) (fun result => .done (.ok result))
  else .done (.error .grindingBits)

def stateCost (s : State) (bits : Nat) : Nat :=
  if bits ≤ 63 then finishCost s + closedCost bits else 0

theorem finishProgram_real (C : PrimitiveOracle) (iv : Digest32) (s : State) :
    (runReal C iv (finishProgram s)).view.result = finish (compressionOf C) s := by
  simp only [finishProgram,finish]
  split <;> simp_all [askPow,runReal,prepend,realAnswer,finalized,finishNode,compressionOf]

theorem verifyClosed_real (C : PrimitiveOracle) (iv cv : Digest32) (consumed : Nat)
    (nonce : Scalar24) (bits : Nat) :
    (runReal C iv (verifyClosed cv consumed nonce bits)).view.result =
      (C (bindNode cv consumed nonce bits),
        if bits = 0 then decide (nonce = fun _ => 0) else powOK C (C (baseNode cv consumed bits)) nonce bits) := by
  by_cases h : bits = 0 <;> simp [verifyClosed,h,askPow,runReal,prepend,realAnswer,powOK]

theorem verifyBounded_real (C : PrimitiveOracle) (iv : Digest32) (s : State)
    (nonce : Scalar24) (bits : Nat) :
    (runReal C iv (verifyBounded s nonce bits)).view.result =
      (bindNonce (compressionOf C) s nonce bits,
        if bits = 0 then decide (nonce = fun _ => 0)
          else powOK C (powBase (compressionOf C) (finish (compressionOf C) s) bits) nonce bits) := by
  rw [verifyBounded,WHIRModeFinal.bind_real_result,finishProgram_real,
    WHIRModeFinal.bind_real_result,verifyClosed_real]
  simp only [runReal,bindNonce,baseNode,bindNode,powBase,finalized,finish_pending,
    Array.isEmpty_empty,↓reduceIte,compressionOf]

theorem verifyState_real (C : PrimitiveOracle) (iv : Digest32) (s : State)
    (nonce : Scalar24) (bits : Nat) :
    (runReal C iv (verifyState s nonce bits)).view.result =
      verifyNonce (compressionOf C) (powOK C) s nonce bits := by
  by_cases h : bits ≤ 63
  · simp only [verifyState,h,↓reduceIte,WHIRModeFinal.bind_real_result,verifyBounded_real,runReal,
      verifyNonce,bindNonce_finish]
  · simp [verifyState,verifyNonce,h,runReal]

theorem verifyState_blake (iv : Digest32) (s : State) (nonce : Scalar24) (bits : Nat) :
    (runReal blake2sOracle iv (verifyState s nonce bits)).view.result =
      verifyNonce DuplexCompression.compress DuplexCompression.powOK s nonce bits := by
  rw [verifyState_real]
  have h : powOK blake2sOracle = DuplexCompression.powOK := by funext base nonce bits; exact powOK_blake _ _ _
  rw [h]
  rfl

theorem finishProgram_counted (s : State) : Counts (finishCost s) (finishProgram s) := by
  by_cases h : s.pending.isEmpty <;> simp [finishProgram,finishCost,h,askPow,Counts,Query.cost]

theorem verifyClosed_counted (cv : Digest32) (consumed : Nat) (nonce : Scalar24) (bits : Nat) :
    Counts (closedCost bits) (verifyClosed cv consumed nonce bits) := by
  by_cases h : bits = 0 <;> simp [verifyClosed,closedCost,h,askPow,Counts,Query.cost]

theorem verifyBounded_counted (s : State) (nonce : Scalar24) (bits : Nat) :
    Counts (finishCost s + closedCost bits) (verifyBounded s nonce bits) := by
  apply WHIRModeFinal.bind_counted _ _ _ _ (finishProgram_counted s)
  intro finished
  simpa only [Nat.add_zero] using WHIRModeFinal.bind_counted
    (verifyClosed finished.cv finished.consumed nonce bits)
    (fun result => .done ({finished with cv := result.1,consumed := 0},result.2))
    (closedCost bits) 0 (verifyClosed_counted _ _ _ _) (fun _ => True.intro)

theorem verifyState_counted (s : State) (nonce : Scalar24) (bits : Nat) :
    Counts (stateCost s bits) (verifyState s nonce bits) := by
  by_cases h : bits ≤ 63
  · simpa only [verifyState,stateCost,h,↓reduceIte,Nat.add_zero] using
      WHIRModeFinal.bind_counted (verifyBounded s nonce bits)
        (fun result => .done (.ok result : Except Error (State × Bool)))
        (finishCost s + closedCost bits) 0 (verifyBounded_counted s nonce bits) (fun _ => True.intro)
  · simp [verifyState,stateCost,h,Counts]

/-- Reuse the actual seed and frame encodings, without any terminal/export node. -/
def historyInstructions (h : FramedHistory) : List DuplexEncoding.Instruction :=
  (ByteCodec.pairBytes (h.domain,h.statement),UInt64.ofNat (2^56)) :: h.frames.flatMap DuplexEncoding.framePlan

theorem historyInstructions_plan (h : FramedHistory) (t : Terminal) :
    historyInstructions h ++ [DuplexEncoding.terminalPlan t] = DuplexEncoding.plan ⟨h,t⟩ := rfl

def instructions (cv : Digest32) : List DuplexEncoding.Instruction → Program Digest32
  | [] => .done cv
  | i :: rest => askPow ⟨cv,i.1,i.2,true⟩ (fun answer => instructions answer rest)

def historyProgram (iv : Digest32) (h : FramedHistory) : Program Digest32 := instructions iv (historyInstructions h)

theorem instructions_real (C : PrimitiveOracle) (iv cv : Digest32) (is : List DuplexEncoding.Instruction) :
    (runReal C iv (instructions cv is)).view.result = evalPlan (compressionOf C) cv is := by
  induction is generalizing cv with
  | nil => rfl
  | cons i rest ih => simpa only [instructions,askPow,runReal,prepend,realAnswer,evalPlan,List.foldl_cons,compressionOf] using ih (C ⟨cv,i.1,i.2,true⟩)

theorem historyProgram_real (C : PrimitiveOracle) (iv : Digest32) (h : FramedHistory) :
    (runReal C iv (historyProgram iv h)).view.result = evalHistory (compressionOf C) iv h := by
  rw [historyProgram,instructions_real]
  change evalPlan (compressionOf C) (seed (compressionOf C) iv h.domain h.statement).cv
    (h.frames.flatMap DuplexEncoding.framePlan) = _
  exact framesPlan_evaluate _ _ _

theorem instructions_counted (cv : Digest32) (is : List DuplexEncoding.Instruction) :
    Counts is.length (instructions cv is) := by
  induction is generalizing cv with
  | nil => trivial
  | cons i rest ih => simpa only [instructions,List.length_cons,Nat.add_comm] using askPow_counted ⟨cv,i.1,i.2,true⟩ _ rest.length ih

theorem historyProgram_counted (iv : Digest32) (h : FramedHistory) :
    Counts (historyInstructions h).length (historyProgram iv h) := instructions_counted _ _

def nonceAt : List Pending → Option (Nat × E)
  | [] => none
  | m :: _ => m.nonce

def beforeNonceMessages : List Pending → List Pending
  | [] => []
  | m :: ps => {m with nonce := none} :: ps

def preHistory (ctx : Context) (p : RawWHIRKeys.PacketData) : FramedHistory :=
  ⟨ctx.domain,p.statement,p.entryFrames ++ canonicalFrames (RawWHIRKeys.width ctx.mode p.profile) (beforeNonceMessages p.messages)⟩

def preModel (ctx : Context) (p : RawWHIRKeys.PacketData) : Model :=
  WHIRCallerPrefix.beforeModelFrom (RawWHIRKeys.width ctx.mode p.profile) (RawWHIRKeys.entry ctx p)
    (beforeNonceMessages p.messages)

theorem nonce_shape (ctx : Context) (Q : Nat) (p : Packet ctx Q) (bits : Nat) (value : E)
    (hn : nonceAt p.val.messages = some (bits,value)) :
    ∃ m ps, p.val.messages = m :: ps ∧ Normal ps ∧ m.scalars ≠ [] ∧ m.nonce = some (bits,value) := by
  have normal := WHIRHistoryKey.scheduled_normal _ _ p.property.2.1 p.property.2.2.1
  generalize hm : p.val.messages = ms at normal hn ⊢
  cases normal with
  | initial => simp [nonceAt,initialPending] at hn
  | cons prior m nonempty => exact ⟨m,_,rfl,prior,nonempty,hn⟩

theorem nonce_bits (ctx : Context) (Q : Nat) (p : Packet ctx Q) (bits : Nat) (value : E)
    (hn : nonceAt p.val.messages = some (bits,value)) : bits ≤ 63 := by
  obtain ⟨m,ps,hm,_,_,he⟩ := nonce_shape ctx Q p bits value hn
  exact WHIRHistoryKey.scheduled_nonce_bits _ _ p.property.2.2.1 m (by simp [hm]) bits value he

theorem post_history (ctx : Context) (Q : Nat) (p : Packet ctx Q) (bits : Nat) (value : E)
    (hn : nonceAt p.val.messages = some (bits,value)) (block : Nat) :
    (RawWHIRKeys.coordinate ctx p.val block).history =
      {preHistory ctx p.val with frames := (preHistory ctx p.val).frames ++ [.nonce 0 bits (ByteCodec.encodeE value)]} := by
  obtain ⟨m,ps,hm,normal,_,he⟩ := nonce_shape ctx Q p bits value hn
  simp only [RawWHIRKeys.coordinate,preHistory,hm,beforeNonceMessages,
    WHIRHistoryKey.canonicalFrames_cons _ _ _ normal.nonempty,WHIRHistoryKey.stepFrames,he]
  simp [List.append_assoc]

theorem preModel_history (ctx : Context) (Q : Nat) (p : Packet ctx Q) (bits : Nat) (value : E)
    (hn : nonceAt p.val.messages = some (bits,value)) :
    (closeRun (preModel ctx p.val)).history = preHistory ctx p.val := by
  obtain ⟨m,ps,hm,normal,nonempty,_⟩ := nonce_shape ctx Q p bits value hn
  have before : Normal (beforeNonceMessages p.val.messages) := by
    rw [hm]
    exact .cons normal {m with nonce := none} nonempty
  exact WHIRCallerPrefix.before_historyFrom _ (RawWHIRKeys.width_positive ctx.mode p.val.profile) _ before

theorem preModel_consumed (ctx : Context) (Q : Nat) (p : Packet ctx Q) (bits : Nat) (value : E)
    (hn : nonceAt p.val.messages = some (bits,value)) : (preModel ctx p.val).consumed = 0 := by
  obtain ⟨m,ps,hm,_,nonempty,_⟩ := nonce_shape ctx Q p bits value hn
  have hb : scalarBytes m.scalars ≠ [] := fun he => nonempty ((WHIRHistory.scalarBytes_empty _).mp he)
  simp [preModel,hm,beforeNonceMessages,WHIRCallerPrefix.beforeModelFrom_cons,WHIRHistory.pendingModel,modelAbsorb,hb]

def preCoordinate (ctx : Context) (p : RawWHIRKeys.PacketData) (bits : Nat) : Coordinate :=
  ⟨preHistory ctx p,.powBase 0 bits⟩

theorem preCoordinate_admissible (ctx : Context) (Q : Nat) (p : Packet ctx Q) (bits : Nat) (value : E)
    (hn : nonceAt p.val.messages = some (bits,value)) : DuplexEncoding.Admissible (preCoordinate ctx p.val bits) := by
  have hb : 0 < RawWHIRKeys.blocks ctx p.val := by
    have hp := RawWHIRKeys.width_positive ctx.mode p.val.profile (p.val.messages.length-1)
    unfold RawWHIRKeys.blocks
    omega
  have h := RawWHIRKeys.coordinate_admissible ctx Q ⟨p,⟨0,hb⟩⟩
  refine ⟨?_,⟨by decide,nonce_bits ctx Q p bits value hn⟩⟩
  intro f hf
  apply h.1 f
  rw [post_history ctx Q p bits value hn 0]
  exact List.mem_append_left _ hf

theorem packet_path_split (ctx : Context) (Q : Nat) (p : Packet ctx Q) (bits : Nat) (value : E)
    (hn : nonceAt p.val.messages = some (bits,value)) :
    pathCost (RawWHIRKeys.coordinate ctx p.val 0) = (historyInstructions (preHistory ctx p.val)).length + 2 := by
  change (DuplexEncoding.plan (RawWHIRKeys.coordinate ctx p.val 0)).length = _
  unfold DuplexEncoding.plan
  rw [post_history ctx Q p bits value hn 0]
  simp [historyInstructions,DuplexEncoding.framePlan,List.flatMap_append,Nat.add_assoc]

structure Outcome (ctx : Context) (Q : Nat) (p : Packet ctx Q) where
  accepted : Bool
  boundCV : Option Digest32
  history : FramedHistory
  canonical : history = (RawWHIRKeys.coordinate ctx p.val 0).history

def Outcome.coordinate {ctx Q p} (outcome : Outcome ctx Q p) (block : Nat) : Coordinate :=
  ⟨outcome.history,.output block⟩

theorem Outcome.coordinate_eq {ctx Q p} (outcome : Outcome ctx Q p) (block : Nat) :
    outcome.coordinate block = RawWHIRKeys.coordinate ctx p.val block := by
  simp only [Outcome.coordinate,outcome.canonical]
  rfl

theorem Outcome.coordinate_admissible {ctx Q p} (outcome : Outcome ctx Q p)
    (i : Fin (RawWHIRKeys.blocks ctx p.val)) : DuplexEncoding.Admissible (outcome.coordinate i.val) := by
  rw [Outcome.coordinate_eq]
  exact RawWHIRKeys.coordinate_admissible ctx Q ⟨p,i⟩

/-- Binding retains the previous output cache, although cursor zero makes it
inactive. Supply those actual bytes rather than claiming a fake zero-cache state. -/
def Outcome.state {ctx Q p} (outcome : Outcome ctx Q p) (oldOutput : Digest32) : Option State :=
  outcome.boundCV.map (fun cv => {cv := cv,output := oldOutput})

def verifyPacket (ctx : Context) (Q : Nat) (p : Packet ctx Q) : Program (Outcome ctx Q p) :=
  match hn : nonceAt p.val.messages with
  | none => .done ⟨true,none,(RawWHIRKeys.coordinate ctx p.val 0).history,rfl⟩
  | some (bits,value) =>
    WHIRModeFinal.bind (historyProgram ctx.iv (preHistory ctx p.val)) fun cv =>
      WHIRModeFinal.bind (verifyClosed cv 0 (ByteCodec.encodeE value) bits) fun result =>
        .done ⟨result.2,some result.1,
          {preHistory ctx p.val with frames := (preHistory ctx p.val).frames ++ [.nonce 0 bits (ByteCodec.encodeE value)]},
          (post_history ctx Q p bits value hn 0).symm⟩

def packetCost (ctx : Context) (p : RawWHIRKeys.PacketData) : Nat :=
  match nonceAt p.messages with
  | none => 0
  | some (bits,_) => (historyInstructions (preHistory ctx p)).length + closedCost bits

theorem verifyPacket_counted (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    Counts (packetCost ctx p.val) (verifyPacket ctx Q p) := by
  unfold verifyPacket
  split
  · simp [Counts]
  next bits value hn =>
    simp only [packetCost,hn]
    apply WHIRModeFinal.bind_counted _ _ _ _ (historyProgram_counted _ _)
    intro cv
    have hc := verifyClosed_counted cv 0 (ByteCodec.encodeE value) bits
    change Counts (closedCost bits) (WHIRModeFinal.bind _ _)
    rw [← Nat.add_zero (closedCost bits)]
    apply WHIRModeFinal.bind_counted _ _ _ _ hc
    intro result
    trivial

theorem packetCost_bound (ctx : Context) (Q : Nat) (p : Packet ctx Q) : packetCost ctx p.val ≤ Q+1 := by
  unfold packetCost
  split
  · omega
  next bits value hn =>
    have h := packet_path_split ctx Q p bits value hn
    have hp := RawWHIRKeys.packet_pathBound ctx Q p
    unfold closedCost
    split <;> omega

theorem verifyPacket_real (C : PrimitiveOracle) (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    let out := (runReal C ctx.iv (verifyPacket ctx Q p)).view.result
    match nonceAt p.val.messages with
    | none => out.accepted = true ∧ out.boundCV = none
    | some (bits,value) =>
      let cv := evalHistory (compressionOf C) ctx.iv (preHistory ctx p.val)
      out.accepted = (if bits = 0 then decide (ByteCodec.encodeE value = fun _ => 0)
        else powOK C (C (baseNode cv 0 bits)) (ByteCodec.encodeE value) bits) ∧
      out.boundCV = some (C (bindNode cv 0 (ByteCodec.encodeE value) bits)) := by
  unfold verifyPacket
  split
  · next hn => simp [hn,runReal]
  next bits value hn =>
    simp [hn,WHIRModeFinal.bind_real_result,historyProgram_real,verifyClosed_real,runReal]

/-- The frame prefix is derived from the actual Pending packet. For every
represented native pre-nonce state, the returned full state (including retained
cache), Boolean, and rejection transition equal native verification exactly. -/
theorem verifyPacket_source (C : PrimitiveOracle) (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (bits : Nat) (value : E) (hn : nonceAt p.val.messages = some (bits,value))
    (s : State) (represented : Represents (compressionOf C) ctx.iv (preModel ctx p.val) s) :
    (verifyNonce (compressionOf C) (powOK C) s (ByteCodec.encodeE value) bits).toOption =
      let out := (runReal C ctx.iv (verifyPacket ctx Q p)).view.result
      (out.state s.output).map (fun state => (state,out.accepted)) := by
  have result := verifyPacket_real C ctx Q p
  simp only [hn] at result
  have hf := finish_represents (compressionOf C) ctx.iv (preModel ctx p.val) s represented
  have hm := materialize_closed (compressionOf C) ctx.iv (closeRun (preModel ctx p.val))
    (finish (compressionOf C) s).output hf.1 (closeRun_empty _)
  have ho : (finish (compressionOf C) s).output = s.output := by unfold finish; split <;> rfl
  have hs := hf.2.1.trans hm
  simp only [preModel_history ctx Q p bits value hn,closeRun_consumed,
    preModel_consumed ctx Q p bits value hn,ho] at hs
  simp only [verifyNonce,nonce_bits ctx Q p bits value hn,↓reduceIte,hs,
    Outcome.state,result.1,result.2,Option.map_some,Except.toOption]
  simp [bindNonce,finish,powBase,finalized,baseNode,bindNode,compressionOf]

theorem preModel_valid (ctx : Context) (Q : Nat) (p : Packet ctx Q) (bits : Nat) (value : E)
    (hn : nonceAt p.val.messages = some (bits,value)) : (preModel ctx p.val).Valid := by
  obtain ⟨m,ps,hm,normal,nonempty,_⟩ := nonce_shape ctx Q p bits value hn
  have hb : scalarBytes m.scalars ≠ [] := fun he => nonempty ((WHIRHistory.scalarBytes_empty _).mp he)
  have bound := RawWHIRKeys.width_bounded ctx.mode p.val.profile (ps.length-1)
  have positive := RawWHIRKeys.width_positive ctx.mode p.val.profile (ps.length-1)
  simp only [preModel,hm,beforeNonceMessages,WHIRCallerPrefix.beforeModelFrom_cons,
    WHIRCallerPrefix.completedModelFrom,
    WHIRHistoryKey.completed_normal _ (RawWHIRKeys.width_positive ctx.mode p.val.profile) _ _ normal,
    WHIRCallerPrefix.prepend,WHIRHistory.pendingModel,modelAbsorb,hb,↓reduceIte,
    List.nil_append,Model.Valid]
  simp only [hb,not_false_eq_true,true_implies,false_implies,
    Nat.zero_le,ne_eq,Nat.ne_of_gt positive,↓reduceIte,true_and]
  change RawWHIRKeys.width ctx.mode p.val.profile (ps.length-1) ≤ 2^49-1
  omega

/-- No assumed representation/codec bridge is needed for the actual source
state obtained by executing its pending absorption from this packet model. -/
theorem verifyPacket_materialized (C : PrimitiveOracle) (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (bits : Nat) (value : E) (hn : nonceAt p.val.messages = some (bits,value)) (oldOutput : Digest32) :
    (verifyNonce (compressionOf C) (powOK C)
      (materialize (compressionOf C) ctx.iv (preModel ctx p.val) oldOutput)
      (ByteCodec.encodeE value) bits).toOption =
      let out := (runReal C ctx.iv (verifyPacket ctx Q p)).view.result
      (out.state oldOutput).map (fun state => (state,out.accepted)) := by
  have hv := preModel_valid ctx Q p bits value hn
  have represented : Represents (compressionOf C) ctx.iv (preModel ctx p.val)
      (materialize (compressionOf C) ctx.iv (preModel ctx p.val) oldOutput) := by
    refine ⟨hv,?_,?_⟩
    · rw [materialize_output]
    · simp [CacheValid,materialize_consumed _ _ _ _ hv,preModel_consumed ctx Q p bits value hn]
  simpa only [materialize_output] using verifyPacket_source C ctx Q p bits value hn _ represented

/-- Every branch of the source helper asks only globally counted PoW-purpose
primitive queries, including finish and binding queries. -/
def PowOnly : Program R → Prop
  | .done _ => True
  | .ask (.primitive .pow _) next => ∀ d, PowOnly (next d)
  | .ask _ _ => False

theorem PowOnly.bind {p : Program R} {next : R → Program S}
    (hp : PowOnly p) (hn : ∀ r, PowOnly (next r)) : PowOnly (WHIRModeFinal.bind p next) := by
  induction p with
  | done r => exact hn r
  | ask q cont ih =>
    cases q with
    | construction q valid => exact False.elim hp
    | primitive purpose node =>
      cases purpose <;> try exact False.elim hp
      exact fun d => ih d (hp d)

theorem finishProgram_powOnly (s : State) : PowOnly (finishProgram s) := by
  unfold finishProgram
  split <;> simp [askPow,PowOnly]

theorem verifyClosed_powOnly (cv : Digest32) (consumed : Nat) (nonce : Scalar24) (bits : Nat) :
    PowOnly (verifyClosed cv consumed nonce bits) := by
  unfold verifyClosed
  split <;> simp [askPow,PowOnly]

theorem verifyState_powOnly (s : State) (nonce : Scalar24) (bits : Nat) :
    PowOnly (verifyState s nonce bits) := by
  unfold verifyState
  split
  · apply PowOnly.bind
    · unfold verifyBounded
      apply PowOnly.bind (finishProgram_powOnly s)
      intro finished
      exact PowOnly.bind (verifyClosed_powOnly _ _ _ _) (fun _ => True.intro)
    · intro result
      trivial
  · trivial

theorem instructions_powOnly (cv : Digest32) (is : List DuplexEncoding.Instruction) :
    PowOnly (instructions cv is) := by
  induction is generalizing cv with
  | nil => trivial
  | cons i rest ih => exact fun d => ih d

theorem verifyPacket_powOnly (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    PowOnly (verifyPacket ctx Q p) := by
  unfold verifyPacket
  split
  · trivial
  · apply PowOnly.bind (instructions_powOnly _ _)
    intro cv
    exact PowOnly.bind (verifyClosed_powOnly _ _ _ _) (fun _ => True.intro)

/-- Consume public answers in order. In particular, repeated nodes may have
different answers: replay neither consults a total hash nor silently memoizes. -/
def replay (p : Program R) (trace : List Observation) : Option (R × List Observation) :=
  match p with
  | .done r => some (r,trace)
  | .ask (.primitive .pow n) next =>
    match trace with
    | ⟨.primitive .pow observed,answer⟩ :: rest =>
      if n = observed then replay (next answer) rest else none
    | _ => none
  | .ask _ _ => none

theorem replay_runs {p : Program R} {trace : List Observation} {result : R}
    (only : PowOnly p) (run : Runs p trace result) (suffix : List Observation) :
    replay p (trace ++ suffix) = some (result,suffix) := by
  induction run with
  | done r => rfl
  | @ask q next trace r answer run ih =>
    cases q with
    | construction q valid => exact False.elim only
    | primitive purpose node =>
      cases purpose <;> try exact False.elim only
      simpa only [replay,List.cons_append,↓reduceIte] using ih (only answer)

theorem replay_ideal {G : Nat} {Seed SimState : Type} (sim : Simulator G Seed SimState)
    (ro : RawKey G → Digest32) (iv : Digest32) (state : SimState) (p : Program R)
    (remaining : Nat) (cap : remaining ≤ G) (counted : Counts remaining p)
    (only : PowOnly p) (suffix : List Observation) :
    replay p ((runIdeal sim ro iv state p remaining cap counted).view.observations ++ suffix) =
      some ((runIdeal sim ro iv state p remaining cap counted).view.result,suffix) :=
  replay_runs only (runIdeal_runs sim ro iv state p remaining cap counted) suffix

end Whir.WHIRPowProgram
