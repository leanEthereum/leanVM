import Whir.WHIRCallerRegistry

/-! Header roots are extracted before an allocation receives its fresh answer. In particular, caller-output garbage keys are decoded as exact bounded mode keys, not as final WHIR packets. The immutable public registry selects the caller layout and profile; no caller output is consulted to parse the header. -/
namespace Whir.WHIRHeaderRoots
open FiatShamirGame DuplexFraming DuplexModeGame
open RawOracleCoupling RawOracleCoupling.Concrete

/-- `extractedPlan` alone forgets raw bits. Exact reconstruction checks the IV, flags, holes, lengths and complete template before any header is used. -/
def decodeRaw {Q : Nat} (iv : Digest32) (raw : RawKey Q) : Option Coordinate :=
  match DuplexEncoding.decode (extractedPlan (expandKey raw)) with
  | none => none
  | some q =>
    if bound : pathCost q ≤ Q then
      if constructionKey Q iv q bound = raw then some q else none
    else none

theorem decodeRaw_construction {Q : Nat} (iv : Digest32) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) (bound : pathCost q ≤ Q) :
    decodeRaw iv (constructionKey Q iv q bound) = some q := by
  simp [decodeRaw, expand_constructionKey, RawWHIRKeys.extractedPlan_modeKey,
    DuplexEncoding.decode_plan q valid, bound]

theorem decodeRaw_sound {Q : Nat} (iv : Digest32) (raw : RawKey Q) (q : Coordinate)
    (decoded : decodeRaw iv raw = some q) :
    ∃ bound : pathCost q ≤ Q, DuplexEncoding.Admissible q ∧ constructionKey Q iv q bound = raw := by
  unfold decodeRaw at decoded
  split at decoded
  · contradiction
  · rename_i parsed found
    split at decoded
    · rename_i bound
      split at decoded
      · rename_i exactRaw
        cases Option.some.inj decoded
        exact ⟨bound,(DuplexEncoding.decode_sound found).1,exactRaw⟩
      · contradiction
    · contradiction

theorem decodeRaw_iff {Q : Nat} (iv : Digest32) (raw : RawKey Q) (q : Coordinate) :
    decodeRaw iv raw = some q ↔
      ∃ bound : pathCost q ≤ Q, DuplexEncoding.Admissible q ∧ constructionKey Q iv q bound = raw := by
  constructor
  · exact decodeRaw_sound iv raw q
  · rintro ⟨bound,valid,rfl⟩
    exact decodeRaw_construction iv q valid bound

/-- No caller output is drawn before the initial absorb-zero frame: its preceding cursor is zero, so enumeration contributes no output block at the empty history. -/
theorem callerOutput_header (entry : FramedHistory) (bytes : List Byte) (rest : List Frame)
    (header : entry.frames = .absorb 0 bytes :: rest) (q : Coordinate)
    (member : q ∈ WHIRCallerOutputs.callerOutputs entry) :
    ∃ later, q.history.frames = .absorb 0 bytes :: later := by
  obtain ⟨pre,f,suffix,block,split,bound,rfl⟩ := WHIRCallerOutputs.callerOutputs_mem entry q member
  rw [header] at split
  cases pre with
  | nil =>
    simp only [List.nil_append,List.cons.injEq] at split
    rw [← split.1] at bound
    simp [WHIRCallerOutputs.previousConsumed,WHIRCallerOutputs.outputBlocks] at bound
  | cons first pre =>
    simp only [List.cons_append,List.cons.injEq] at split
    exact ⟨pre,by rw [← split.1]⟩

/-- The complete first absorb run is already present in every source caller output key. Later samples are not needed to read it. -/
def initialBytes (history : FramedHistory) : Option (List Byte) :=
  match history.frames with
  | .absorb 0 bytes :: _ => some bytes
  | _ => none

theorem callerOutput_initialBytes (entry : FramedHistory) (bytes : List Byte) (rest : List Frame)
    (header : entry.frames = .absorb 0 bytes :: rest) (q : Coordinate)
    (member : q ∈ WHIRCallerOutputs.callerOutputs entry) :
    initialBytes q.history = some bytes := by
  obtain ⟨later,head⟩ := callerOutput_header entry bytes rest header q member
  simp [initialBytes,head]

theorem decodeRaw_callerOutputKey (ctx : RawWHIRKeys.Context) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (q : Coordinate)
    (member : q ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val)) :
    decodeRaw ctx.iv (RawWHIRKeys.callerOutputKey ctx Q packet q member).val = some q :=
  decodeRaw_construction ctx.iv q (RawWHIRKeys.callerOutput_admissible ctx Q packet q member)
    (RawWHIRKeys.callerOutput_pathBound ctx Q packet q member)

theorem callerGroup_header (ctx : RawWHIRKeys.Context) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (bytes : List Byte) (rest : List Frame)
    (header : packet.val.entryFrames = .absorb 0 bytes :: rest)
    (raw : {raw : RawKey Q // RawWHIRKeys.Garbage ctx Q raw})
    (member : raw ∈ RawWHIRKeys.callerGroups ctx Q packet) :
    ∃ q, decodeRaw ctx.iv raw.val = some q ∧ initialBytes q.history = some bytes ∧
      q.history.domain = ctx.domain ∧ q.history.statement = packet.val.statement := by
  obtain ⟨⟨q,hq⟩,_,rfl⟩ := List.mem_map.mp member
  have same := WHIRCallerOutputs.callerOutputs_strict_prefix (RawWHIRKeys.entry ctx packet.val) q hq
  exact ⟨q,decodeRaw_callerOutputKey ctx Q packet q hq,
    callerOutput_initialBytes _ bytes rest header q hq,same.1,same.2.1⟩

open WHIRCallerClaims WHIRCallerRegistry

structure Header where
  statement : Digest32
  profile : ParameterBounds.Profile
  root : Digest32

/-- Public layout selection and exact concrete CPU/recursion header parsing. -/
def fromHistory (registry : Public) (history : FramedHistory) : Option Header :=
  if history.domain = registry.domain then
    match selection registry history.statement with
    | none => none
    | some (layout,profile) =>
      (initialRoot layout history).map (fun root => ⟨history.statement,profile,root⟩)
  else none

def rawHeader (registry : Public) {Q : Nat} (raw : RawKey Q) : Option Header :=
  (decodeRaw registry.iv raw).bind (fun q => fromHistory registry q.history)

def packetHeader (registry : Public) (Q : Nat) (packet : RawWHIRKeys.Packet (context registry) Q) :
    Option Header := fromHistory registry (RawWHIRKeys.entry (context registry) packet.val)

/-- Only the allocation key is inspected. Neither its new answer nor its old answer annotation is an input to header parsing. -/
def allocationHeader (registry : Public) (Q : Nat) (key : AllocationKey (context registry) Q) : Option Header :=
  match key.1 with
  | .inl packet => packetHeader registry Q packet
  | .inr raw => rawHeader registry raw.val

def rawRoot (registry : Public) {Q : Nat} (raw : RawKey Q) : Option Digest32 :=
  (rawHeader registry raw).map Header.root

def allocationRoot (registry : Public) (Q : Nat) (key : AllocationKey (context registry) Q) : Option Digest32 :=
  (allocationHeader registry Q key).map Header.root

def allocationRoots (registry : Public) (Q : Nat) (key : AllocationKey (context registry) Q) : List Digest32 :=
  (allocationRoot registry Q key).toList

theorem allocationHeader_prior_irrelevant (registry : Public) (Q : Nat)
    (key : GroupKey (context registry) Q)
    (a b : List (Sigma (GroupAnswer (context registry) Q))) :
    allocationHeader registry Q (key,a) = allocationHeader registry Q (key,b) := rfl

theorem fromHistory_selected (registry : Public) (history : FramedHistory)
    (layout : CallerLayout) (profile : ParameterBounds.Profile) (root : Digest32)
    (domain : history.domain = registry.domain)
    (selected : selection registry history.statement = some (layout,profile))
    (parsed : initialRoot layout history = some root) :
    fromHistory registry history = some ⟨history.statement,profile,root⟩ := by
  simp [fromHistory,domain,selected,parsed]

theorem fromHistory_sound (registry : Public) (history : FramedHistory) (header : Header)
    (parsed : fromHistory registry history = some header) :
    history.domain = registry.domain ∧ header.statement = history.statement ∧
      ∃ layout, selection registry history.statement = some (layout,header.profile) ∧
        initialRoot layout history = some header.root := by
  unfold fromHistory at parsed
  split at parsed
  · rename_i domain
    split at parsed
    · contradiction
    · rename_i layout profile selected
      cases root : initialRoot layout history with
      | none => simp [root] at parsed
      | some value =>
        simp only [root,Option.map_some,Option.some.injEq] at parsed
        subst header
        exact ⟨domain,rfl,layout,selected,root⟩
  · contradiction

/-- Any accepted raw header comes from an exact valid bounded mode key and a real public-layout header parse, even when the key is garbage for the WHIR packet partition. -/
theorem rawHeader_sound (registry : Public) {Q : Nat} (raw : RawKey Q) (header : Header)
    (parsed : rawHeader registry raw = some header) :
    ∃ q, decodeRaw registry.iv raw = some q ∧
      (∃ bound : pathCost q ≤ Q, DuplexEncoding.Admissible q ∧ constructionKey Q registry.iv q bound = raw) ∧
      fromHistory registry q.history = some header := by
  cases decoded : decodeRaw registry.iv raw with
  | none => simp [rawHeader,decoded] at parsed
  | some q =>
    have hp : fromHistory registry q.history = some header := by simpa [rawHeader,decoded] using parsed
    exact ⟨q,rfl,decodeRaw_sound registry.iv raw q decoded,hp⟩

theorem initialRoot_header (layout : CallerLayout) (entry : FramedHistory) (root : Digest32)
    (parsed : initialRoot layout entry = some root) :
    ∃ bytes rest, entry.frames = .absorb 0 bytes :: rest := by
  cases frames : entry.frames with
  | nil => simp [initialRoot,frames] at parsed
  | cons frame rest =>
    cases frame with
    | nonce consumed bits value => simp [initialRoot,frames] at parsed
    | absorb previous bytes =>
      cases previous with
      | zero => exact ⟨bytes,rest,rfl⟩
      | succ previous => simp [initialRoot,frames] at parsed

theorem callerOutput_initialRoot (layout : CallerLayout) (entry : FramedHistory) (root : Digest32)
    (parsed : initialRoot layout entry = some root) (q : Coordinate)
    (member : q ∈ WHIRCallerOutputs.callerOutputs entry) :
    initialRoot layout q.history = some root := by
  obtain ⟨bytes,rest,header⟩ := initialRoot_header layout entry root parsed
  obtain ⟨later,qheader⟩ := callerOutput_header entry bytes rest header q member
  simpa only [initialRoot,header,qheader] using parsed

theorem initialRoot_append (layout : CallerLayout) (entry : FramedHistory) (root : Digest32)
    (parsed : initialRoot layout entry = some root) (suffix : List Frame) :
    initialRoot layout {entry with frames := entry.frames ++ suffix} = some root := by
  obtain ⟨bytes,rest,header⟩ := initialRoot_header layout entry root parsed
  simpa only [initialRoot,header,List.cons_append] using parsed

theorem rawHeader_construction (registry : Public) {Q : Nat} (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) (bound : pathCost q ≤ Q)
    (header : Header) (parsed : fromHistory registry q.history = some header) :
    rawHeader registry (constructionKey Q registry.iv q bound) = some header := by
  simp [rawHeader,decodeRaw_construction registry.iv q valid bound,parsed]

theorem packetRequest_initialRoot (registry : Public) (Q cap : Nat)
    (packet : RawWHIRKeys.Packet (context registry) Q)
    (history : List (Sigma (GroupAnswer (context registry) Q)))
    (request : CausalBindingState.ClaimRequest cap packet.val.profile)
    (decoded : packetRequest registry Q cap packet history = some request) :
    initialRoot (packetLayout registry Q packet) (RawWHIRKeys.entry (context registry) packet.val) =
      some request.root :=
  decodeAvailableRequest_initialRoot cap packet.val.profile
    (callerLanes (packetLayout registry Q packet)) (packetLayout registry Q packet)
    (RawWHIRKeys.entry (context registry) packet.val)
    (callerAnswers (context registry) Q packet history) request decoded

theorem packetHeader_request (registry : Public) (Q cap : Nat)
    (packet : RawWHIRKeys.Packet (context registry) Q)
    (history : List (Sigma (GroupAnswer (context registry) Q)))
    (request : CausalBindingState.ClaimRequest cap packet.val.profile)
    (decoded : packetRequest registry Q cap packet history = some request) :
    packetHeader registry Q packet = some ⟨packet.val.statement,packet.val.profile,request.root⟩ :=
  fromHistory_selected registry _ (packetLayout registry Q packet) packet.val.profile request.root
    rfl (packet_selection registry Q packet) (packetRequest_initialRoot registry Q cap packet history request decoded)

theorem callerOutputKey_header (registry : Public) (Q cap : Nat)
    (packet : RawWHIRKeys.Packet (context registry) Q)
    (history : List (Sigma (GroupAnswer (context registry) Q)))
    (request : CausalBindingState.ClaimRequest cap packet.val.profile)
    (decoded : packetRequest registry Q cap packet history = some request)
    (q : Coordinate) (member : q ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry (context registry) packet.val)) :
    rawHeader registry (RawWHIRKeys.callerOutputKey (context registry) Q packet q member).val =
      some ⟨packet.val.statement,packet.val.profile,request.root⟩ := by
  have same := WHIRCallerOutputs.callerOutputs_strict_prefix (RawWHIRKeys.entry (context registry) packet.val) q member
  have hs : q.history.statement = packet.val.statement := same.2.1
  have hd : q.history.domain = registry.domain := same.1
  have root := callerOutput_initialRoot (packetLayout registry Q packet) _ request.root
    (packetRequest_initialRoot registry Q cap packet history request decoded) q member
  have selected : selection registry q.history.statement =
      some (packetLayout registry Q packet,packet.val.profile) := by
    rw [hs]
    exact packet_selection registry Q packet
  have result := fromHistory_selected registry q.history _ _ _ hd selected root
  unfold rawHeader
  rw [show decodeRaw registry.iv (RawWHIRKeys.callerOutputKey (context registry) Q packet q member).val =
    some q from decodeRaw_callerOutputKey (context registry) Q packet q member]
  simpa only [Option.bind_some,hs] using result

theorem callerGroup_header_request (registry : Public) (Q cap : Nat)
    (packet : RawWHIRKeys.Packet (context registry) Q)
    (history : List (Sigma (GroupAnswer (context registry) Q)))
    (request : CausalBindingState.ClaimRequest cap packet.val.profile)
    (decoded : packetRequest registry Q cap packet history = some request)
    (raw : {raw : RawKey Q // RawWHIRKeys.Garbage (context registry) Q raw})
    (member : raw ∈ RawWHIRKeys.callerGroups (context registry) Q packet) :
    rawHeader registry raw.val = some ⟨packet.val.statement,packet.val.profile,request.root⟩ := by
  obtain ⟨⟨q,hq⟩,_,rfl⟩ := List.mem_map.mp member
  exact callerOutputKey_header registry Q cap packet history request decoded q hq

/-- This conclusion holds for every old annotation, including an empty cache before the very first fresh caller answer. -/
theorem allocation_caller_root (registry : Public) (Q cap : Nat)
    (packet : RawWHIRKeys.Packet (context registry) Q)
    (history : List (Sigma (GroupAnswer (context registry) Q)))
    (request : CausalBindingState.ClaimRequest cap packet.val.profile)
    (decoded : packetRequest registry Q cap packet history = some request)
    (raw : {raw : RawKey Q // RawWHIRKeys.Garbage (context registry) Q raw})
    (member : raw ∈ RawWHIRKeys.callerGroups (context registry) Q packet)
    (prior : List (Sigma (GroupAnswer (context registry) Q))) :
    allocationRoots registry Q (.inr raw,prior) = [request.root] := by
  simp [allocationRoots,allocationRoot,allocationHeader,
    callerGroup_header_request registry Q cap packet history request decoded raw member]

theorem allocation_packet_root (registry : Public) (Q cap : Nat)
    (packet : RawWHIRKeys.Packet (context registry) Q)
    (history : List (Sigma (GroupAnswer (context registry) Q)))
    (request : CausalBindingState.ClaimRequest cap packet.val.profile)
    (decoded : packetRequest registry Q cap packet history = some request)
    (prior : List (Sigma (GroupAnswer (context registry) Q))) :
    allocationRoots registry Q (.inl packet,prior) = [request.root] := by
  simp [allocationRoots,allocationRoot,allocationHeader,
    packetHeader_request registry Q cap packet history request decoded]

end Whir.WHIRHeaderRoots
