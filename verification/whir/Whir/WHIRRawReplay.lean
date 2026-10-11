import Whir.RawOracleProvenance
import Whir.StackWHIRCodec

namespace Whir.WHIRRawReplay
open Concrete Protocol CausalProbability ParameterBounds
open FiatShamirGame (Digest32 average)
open RawOracleCoupling RawOracleCoupling.Concrete
open Classical
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

abbrev GlobalCoordinate := (p : Profile) × Coordinate (config p)
abbrev GlobalSample (q : GlobalCoordinate) := StackWHIRReplay.Sample q.2
abbrev GlobalStatement := Profile × FiatShamirGame.FramedHistory

def globalQuery (input : GlobalStatement × List WHIRHistory.Pending) : GlobalCoordinate :=
  ⟨input.1.1, StackWHIRReplay.query input.1.1 (input.1.2.statement,input.2)⟩

abbrev GlobalKey := TypedFiatShamirGame.FullInput GlobalStatement WHIRHistory.Pending
  GlobalCoordinate GlobalSample
abbrev GlobalAnswer := TypedOracleCompiler.Fiber (A := GlobalSample) globalQuery
abbrev GlobalEntry := WHIRHistory.Pending × Sigma GlobalSample

theorem packet_blocks (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) :
    RawWHIRKeys.blocks ctx packet.val = StackWHIRCodec.outputBlocks
      (StackWHIRReplay.query packet.val.profile (packet.val.statement,packet.val.messages)) := by
  rw [StackWHIRCodec.outputBlocks_eq]
  simp only [RawWHIRKeys.blocks, RawWHIRKeys.width, stack, WHIRHistoryKey.stackWidth,
    StackWHIRReplay.query, WHIRReplay.query, WHIRHistory.queryFor, Nat.mul_comm]

def packetEquiv (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) :
    GroupAnswer ctx Q (.inl packet) ≃
      (Fin (StackWHIRCodec.outputBlocks
        (StackWHIRReplay.query packet.val.profile (packet.val.statement,packet.val.messages))) → Digest32) :=
  Equiv.arrowCongr (finCongr (packet_blocks ctx stack Q packet)) (Equiv.refl Digest32)

def decodePacket (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (raw : GroupAnswer ctx Q (.inl packet)) :
    StackWHIRReplay.Sample
      (StackWHIRReplay.query packet.val.profile (packet.val.statement,packet.val.messages)) :=
  StackWHIRCodec.blockDecode _ (packetEquiv ctx stack Q packet raw)

def packetEntry (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (raw : GroupAnswer ctx Q (.inl packet)) : GlobalEntry :=
  (packet.val.messages.headD ⟨[],none⟩,
    ⟨⟨packet.val.profile,StackWHIRReplay.query packet.val.profile
      (packet.val.statement,packet.val.messages)⟩,decodePacket ctx stack Q packet raw⟩)

def decodeEntry (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat) :
    Sigma (GroupAnswer ctx Q) → Option GlobalEntry
  | ⟨.inl packet,raw⟩ => some (packetEntry ctx stack Q packet raw)
  | ⟨.inr _,_⟩ => none

def decodeHistory (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (history : List (Sigma (GroupAnswer ctx Q))) : List GlobalEntry :=
  (history.filterMap (decodeEntry ctx stack Q)).reverse

def callerEntry (ctx : RawWHIRKeys.Context) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) :
    FiatShamirGame.FramedHistory :=
  RawWHIRKeys.entry ctx packet.val

def allocationKey (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (history : List (Sigma (GroupAnswer ctx Q))) : GlobalKey :=
  ⟨(packet.val.profile,callerEntry ctx Q packet),packet.val.messages,
    decodeHistory ctx stack Q history⟩

def decodeAllocation (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat) :
    Sigma (AllocationAnswer ctx Q) → Option (Sigma GlobalAnswer)
  | ⟨(.inl packet,history),raw⟩ =>
    some ⟨allocationKey ctx stack Q packet history,decodePacket ctx stack Q packet raw⟩
  | ⟨(.inr _,_),_⟩ => none

def decodedTrace (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (trace : List (Sigma (AllocationAnswer ctx Q))) : List (Sigma GlobalAnswer) :=
  trace.filterMap (decodeAllocation ctx stack Q)

abbrev LocalEntry (p : Profile) :=
  WHIRHistory.Pending × Sigma (@StackWHIRReplay.Sample (config p))

def restrictEntry (p : Profile) : GlobalEntry → Option (LocalEntry p)
  | (m,⟨⟨r,q⟩,x⟩) =>
    if h : r = p then some (h ▸ (m,⟨q,x⟩)) else none

@[simp] theorem restrictEntry_self (p : Profile) (m : WHIRHistory.Pending)
    (q : Coordinate (config p)) (x : StackWHIRReplay.Sample q) :
    restrictEntry p (m,⟨⟨p,q⟩,x⟩) = some (m,⟨q,x⟩) := by
  simp [restrictEntry]

def localKey (key : GlobalKey) : StackWHIRReplay.Key key.statement.1 :=
  ⟨key.statement.2.statement,key.messages,key.ancestors.filterMap (restrictEntry key.statement.1)⟩

def restrictAllocation (p : Profile) (entry : FiatShamirGame.FramedHistory) : Sigma GlobalAnswer →
    Option (Sigma (StackWHIRReplay.Answer p))
  | ⟨⟨(r,s),messages,history⟩,a⟩ =>
    if h : r = p then
      if s = entry then
        some (h ▸ (⟨⟨s.statement,messages,history.filterMap (restrictEntry r)⟩,a⟩ :
          Sigma (StackWHIRReplay.Answer r)))
      else none
    else none

@[simp] theorem restrictAllocation_self (p : Profile) (s : FiatShamirGame.FramedHistory)
    (messages : List WHIRHistory.Pending) (history : List GlobalEntry)
    (a : StackWHIRReplay.Sample (StackWHIRReplay.query p (s.statement,messages))) :
    restrictAllocation p s ⟨⟨(p,s),messages,history⟩,a⟩ =
      some ⟨⟨s.statement,messages,history.filterMap (restrictEntry p)⟩,a⟩ := by
  simp [restrictAllocation]

def localTrace (p : Profile) (entry : FiatShamirGame.FramedHistory) (trace : List (Sigma GlobalAnswer)) :=
  trace.filterMap (restrictAllocation p entry)

theorem restrict_recorded (p : Profile) (s : FiatShamirGame.FramedHistory) (trace : List (Sigma GlobalAnswer))
    (messages : List WHIRHistory.Pending) (history : List GlobalEntry)
    (recorded : TypedOracleCompiler.HistoryRecorded globalQuery (p,s) trace messages history) :
    TypedOracleCompiler.HistoryRecorded (StackWHIRReplay.query p) s.statement
      (localTrace p s trace) messages (history.filterMap (restrictEntry p)) := by
  induction recorded with
  | nil => exact .nil
  | @cons m messages history a older allocated ih =>
    simp only [List.filterMap_cons, globalQuery, restrictEntry]
    apply TypedOracleCompiler.HistoryRecorded.cons
      (query := StackWHIRReplay.query p) (A := @StackWHIRReplay.Sample (config p)) a ih
    exact List.mem_filterMap.mpr ⟨_,allocated,restrictAllocation_self p s _ _ a⟩

end Whir.WHIRRawReplay
