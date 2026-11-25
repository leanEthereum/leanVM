module

public import NativeVm.Entry.Data
public import NativeVm.Transcript.Mem
public import NativeRustcVm.Mem

/-!
# The rustc verifier's caller-supplied memory
-/

@[expose] public section

namespace NativeVm.Entry

open NativeRustcVm (wordView BytesAt NoWrap Apart)
open NativeVm.Transcript (wd Fits Disj)

/-- The caller's areas: the wire bytes', the bytecode's, the decoded proof's and the working
area's addresses. -/
structure Areas where
  wire : UInt64
  bytecode : UInt64
  decoded : UInt64
  work : UInt64
  decCount : UInt64
  workCount : UInt64

/-- The twelve context words, including the declared capacities. -/
structure ContextAt (mem : Mem 64) (ctx : UInt64) (a : Areas) (bytes : List UInt8)
    (bytecode : List UInt64) (pub : Vector UInt64 4) : Prop where
  ctxSome : ∀ k < ctxWords, (wordView mem (wd ctx k)).isSome
  wirePtr : wordView mem (wd ctx 0) = some a.wire
  wireLen : wordView mem (wd ctx 1) = some bytes.length.toUInt64
  bcPtr : wordView mem (wd ctx 2) = some a.bytecode
  bcLen : wordView mem (wd ctx 3) = some bytecode.length.toUInt64
  pubWords : ∀ i (h : i < 4), wordView mem (wd ctx (4 + i)) = some pub[i]
  decPtr : wordView mem (wd ctx 8) = some a.decoded
  decCount : wordView mem (wd ctx 9) = some a.decCount
  workPtr : wordView mem (wd ctx 10) = some a.work
  workCount : wordView mem (wd ctx 11) = some a.workCount
  L64 : bytes.length < 2 ^ 64
  bc64 : bytecode.length < 2 ^ 64
  fitCtx : Fits ctx ctxWords
  ctxAligned : ctx.toNat % 8 = 0
  ctxNonzero : ctx ≠ 0

/-- The size checks performed by `leanvm_verify`, not caller obligations. -/
def CountsOk (a : Areas) (L n : Nat) : Prop :=
  L < 2 ^ 32 ∧ 8 * n + 9 < 2 ^ 32 ∧
    decodedWords L ≤ a.decCount.toNat ∧ workWords ≤ a.workCount.toNat

/-- The Rust safety contract: exact input bytes and declared scratch capacities. -/
structure EntryPre (mem : Mem 64) (ctx : UInt64) (a : Areas) (bytes : List UInt8)
    (bytecode : List UInt64) (pub : Vector UInt64 4) : Prop extends ContextAt mem ctx a bytes bytecode pub where
  wire : BytesAt mem a.wire.toBitVec bytes
  bcWords : ∀ i (h : i < bytecode.length), wordView mem (wd a.bytecode i) = some bytecode[i]
  decSome : ∀ k < a.decCount.toNat, (wordView mem (wd a.decoded k)).isSome
  workSome : ∀ k < a.workCount.toNat, (wordView mem (wd a.work k)).isSome
  fitWire : NoWrap a.wire.toBitVec bytes.length
  fitBc : Fits a.bytecode bytecode.length
  fitDec : Fits a.decoded a.decCount.toNat
  fitWork : Fits a.work a.workCount.toNat
  disjCtxWire : 0 < bytes.length → Apart ctx.toBitVec (8 * ctxWords) a.wire.toBitVec bytes.length
  disjCtxBc : 0 < bytecode.length → Disj ctx ctxWords a.bytecode bytecode.length
  disjCtxDec : 0 < a.decCount.toNat → Disj ctx ctxWords a.decoded a.decCount.toNat
  disjCtxWork : 0 < a.workCount.toNat → Disj ctx ctxWords a.work a.workCount.toNat
  disjWireDec : 0 < bytes.length → 0 < a.decCount.toNat → Apart a.wire.toBitVec bytes.length a.decoded.toBitVec (8 * a.decCount.toNat)
  disjWireWork : 0 < bytes.length → 0 < a.workCount.toNat → Apart a.wire.toBitVec bytes.length a.work.toBitVec (8 * a.workCount.toNat)
  disjBcDec : 0 < bytecode.length → 0 < a.decCount.toNat → Disj a.bytecode bytecode.length a.decoded a.decCount.toNat
  disjBcWork : 0 < bytecode.length → 0 < a.workCount.toNat → Disj a.bytecode bytecode.length a.work a.workCount.toNat
  disjDecWork : 0 < a.decCount.toNat → 0 < a.workCount.toNat → Disj a.decoded a.decCount.toNat a.work a.workCount.toNat

/-- The successful-check path's memory, narrowed to the words it may use. -/
structure CheckedEntryPre (mem : Mem 64) (ctx : UInt64) (a : Areas) (bytes : List UInt8)
    (bytecode : List UInt64) (pub : Vector UInt64 4) : Prop extends ContextAt mem ctx a bytes bytecode pub where
  decLen : ∃ v, wordView mem (wd ctx 9) = some v ∧ decodedWords bytes.length ≤ v.toNat
  workLen : ∃ v, wordView mem (wd ctx 11) = some v ∧ workWords ≤ v.toNat
  wire : BytesAt mem a.wire.toBitVec bytes
  bcWords : ∀ i (h : i < bytecode.length), wordView mem (wd a.bytecode i) = some bytecode[i]
  decSome : ∀ k < decodedWords bytes.length, (wordView mem (wd a.decoded k)).isSome
  workSome : ∀ k < workWords, (wordView mem (wd a.work k)).isSome
  L32 : bytes.length < 2 ^ 32
  bcSmall : 8 * bytecode.length + 9 < 2 ^ 32
  fitWire : NoWrap a.wire.toBitVec bytes.length
  fitBc : Fits a.bytecode bytecode.length
  fitDec : Fits a.decoded (decodedWords bytes.length)
  fitWork : Fits a.work workWords
  disjCtxWire : 0 < bytes.length → Apart ctx.toBitVec (8 * ctxWords) a.wire.toBitVec bytes.length
  disjCtxBc : 0 < bytecode.length → Disj ctx ctxWords a.bytecode bytecode.length
  disjCtxDec : Disj ctx ctxWords a.decoded (decodedWords bytes.length)
  disjCtxWork : Disj ctx ctxWords a.work workWords
  disjWireDec : 0 < bytes.length → Apart a.wire.toBitVec bytes.length a.decoded.toBitVec (8 * decodedWords bytes.length)
  disjWireWork : 0 < bytes.length → Apart a.wire.toBitVec bytes.length a.work.toBitVec (8 * workWords)
  disjBcDec : 0 < bytecode.length → Disj a.bytecode bytecode.length a.decoded (decodedWords bytes.length)
  disjBcWork : 0 < bytecode.length → Disj a.bytecode bytecode.length a.work workWords
  disjDecWork : Disj a.decoded (decodedWords bytes.length) a.work workWords

theorem EntryPre.checked {mem : Mem 64} {ctx : UInt64} {a : Areas} {bytes : List UInt8}
    {bytecode : List UInt64} {pub : Vector UInt64 4} (h : EntryPre mem ctx a bytes bytecode pub)
    (hc : CountsOk a bytes.length bytecode.length) : CheckedEntryPre mem ctx a bytes bytecode pub := by
  obtain ⟨hL, hn, hd, hw⟩ := hc
  have hdpos : 0 < a.decCount.toNat := by
    have : 0 < decodedWords bytes.length := by unfold decodedWords phaseBase; omega
    omega
  have hwpos : 0 < a.workCount.toNat := by
    change 61944 ≤ a.workCount.toNat at hw
    omega
  refine ⟨h.toContextAt, ⟨a.decCount, h.decCount, hd⟩, ⟨a.workCount, h.workCount, hw⟩,
    h.wire, h.bcWords, (fun k hk ↦ h.decSome k (by omega)),
    (fun k hk ↦ h.workSome k (by omega)), hL, hn, h.fitWire, h.fitBc, ?_, ?_,
    h.disjCtxWire, h.disjCtxBc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    try intro hpos
    have hfd := h.fitDec
    have hfw := h.fitWork
    have hcd := h.disjCtxDec hdpos
    have hcw := h.disjCtxWork hwpos
    have hwd := fun hp ↦ h.disjWireDec hp hdpos
    have hww := fun hp ↦ h.disjWireWork hp hwpos
    have hbd := fun hp ↦ h.disjBcDec hp hdpos
    have hbw := fun hp ↦ h.disjBcWork hp hwpos
    have hdw := h.disjDecWork hdpos hwpos
    unfold Fits Disj Apart at *
    omega

end NativeVm.Entry
