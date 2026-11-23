module

public import NativeVm.Entry.Data
public import NativeVm.Transcript.Mem
public import Native.Keccak.Words

/-!
# The rustc verifier's caller-supplied memory
-/

@[expose] public section

namespace NativeVm.Entry

open Native.Keccak
open NativeVm.Transcript (wd Fits Disj ctxEnd)

/-- The caller's areas: the wire bytes', the bytecode's, the decoded proof's and the working
area's addresses. -/
structure Areas where
  wire : UInt64
  bytecode : UInt64
  decoded : UInt64
  work : UInt64

/-- The wire's words for `L` bytes. -/
def wireWords (L : Nat) : Nat := (L + 7) / 8

/-- **What the caller provides**: the context at `ctx`, its first `ctxEnd` words present, holding
the wire bytes' address and count (words `0`, `1`), the bytecode's address and word count (`2`,
`3`), the public input (`4 .. 7`), the decoded area's address and a size of at least
`decodedWords L` (`8`, `9`) and the working area's address and a size of at least
`workWords n` (`10`, `11`), `L` the bytes' count and `n` the bytecode's; the wire area holding the
bytes packed little-endian into `wireWords L` words, the last word's bytes past `L` zero; the
bytecode area holding its words; every word of the decoded and working areas present; `L < 2^32`
and `8 n + 9 < 2^32`; every area inside the address space and apart from the others, but for the
wire and the bytecode, which are only read. -/
structure EntryPre (mem : UInt64 → Option UInt64) (ctx : UInt64) (a : Areas) (bytes : List UInt8)
    (bytecode : List UInt64) (pub : Vector UInt64 4) : Prop where
  ctxSome : ∀ k < ctxEnd, (mem (wd ctx k)).isSome
  wirePtr : mem (wd ctx 0) = some a.wire
  wireLen : mem (wd ctx 1) = some bytes.length.toUInt64
  bcPtr : mem (wd ctx 2) = some a.bytecode
  bcLen : mem (wd ctx 3) = some bytecode.length.toUInt64
  pubWords : ∀ i (h : i < 4), mem (wd ctx (4 + i)) = some pub[i]
  decPtr : mem (wd ctx 8) = some a.decoded
  decLen : ∃ v, mem (wd ctx 9) = some v ∧ decodedWords bytes.length ≤ v.toNat
  workPtr : mem (wd ctx 10) = some a.work
  workLen : ∃ v, mem (wd ctx 11) = some v ∧ workWords bytecode.length ≤ v.toNat
  wire : ∃ ws : List UInt64, HoldsBytes ws bytes.length ∧
    (wordsBytes ws).take bytes.length = bytes ∧
    ∀ i (h : i < ws.length), mem (wd a.wire i) = some ws[i]
  bcWords : ∀ i (h : i < bytecode.length), mem (wd a.bytecode i) = some bytecode[i]
  decSome : ∀ k < decodedWords bytes.length, (mem (wd a.decoded k)).isSome
  workSome : ∀ k < workWords bytecode.length, (mem (wd a.work k)).isSome
  L32 : bytes.length < 2 ^ 32
  bcSmall : 8 * bytecode.length + 9 < 2 ^ 32
  fitCtx : Fits ctx ctxEnd
  fitWire : Fits a.wire (wireWords bytes.length)
  fitBc : Fits a.bytecode bytecode.length
  fitDec : Fits a.decoded (decodedWords bytes.length)
  fitWork : Fits a.work (workWords bytecode.length)
  disjCtxWire : Disj ctx ctxEnd a.wire (wireWords bytes.length)
  disjCtxBc : Disj ctx ctxEnd a.bytecode bytecode.length
  disjCtxDec : Disj ctx ctxEnd a.decoded (decodedWords bytes.length)
  disjCtxWork : Disj ctx ctxEnd a.work (workWords bytecode.length)
  disjWireDec : Disj a.wire (wireWords bytes.length) a.decoded (decodedWords bytes.length)
  disjWireWork : Disj a.wire (wireWords bytes.length) a.work (workWords bytecode.length)
  disjBcDec : Disj a.bytecode bytecode.length a.decoded (decodedWords bytes.length)
  disjBcWork : Disj a.bytecode bytecode.length a.work (workWords bytecode.length)
  disjDecWork : Disj a.decoded (decodedWords bytes.length) a.work (workWords bytecode.length)

end NativeVm.Entry
