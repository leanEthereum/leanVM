module

public import NativeVm.Code.Main
public import NativeVm.Wire.End

/-!
# The leanVM verifier's entry

What a caller of the verifier provides, in the terms of `NativeVm.Input`: the context at `rdi`
pointing to the wire bytes, the bytecode words, the decoded proof's area and the working area, and
holding the public input (`EntryPre`); and what the verifier then does (`entry_spec`): `body` ends
normally, or fails and `onFail` ends normally, either way with `rax = 1` exactly when the wire
bytes decode (`Proof.fromBytes`) to a proof `verifyWith` accepts, and the callee-saved registers
restored. `EntryPre` gives `BodyPre` (`bodyPre_of_entryPre`), from which `verifier_spec` runs, with
the decoder's contract proved (`Wire.decode_ok'`).
-/

@[expose] public section

namespace NativeVm.Code

open Native Native.Keccak LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
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

/-- The verifier's input: the bytecode at its address, the public input. -/
def EntryPre.input (a : Areas) (bytecode : List UInt64) (pub : Vector UInt64 4) : Input :=
  ⟨a.bytecode, bytecode.toArray, pub⟩

theorem ctxN_le : Wire.ctxN ≤ ctxEnd := by decide

/-- **`EntryPre` gives `BodyPre`**, the decoder's environment holding the wire's words. -/
theorem bodyPre_of_entryPre {s : QState} {ctx : UInt64} {a : Areas} {bytes : List UInt8}
    {bytecode : List UInt64} {pub : Vector UInt64 4} (hrdi : s.reg .rdi = ctx)
    (hp : EntryPre s.mem ctx a bytes bytecode pub) :
    ∃ we : Wire.Env, we.B = bytes ∧ BodyPre s we (EntryPre.input a bytecode pub) := by
  obtain ⟨ws, hold, htake, hws⟩ := hp.wire
  have hlen : ws.length = wireWords bytes.length := hold.1
  have hcx := ctxN_le
  have hww := wireWork_le bytecode.length
  have hsz : (EntryPre.input a bytecode pub).bytecode.size = bytecode.length := by
    simp [EntryPre.input]
  refine ⟨⟨s.mem, ctx, a.wire, a.decoded, a.work, ws, bytes.length⟩, htake, ?_⟩
  have hfx : Wire.Fit ctx Wire.ctxN := by
    have := hp.fitCtx; unfold Fits at this; unfold Wire.Fit; omega
  have hfw : Wire.Fit a.wire ws.length := by
    have := hp.fitWire; unfold Fits at this; unfold Wire.Fit; omega
  have hfk : Wire.Fit a.work Wire.workWords := by
    have := hp.fitWork; unfold Fits at this; unfold Wire.Fit; omega
  have hxw : Wire.Apart ctx Wire.ctxN a.wire ws.length := by
    have := hp.disjCtxWire; unfold Disj at this; unfold Wire.Apart; omega
  have hxd : Wire.Apart ctx Wire.ctxN a.decoded (decodedWords bytes.length) := by
    have := hp.disjCtxDec; unfold Disj at this; unfold Wire.Apart; omega
  have hxk : Wire.Apart ctx Wire.ctxN a.work Wire.workWords := by
    have := hp.disjCtxWork; unfold Disj at this; unfold Wire.Apart; omega
  have hwd : Wire.Apart a.wire ws.length a.decoded (decodedWords bytes.length) := by
    have := hp.disjWireDec; unfold Disj at this; unfold Wire.Apart; omega
  have hwk : Wire.Apart a.wire ws.length a.work Wire.workWords := by
    have := hp.disjWireWork; unfold Disj at this; unfold Wire.Apart; omega
  have hdk : Wire.Apart a.decoded (decodedWords bytes.length) a.work Wire.workWords := by
    have := hp.disjDecWork; unfold Disj at this; unfold Wire.Apart; omega
  exact
    { rdi := hrdi
      mem := rfl
      wire :=
        { fx := hfx, fw := hfw, fd := hp.fitDec, fk := hfk, xw := hxw, xd := hxd, xk := hxk
          wd := hwd, wk' := hwk, dk := hdk, hold := hold, L32 := hp.L32
          c0 := hp.wirePtr, c1 := hp.wireLen, c8 := hp.decPtr, c9 := hp.decLen
          c10 := hp.workPtr
          c11 := by
            obtain ⟨v, hv, hle⟩ := hp.workLen
            exact ⟨v, hv, le_trans hww hle⟩
          scr := fun k hk ↦ hp.ctxSome _ (by
            have : Wire.ctxN = Wire.cScr + Keccak.scratchWords := rfl
            omega)
          wire := fun i hi ↦ by
            have hi' : i < ws.length := hi
            show s.mem (wd a.wire i) = some (ws.getD i 0)
            rw [hws i hi', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
              Option.getD_some]
          dec := hp.decSome
          work := fun k hk ↦ hp.workSome k (by omega) }
      fitCtx := hp.fitCtx
      ctxSome := hp.ctxSome
      disjCtxDec := hp.disjCtxDec
      bcPtr := hp.bcPtr
      bcLen := ⟨by rw [hsz]; have := hp.bcSmall; omega, by rw [hsz]; exact hp.bcLen⟩
      bcWords := fun i hi ↦ by
        have hi' : i < bytecode.length := hsz ▸ hi
        show s.mem (wd a.bytecode i) = _
        rw [hp.bcWords i hi']
        simp [EntryPre.input]
      pubWords := hp.pubWords
      bcSmall := by rw [hsz]; exact hp.bcSmall
      fitBc := by rw [hsz]; exact hp.fitBc
      fitWork := by rw [hsz]; exact hp.fitWork
      disjCtxWork := by rw [hsz]; exact hp.disjCtxWork
      disjDecWork := by rw [hsz]; exact hp.disjDecWork
      disjBcCtx := by rw [hsz]; exact Disj.symm hp.disjCtxBc
      disjBcDec := by rw [hsz]; exact hp.disjBcDec
      disjBcWork := by rw [hsz]; exact hp.disjBcWork
      workSome := by rw [hsz]; exact hp.workSome }

/-- The verdict on the entry's input is the wire's: `Proof.fromBytes`, then `verifyWith`. -/
theorem verdict_input (bytes : List UInt8) (a : Areas) (bytecode : List UInt64)
    (pub : Vector UInt64 4) :
    verdict bytes (EntryPre.input a bytecode pub) =
      (Id.run (Proof.fromBytes (m := Id) keccakF1600 bytes)).elim false fun π ↦
        Id.run (LeanVM.Protocol.Verifier.verifyWith (m := Id) keccakF1600
          (bytecode.map K.ofLane) pub π) := by
  simp only [verdict, EntryPre.input, List.toList_toArray]

/-- **The verifier from its entry**: from `EntryPre`, `body` ends normally, or fails and `onFail`
ends normally, either way with `rax = 1` exactly when the wire bytes decode to a proof
`verifyWith` accepts (`verdict_input`), and the callee-saved registers restored. It assumes the
phases' contracts. -/
theorem entry_spec (h1 : Phase1Ok phase1) (h2 : Phase2Ok phase2)
    (h3 : Phase3Ok phase3) (h4 : Phase4Ok phase4) (h5 : Phase5Ok phase5) (h6 : Phase6Ok phase6)
    (h7 : Phase7Ok phase7) {s : QState} {ctx : UInt64} {a : Areas} {bytes : List UInt8}
    {bytecode : List UInt64} {pub : Vector UInt64 4} (hrdi : s.reg .rdi = ctx)
    (hp : EntryPre s.mem ctx a bytes bytecode pub) :
    WP body s (Ret s.reg (verdict bytes (EntryPre.input a bytecode pub)))
      (fun s' ↦ WP onFail s' (Ret s.reg (verdict bytes (EntryPre.input a bytecode pub)))
        (fun _ ↦ False)) := by
  obtain ⟨we, hB, hbp⟩ := bodyPre_of_entryPre hrdi hp
  rw [← hB]
  exact verifier_spec Wire.decode_ok' h1 h2 h3 h4 h5 h6 h7 hbp

end NativeVm.Code
