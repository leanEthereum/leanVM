module

public import NativeRustcVmX64.Top.Leanvm.Exec
public import NativeRustcVmX64.Top.Basic
public import NativeRustcVm.WordView
public import NativeVm.Equiv.Execution
public import NativeVm.Wire.ModelSpec
public import NativeRustcVm.Wire.ModelFacts

/-!
# `leanvm_verify`: where things are (x86-64)

The verdict in the model's terms (`verdict_none`, `verdict_some`: `decodeM_spec` is
`Proof.fromBytes`, `decodeM_toProof` its proof, `verify_eq` is `verifyWith`); rustc's
`decoded_words(L)` (`dw_toNat`); the context's words (`ctxWord`); what `LeanvmVerifyPre` gives as
numbers, relative to the stack's bottom `lsb m0` and without subtraction (`Geo`, `geo_of`).
-/

namespace NativeRustcVmX64.Top.Leanvm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeVm NativeVm.Wire
open NativeRustcVm.Wire
open NativeRustcVm.Top (workAreaBytes usedRegions ApartFrom Aligned)
open NativeVm.Transcript (wd)
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

theorem verdict_none {bytes : List UInt8} (h : decodeM bytes = none) (bytecode : List UInt64)
    (pub : Vector UInt64 4) : verdictWord bytes bytecode pub = 0 := by
  unfold verdictWord
  rw [decodeM_spec, h]
  rfl

theorem verdict_some {bytes : List UInt8} {r : List E × List PhaseOut} (h : decodeM bytes = some r)
    (bytecode : List UInt64) (pub : Vector UInt64 4) :
    verdictWord bytes bytecode pub =
      if Model.verify bytecode.toArray pub (streamW r.1) (openingsW r.2) then 1 else 0 := by
  unfold verdictWord
  rw [decodeM_spec, h, NativeVm.Equiv.verify_eq]
  simp only [Option.map_some, Option.elim_some, decodeM_toProof h]

theorem orOne (n : Nat) : n ||| 1 = 2 * (n / 2) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    rw [Nat.testBit_succ, Nat.testBit_succ (2 * (n / 2) + 1),
      show (2 * (n / 2) + 1) / 2 = n / 2 by omega, Nat.testBit_succ 1]
    simp

/-- rustc's `decoded_words(L)`: `((L >> 3) | 1) + 395289`. -/
theorem dw_toNat {x : BitVec 64} {L : Nat} (hx : x.toNat = L) (hL : L < 2 ^ 32) :
    (BinOp.apply .add .W64 (BitVec.ofNat 64 395289)
      (BinOp.apply .or .W64 (BinOp.apply .shr .W64 x (BitVec.ofNat 64 3))
        (BitVec.ofNat 64 1))).toNat = decodedWords L := by
  simp only [BinOp.apply, low_W64, ext_W64, shiftCount, shiftMask]
  have e3 : (low .W8 (BitVec.ofNat 64 3)).toNat &&& 63 = 3 := by decide
  rw [e3, BitVec.toNat_add, BitVec.toNat_or, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, hx, Nat.shiftRight_eq_div_pow,
    show 1 % 2 ^ 64 = 1 from rfl, orOne]
  unfold decodedWords phaseBase streamEnd maxStream
  simp only [LeanVM.Protocol.Compile.wireMaxPhases]
  rw [show phaseWords = 49411 from rfl]
  omega

/-- A word of the context. -/
theorem ctxWord {d : DataMem} {ctx v : UInt64} {k : Nat}
    (h : NativeRustcVm.wordView d (wd ctx k) = some v) :
    NativeRustcVm.WordAt d (ctx.toBitVec + BitVec.ofNat 64 (8 * k)) v := by
  have := NativeRustcVm.wordAt_of_wordView h
  rwa [NativeRustcVm.toBitVec_wd] at this

theorem leanvmVerifyStack_eq : leanvmVerifyStack = 18816 := rfl

theorem workAreaBytes_le : workAreaBytes ≤ 8 * NativeVm.Entry.workWords := by
  have := NativeRustcVm.Top.workAreaWords_le
  unfold workAreaBytes; omega

theorem decodedWords_pos (L : Nat) : 0 < decodedWords L := by
  unfold decodedWords phaseBase; omega

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 112 := by decide
theorem slots_ge : ∀ p ∈ slots, 64 ≤ p.1 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

end

/-- The stack's bottom: the `18816` bytes below the entry's RSP start here. -/
@[expose] public def lsb (m0 : MachineData) : Nat := (stackBelow m0 18816).toNat

public theorem lsb_eq (m0 : MachineData) : (stackBelow m0 18816).toNat = lsb m0 := rfl

/-- `LeanvmVerifyPre`'s addresses as numbers (`C` the context, `D` the decoded area's bytes). -/
public structure Geo (a : NativeVm.Entry.Areas) (L n : Nat) (m0 : MachineData) : Prop where
  R : (rspOf m0).toNat = lsb m0 + 18816
  e8 : lsb m0 + 18824 ≤ 2 ^ 64
  F : (stackBelow m0 112).toNat = lsb m0 + 18704
  ctxN : (ctxOf m0).toNat + 8 * NativeVm.Entry.ctxWords ≤ 2 ^ 64
  ctx : (ctxOf m0).toNat + 8 * NativeVm.Entry.ctxWords ≤ lsb m0 ∨ lsb m0 + 18824 ≤ (ctxOf m0).toNat
  decN : a.decoded.toNat + 8 * decodedWords L ≤ 2 ^ 64
  dec : a.decoded.toNat + 8 * decodedWords L ≤ lsb m0 ∨ lsb m0 + 18824 ≤ a.decoded.toNat
  workN : a.work.toNat + workAreaBytes ≤ 2 ^ 64
  work : a.work.toNat + workAreaBytes ≤ lsb m0 ∨ lsb m0 + 18824 ≤ a.work.toNat
  decWork : a.decoded.toNat + 8 * decodedWords L ≤ a.work.toNat ∨
    a.work.toNat + workAreaBytes ≤ a.decoded.toNat
  ctxDec : (ctxOf m0).toNat + 8 * NativeVm.Entry.ctxWords ≤ a.decoded.toNat ∨
    a.decoded.toNat + 8 * decodedWords L ≤ (ctxOf m0).toNat
  ctxWork : (ctxOf m0).toNat + 8 * NativeVm.Entry.ctxWords ≤ a.work.toNat ∨
    a.work.toNat + workAreaBytes ≤ (ctxOf m0).toNat
  bcN : a.bytecode.toNat + 8 * n ≤ 2 ^ 64
  bc : 0 < n → a.bytecode.toNat + 8 * n ≤ lsb m0 ∨ lsb m0 + 18824 ≤ a.bytecode.toNat
  bcDec : 0 < n → a.bytecode.toNat + 8 * n ≤ a.decoded.toNat ∨
    a.decoded.toNat + 8 * decodedWords L ≤ a.bytecode.toNat
  bcWork : 0 < n → a.bytecode.toNat + 8 * n ≤ a.work.toNat ∨
    a.work.toNat + workAreaBytes ≤ a.bytecode.toNat
  wireN : a.wire.toNat + L ≤ 2 ^ 64
  wire : 0 < L → a.wire.toNat + L ≤ lsb m0 ∨ lsb m0 + 18824 ≤ a.wire.toNat
  wireDec : 0 < L → a.wire.toNat + L ≤ a.decoded.toNat ∨
    a.decoded.toNat + 8 * decodedWords L ≤ a.wire.toNat
  wireWork : 0 < L → a.wire.toNat + L ≤ a.work.toNat ∨
    a.work.toNat + workAreaBytes ≤ a.wire.toNat

public section

theorem geo_of [Labels] {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {m0 : MachineData}
    (hpre : LeanvmVerifyPre a bytes bytecode pub m0) :
    Geo a bytes.length bytecode.length m0 := by
  obtain ⟨hst, -, hin, -, hapS, -⟩ := hpre
  have hS := leanvmVerifyStack_eq
  have hs : 18816 ≤ (rspOf m0).toNat := by have := hst.1; omega
  have h8 := hst.2.1
  have hR : (rspOf m0).toNat = lsb m0 + 18816 := by rw [lsb, stackBelow_toNat hs]; omega
  have hF : (stackBelow m0 112).toNat = lsb m0 + 18704 := by
    rw [stackBelow_toNat (by omega)]; omega
  have hwa := workAreaBytes_le
  have hdp := decodedWords_pos bytes.length
  have hce : NativeVm.Entry.ctxWords = 12 := (rfl)
  have ap : ∀ (x : UInt64) (sz : Nat),
      (⟨x.toBitVec, sz⟩ : NativeRustcVm.Region) ∈
        usedRegions (ctxOf m0) a bytes.length bytecode.length →
      0 < sz → x.toNat + sz ≤ lsb m0 ∨ lsb m0 + 18824 ≤ x.toNat := fun x sz hr hp ↦ by
    have h := hapS _ hr hp
    unfold NativeRustcVm.Apart at h
    rw [hS, lsb_eq] at h
    simp only [UInt64.toNat_toBitVec] at h
    omega
  have fx := hin.fitCtx
  have fd := hin.fitDec
  have fk := hin.fitWork
  have fb := hin.fitBc
  have fw := hin.fitWire
  have dxd := hin.disjCtxDec
  have dxk := hin.disjCtxWork
  have ddk := hin.disjDecWork
  have dbd := hin.disjBcDec
  have dbk := hin.disjBcWork
  have dwd := hin.disjWireDec
  have dwk := hin.disjWireWork
  unfold NativeVm.Transcript.Fits at fx fd fk fb
  unfold NativeRustcVm.NoWrap at fw
  unfold NativeVm.Transcript.Disj at dxd dxk ddk dbd dbk
  unfold NativeRustcVm.Apart at dwd dwk
  simp only [UInt64.toNat_toBitVec] at fw dwd dwk
  have a0 := ap (ctxOf m0) (8 * NativeVm.Entry.ctxWords) (by simp [usedRegions]) (by omega)
  have a3 := ap a.decoded (8 * decodedWords bytes.length) (by simp [usedRegions]) (by omega)
  have a4 := ap a.work (8 * NativeVm.Entry.workWords) (by simp [usedRegions])
    (by unfold workAreaBytes NativeRustcVm.Top.workAreaWords at hwa; omega)
  refine ⟨hR, by omega, hF, fx, a0, fd, a3, by omega, by omega, by omega, dxd, by omega, fb,
    fun hn ↦ ?_, dbd, (fun hn ↦ by have := dbk hn; omega), fw, fun hL ↦ ?_,
    dwd, (fun hL ↦ by have := dwk hL; omega)⟩
  · exact ap a.bytecode (8 * bytecode.length) (by simp [usedRegions]) (by omega)
  · exact ap a.wire bytes.length (by simp [usedRegions]) hL

end

end NativeRustcVmX64.Top.Leanvm
