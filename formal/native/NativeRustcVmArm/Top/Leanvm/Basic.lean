module

public import NativeRustcVmArm.Code.Vm.LeanvmVerify.Names
public import NativeRustcVmArm.Spec.Top
public import NativeRustcVmArm.Top.Leanvm.Exec
public import NativeRustcVm.WordView

/-!
# `leanvm_verify`: where things are

The 128-byte frame at `frameOf m0`; the context's words in memory (`ctxWord`); what
`LeanvmVerifyPre` gives as numbers (`Geo`, `geo_of`); the read-only data kept where memory changed
apart from it (`rodataAt_keep`); the blocks' places and labels.
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LeanvmVerify NativeVm
open NativeRustcVm (WordAt WordsAt Region)
open NativeRustcVm.Top (workAreaBytes usedRegions ApartFrom Aligned)
open NativeVm.Transcript (wd)

/-- The frame's address. -/
@[expose] public def frameOf (m0 : MachineData) : BitVec 64 :=
  m0.regs.SP.toBitVec - BitVec.ofNat 64 128

public section

theorem leanvmVerifyStack_eq : leanvmVerifyStack = 19344 := rfl

theorem slotsIn : SlotsIn slots 64 128 := by
  intro p hp
  simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem nonslot {r : XReg} (hr : calleeSaved r = true) (hn : r ∉ slots.map (·.2)) :
    r ∈ nonslots := by
  cases r <;> simp_all [calleeSaved, slots, nonslots]

/-- A word of the context. -/
theorem ctxWord {d : DataMem} {ctx v : UInt64} {k : Nat}
    (h : NativeRustcVm.wordView d (wd ctx k) = some v) :
    WordAt d (ctx.toBitVec + BitVec.ofNat 64 (8 * k)) v := by
  have := NativeRustcVm.wordAt_of_wordView h
  rwa [NativeRustcVm.toBitVec_wd] at this

/-- The read-only data kept where memory changed apart from it, apart from a stack range inside
the first. -/
theorem rodataAt_keep [Labels] {m m' : MachineData} {n n' : Nat} {R : BitVec 64 → Prop}
    (h : RodataAt m n) (hs : SameOutside m.dmem m'.dmem R)
    (hR : ∀ p, R p → ∀ t : NativeRustcVm.Data.Item,
      p.toNat < (rodataAddr t).toNat ∨ (rodataAddr t).toNat + t.bytes.length ≤ p.toNat)
    (h1 : (stackBelow m n).toNat ≤ (stackBelow m' n').toNat)
    (h2 : (stackBelow m' n').toNat + n' ≤ (stackBelow m n).toNat + n) : RodataAt m' n' :=
  fun t ↦ ⟨bytesAt_keep (h.bytesAt t) hs (h.noWrap t) (fun p hp ↦ hR p hp t), h.noWrap t,
    NativeRustcVm.Apart.mono_right (h.apart t) h1 h2⟩

/-- `LeanvmVerifyPre`'s addresses as numbers. -/
public structure Geo (a : NativeVm.Entry.Areas) (L n : Nat) (m0 : MachineData) : Prop where
  s : 19344 ≤ m0.regs.SP.toBitVec.toNat
  al : m0.regs.SP.toBitVec.toNat % 16 = 0
  F : (frameOf m0).toNat = m0.regs.SP.toBitVec.toNat - 128
  sb : (stackBelow m0 leanvmVerifyStack).toNat = m0.regs.SP.toBitVec.toNat - 19344
  ctxN : m0.regs.X0.toNat + 8 * NativeVm.Entry.ctxWords ≤ 2 ^ 64
  ctx : m0.regs.X0.toNat + 8 * NativeVm.Entry.ctxWords ≤ m0.regs.SP.toBitVec.toNat - 19344 ∨
    m0.regs.SP.toBitVec.toNat ≤ m0.regs.X0.toNat
  decN : a.decoded.toNat + 8 * decodedWords L ≤ 2 ^ 64
  dec : a.decoded.toNat + 8 * decodedWords L ≤ m0.regs.SP.toBitVec.toNat - 19344 ∨
    m0.regs.SP.toBitVec.toNat ≤ a.decoded.toNat
  workN : a.work.toNat + workAreaBytes ≤ 2 ^ 64
  work : a.work.toNat + workAreaBytes ≤ m0.regs.SP.toBitVec.toNat - 19344 ∨
    m0.regs.SP.toBitVec.toNat ≤ a.work.toNat
  decWork : a.decoded.toNat + 8 * decodedWords L ≤ a.work.toNat ∨
    a.work.toNat + workAreaBytes ≤ a.decoded.toNat
  ctxDec : m0.regs.X0.toNat + 8 * NativeVm.Entry.ctxWords ≤ a.decoded.toNat ∨
    a.decoded.toNat + 8 * decodedWords L ≤ m0.regs.X0.toNat
  ctxWork : m0.regs.X0.toNat + 8 * NativeVm.Entry.ctxWords ≤ a.work.toNat ∨
    a.work.toNat + workAreaBytes ≤ m0.regs.X0.toNat
  bcN : a.bytecode.toNat + 8 * n ≤ 2 ^ 64
  bc : 0 < n → a.bytecode.toNat + 8 * n ≤ m0.regs.SP.toBitVec.toNat - 19344 ∨
    m0.regs.SP.toBitVec.toNat ≤ a.bytecode.toNat
  bcDec : 0 < n → a.bytecode.toNat + 8 * n ≤ a.decoded.toNat ∨
    a.decoded.toNat + 8 * decodedWords L ≤ a.bytecode.toNat
  bcWork : 0 < n → a.bytecode.toNat + 8 * n ≤ a.work.toNat ∨
    a.work.toNat + workAreaBytes ≤ a.bytecode.toNat
  wireN : a.wire.toNat + L ≤ 2 ^ 64
  wire : 0 < L → a.wire.toNat + L ≤ m0.regs.SP.toBitVec.toNat - 19344 ∨
    m0.regs.SP.toBitVec.toNat ≤ a.wire.toNat
  wireDec : 0 < L → a.wire.toNat + L ≤ a.decoded.toNat ∨
    a.decoded.toNat + 8 * decodedWords L ≤ a.wire.toNat
  wireWork : 0 < L → a.wire.toNat + L ≤ a.work.toNat ∨
    a.work.toNat + workAreaBytes ≤ a.wire.toNat

theorem workAreaBytes_le : workAreaBytes ≤ 8 * NativeVm.Entry.workWords := by
  have := NativeRustcVm.Top.workAreaWords_le
  unfold workAreaBytes; omega

theorem decodedWords_pos (L : Nat) : 0 < decodedWords L := by
  unfold decodedWords phaseBase; omega

theorem geo_of [Labels] {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {m0 : MachineData}
    (hpre : LeanvmVerifyPre a bytes bytecode pub m0) :
    Geo a bytes.length bytecode.length m0 := by
  obtain ⟨⟨hal, hsN, -⟩, -, hin, -, hapS, -⟩ := hpre
  have hS := leanvmVerifyStack_eq
  have hsl := m0.regs.SP.toBitVec.isLt
  have hs : 19344 ≤ m0.regs.SP.toBitVec.toNat := by
    have : leanvmVerifyStack ≤ m0.regs.SP.toBitVec.toNat := hsN
    rw [hS] at this; exact this
  have hsb : (stackBelow m0 leanvmVerifyStack).toNat = m0.regs.SP.toBitVec.toNat - 19344 := by
    show (m0.regs.SP.toBitVec - BitVec.ofNat 64 leanvmVerifyStack).toNat = _
    rw [hS]; exact toNat_subAddr hs
  have hwa := workAreaBytes_le
  have hdp := decodedWords_pos bytes.length
  have hce : NativeVm.Entry.ctxWords = 12 := (rfl)
  have ap : ∀ (x : UInt64) (sz : Nat),
      (⟨x.toBitVec, sz⟩ : Region) ∈ usedRegions m0.regs.X0 a bytes.length bytecode.length →
      0 < sz → x.toNat + sz ≤ m0.regs.SP.toBitVec.toNat - 19344 ∨
        m0.regs.SP.toBitVec.toNat ≤ x.toNat := fun x sz hr hp ↦ by
    have h := hapS _ hr hp
    unfold NativeRustcVm.Apart at h
    rw [hsb, hS] at h
    have e : x.toNat = x.toBitVec.toNat := rfl
    rw [e]
    exact h.imp id (fun h ↦ by simp only at h; omega)
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
  have a0 := ap m0.regs.X0 (8 * NativeVm.Entry.ctxWords) (by simp [usedRegions]) (by omega)
  have a3 := ap a.decoded (8 * decodedWords bytes.length) (by simp [usedRegions]) (by omega)
  have a4 := ap a.work (8 * NativeVm.Entry.workWords) (by simp [usedRegions])
    (by have h := hwa; unfold workAreaBytes NativeRustcVm.Top.workAreaWords at h; omega)
  refine ⟨hs, hal, toNat_subAddr (by omega), hsb, fx, a0, fd, by omega, by omega, by omega,
    by omega, by omega, by omega, fb, fun hn ↦ ?_, dbd,
    (fun hn ↦ by have := dbk hn; omega), fw, fun hL ↦ ?_,
    dwd, (fun hL ↦ by have := dwk hL; omega)⟩
  · exact ap a.bytecode (8 * bytecode.length) (by simp [usedRegions]) (by omega)
  · exact ap a.wire bytes.length (by simp [usedRegions]) hL

variable [Host] {k : Nat}

theorem hb (i : Nat) {ds : List Directive} (hp : Placed code k) (h : ds.IsInfixAt code i)
    (hne : ds ≠ []) : ds.IsInfixAt Host.prog (k + i) :=
  h.trans hp.1 hne

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.LeanvmVerify.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.LeanvmVerify.entryOffset) NativeRustcVmArm.Vm.LeanvmVerify.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.LeanvmVerify.label_1 = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b1Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.LeanvmVerify.b1Offset) NativeRustcVmArm.Vm.LeanvmVerify.label_1_at
theorem lbl_2 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.LeanvmVerify.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b2Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.LeanvmVerify.b2Offset) NativeRustcVmArm.Vm.LeanvmVerify.label_2_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.LeanvmVerify.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b3Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.LeanvmVerify.b3Offset) NativeRustcVmArm.Vm.LeanvmVerify.label_3_at
theorem lbl_10 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.LeanvmVerify.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b10Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.LeanvmVerify.b10Offset) NativeRustcVmArm.Vm.LeanvmVerify.label_10_at
theorem lbl_13 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.LeanvmVerify.label_13 = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b15Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.LeanvmVerify.b15Offset) NativeRustcVmArm.Vm.LeanvmVerify.label_13_at
theorem lbl_14 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.LeanvmVerify.label_14 = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b17Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.LeanvmVerify.b17Offset) NativeRustcVmArm.Vm.LeanvmVerify.label_14_at

end

end NativeRustcVmArm.Top.Leanvm
