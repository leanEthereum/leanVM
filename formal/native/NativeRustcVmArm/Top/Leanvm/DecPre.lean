module

public import NativeRustcVmArm.Top.Leanvm.Checks
public import NativeRustcVmArm.Top.Verify.Basic
public import NativeRustcVmArm.Rodata.Keccak

/-!
# `leanvm_verify`: `decode`'s precondition

Before `bl decode`, with the frame's body and `decode`'s arguments in X0 to X4 (the wire, `L`, the
decoded area, `decodedWords L`, the working area), `decode`'s precondition holds (`decPre`); the
wire's bytes at its address (`wireBytes`).
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LeanvmVerify NativeVm
open NativeRustcVm (WordAt WordsAt Region)
open NativeRustcVm.Top (workAreaBytes entryRegions ApartFrom Aligned)
open NativeVm.Transcript (wd ctxEnd)

public section

theorem natToU64 {x : Nat} (h : x < 2 ^ 64) : x.toUInt64.toNat = x := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

theorem workBytes_le : NativeRustcVm.Wire.workBytes ≤ workAreaBytes := by decide

/-- The wire's bytes at its address. -/
theorem wireBytes {d : DataMem} {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {ctx : UInt64}
    (hin : NativeVm.Entry.EntryPre (NativeRustcVm.wordView d) ctx a bytes bytecode pub) :
    BytesAt d a.wire.toBitVec bytes ∧ Mapped d a.wire.toBitVec (8 * NativeVm.Entry.wireWords bytes.length) := by
  obtain ⟨ws, hold, htake, hws⟩ := hin.wire
  have hW : WordsAt d a.wire.toBitVec ws := NativeRustcVm.wordsAt_of_wordView hws
  have hl : ws.length = NativeVm.Entry.wireWords bytes.length := hold.1
  refine ⟨?_, ?_⟩
  · have := NativeRustcVm.BytesAt.take hW bytes.length
    rw [← htake]
    exact this
  · have := NativeRustcVm.WordsAt.mapped hW
    rw [hl] at this
    exact this

/-- **`decode`'s precondition.** -/
theorem decPre [Labels] {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {m0 st : MachineData}
    (hpre : LeanvmVerifyPre a bytes bytecode pub m0)
    (hB : Body m0 128 slots (InStack m0 leanvmVerifyStack) st)
    (hx0 : 0 < bytes.length → st.regs.X0 = a.wire) (hx1 : st.regs.X1 = bytes.length.toUInt64)
    (hx2 : st.regs.X2 = a.decoded) (hx3 : st.regs.X3 = (decodedWords bytes.length).toUInt64)
    (hx4 : st.regs.X4 = a.work) : DecodePre st := by
  have g := geo_of hpre
  obtain ⟨⟨-, -, hmap⟩, hrod, hin, -, -, hapR⟩ := hpre
  have hs := g.s
  have hF := g.F
  have hsb : (m0.regs.SP.toBitVec - BitVec.ofNat 64 leanvmVerifyStack).toNat =
      m0.regs.SP.toBitVec.toNat - 19344 := g.sb
  have hS := leanvmVerifyStack_eq
  have hsl := m0.regs.SP.toBitVec.isLt
  have hsp : st.regs.SP.toBitVec = frameOf m0 := hB.sp
  have hDS : decodeStack = 1280 := rfl
  have hwb : NativeRustcVm.Wire.workBytes = 483584 := rfl
  have hwa : workAreaBytes = 495552 := rfl
  have hL := hin.L32
  have hdp := decodedWords_pos bytes.length
  have gd := g.dec
  have gdN := g.decN
  have gw := g.work
  have gwN := g.workN
  have gdw := g.decWork
  have hsbD : (stackBelow st decodeStack).toNat = m0.regs.SP.toBitVec.toNat - 1408 := by
    show (st.regs.SP.toBitVec - BitVec.ofNat 64 decodeStack).toNat = _
    rw [hsp, hDS, toNat_subAddr (by rw [hF]; omega), hF]; omega
  have hrc : RcAt st decodeStack :=
    RodataAt.rcAt (NativeRustcVmArm.Top.Verify.rodataAt_body hrod hB (by rw [hS]; omega) hsp
      (by rw [hS, hDS]; decide))
  have hX1 : st.regs.X1.toNat = bytes.length := by rw [hx1]; exact natToU64 (by omega)
  have hX3 : st.regs.X3.toNat = decodedWords bytes.length := by
    rw [hx3]; exact natToU64 (by omega)
  have hdM : Mapped st.dmem a.decoded.toBitVec (8 * decodedWords bytes.length) :=
    Mapped.kept (NativeRustcVm.mapped_of_wordView hin.decSome) hB.kept
  have hwM : Mapped st.dmem a.work.toBitVec (8 * NativeVm.Entry.workWords bytecode.length) :=
    Mapped.kept (NativeRustcVm.mapped_of_wordView hin.workSome) hB.kept
  have hwle := workAreaBytes_le bytecode.length
  -- The round constants apart from the stack and the areas.
  have rcS : NativeRustcVm.Apart (stackBelow st decodeStack) decodeStack rcAddr 192 :=
    NativeRustcVm.Apart.symm hrc.2.2
  have rcD : NativeRustcVm.Apart a.decoded.toBitVec (8 * decodedWords bytes.length) rcAddr 192 :=
    hapR ⟨a.decoded.toBitVec, _⟩ (by simp [entryRegions])
      (by show 0 < 8 * decodedWords bytes.length; omega) .keccakRC
  have rcW : NativeRustcVm.Apart a.work.toBitVec (8 * NativeVm.Entry.workWords bytecode.length) rcAddr 192 :=
    hapR ⟨a.work.toBitVec, _⟩ (by simp [entryRegions])
      (by show 0 < 8 * NativeVm.Entry.workWords bytecode.length; omega) .keccakRC
  have ed : a.decoded.toBitVec.toNat = a.decoded.toNat := rfl
  have ew : a.work.toBitVec.toNat = a.work.toNat := rfl
  have ewi : a.wire.toBitVec.toNat = a.wire.toNat := rfl
  unfold NativeRustcVm.Apart at rcS rcD rcW
  refine ⟨⟨?_, ?_, ?_⟩, hrc, by rw [hX1]; exact hL, by rw [hX1, hX3], ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, ?_, fun hL0 ↦ ?_⟩
  · show st.regs.SP.toBitVec.toNat % 16 = 0
    rw [hsp, hF]; have := g.al; omega
  · show decodeStack ≤ st.regs.SP.toBitVec.toNat
    rw [hsp, hF, hDS]; omega
  · show Mapped st.dmem (st.regs.SP.toBitVec - BitVec.ofNat 64 decodeStack) decodeStack
    refine Mapped.kept (Mapped.within hmap (by rw [hsb]; omega) ?_ ?_) hB.kept
    · rw [hsb, hsp, hDS, toNat_subAddr (by rw [hF]; omega), hF]; omega
    · rw [hsb, hsp, hDS, toNat_subAddr (by rw [hF]; omega), hF]; omega
  · show Mapped st.dmem st.regs.X0.toBitVec st.regs.X1.toNat
    rw [hX1]
    by_cases h0 : bytes.length = 0
    · rw [h0]; exact fun i hi ↦ absurd hi (Nat.not_lt_zero _)
    · rw [hx0 (by omega)]
      exact NativeRustcVm.Mapped.mono (Mapped.kept (wireBytes hin).2 hB.kept)
        (by unfold NativeVm.Entry.wireWords; omega)
  · show st.regs.X0.toBitVec.toNat + st.regs.X1.toNat ≤ 2 ^ 64
    rw [hX1]
    by_cases h0 : bytes.length = 0
    · rw [h0]; have := st.regs.X0.toBitVec.isLt; omega
    · rw [hx0 (by omega)]; have := g.wireN; unfold NativeVm.Entry.wireWords at this; omega
  · show Mapped st.dmem st.regs.X2.toBitVec (8 * st.regs.X3.toNat)
    rw [hx2, hX3]; exact hdM
  · show st.regs.X2.toBitVec.toNat + 8 * st.regs.X3.toNat ≤ 2 ^ 64
    rw [hx2, hX3]; exact gdN
  · show Mapped st.dmem st.regs.X4.toBitVec NativeRustcVm.Wire.workBytes
    rw [hx4]; exact NativeRustcVm.Mapped.mono hwM (by omega)
  · show st.regs.X4.toBitVec.toNat + NativeRustcVm.Wire.workBytes ≤ 2 ^ 64
    rw [hx4]; omega
  · show NativeRustcVm.Disjoint [⟨stackBelow st decodeStack, decodeStack⟩, ⟨rcAddr, 192⟩,
      ⟨st.regs.X2.toBitVec, 8 * st.regs.X3.toNat⟩, ⟨st.regs.X4.toBitVec, NativeRustcVm.Wire.workBytes⟩]
    rw [hx2, hX3, hx4]
    refine disjoint_four ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp only [NativeRustcVm.Apart] <;>
      omega
  · rw [hX1] at hL0
    have gwi := g.wire hL0
    have gwd := g.wireDec
    have gwk := g.wireWork
    have rcI : NativeRustcVm.Apart a.wire.toBitVec (8 * NativeVm.Entry.wireWords bytes.length) rcAddr 192 :=
      hapR ⟨a.wire.toBitVec, _⟩ (by simp [entryRegions])
        (by show 0 < 8 * NativeVm.Entry.wireWords bytes.length; unfold NativeVm.Entry.wireWords; omega) .keccakRC
    unfold NativeRustcVm.Apart at rcI
    have hww : bytes.length ≤ 8 * NativeVm.Entry.wireWords bytes.length := by unfold NativeVm.Entry.wireWords; omega
    show NativeRustcVm.Disjoint [⟨stackBelow st decodeStack, decodeStack⟩, ⟨rcAddr, 192⟩,
      ⟨st.regs.X0.toBitVec, st.regs.X1.toNat⟩, ⟨st.regs.X2.toBitVec, 8 * st.regs.X3.toNat⟩,
      ⟨st.regs.X4.toBitVec, NativeRustcVm.Wire.workBytes⟩]
    rw [hx0 hL0, hX1, hx2, hX3, hx4]
    refine disjoint_five ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp only [NativeRustcVm.Apart] <;>
      omega

end

end NativeRustcVmArm.Top.Leanvm
