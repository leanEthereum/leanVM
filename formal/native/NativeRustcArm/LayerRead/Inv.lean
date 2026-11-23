module

public import NativeRustcArm.LayerRead.Glue
public import NativeRustcArm.Spec.LayerRead
public import NativeRustcArm.Code.Xmss.LayerRead

/-!
# `LayerSignature::read`: proof states

The descriptor contains a data pointer and remaining length. The chain loop
copies 58 values to the upper part of the frame, then `memcpy` moves them to
its base. The unrolled path occupies that upper part afterward. The randomizer
is read from the preserved input only when writing the final output.
-/

namespace NativeRustcArm.Xmss.LayerRead

open NativeRustcArm.Sym

@[expose] public section

/-- The frame's base: SP after the prologue. -/
def frame (m₀ : MachineData) : BitVec 64 := stackBelow m₀ layerReadStack

/-- The output. -/
def out (m₀ : MachineData) : BitVec 64 := m₀.regs.X0.toBitVec

/-- The cursor. -/
def cur (m₀ : MachineData) : BitVec 64 := m₀.regs.X1.toBitVec

/-- The slice's initial data pointer. -/
def sig (m₀ : MachineData) : BitVec 64 := LayerReadPre.data m₀

/-- The slice's initial remaining byte count. -/
def remaining (m₀ : MachineData) : Nat := LayerReadPre.remaining m₀

/-- Saved words; slot three is padding and is not restored. -/
def saveRegs : List XReg := [.X29, .X30, .X28, .X0, .X24, .X23, .X22, .X21, .X20, .X19]

/-- The randomizer. -/
def rand (m₀ : MachineData) : List UInt8 := NativeRustc.slice (LayerReadPre.bytes m₀) 0 16

/-- Chain value `j`. -/
def chainSlot (m₀ : MachineData) (j : Nat) : List UInt8 :=
  NativeRustc.slice (LayerReadPre.bytes m₀) (16 + 16 * j) 16

/-- Path node `j`. -/
def pathSlot (m₀ : MachineData) (j : Nat) : List UInt8 :=
  NativeRustc.slice (LayerReadPre.bytes m₀) (944 + 16 * j) 16

/-- The memory a run may change before writing the output. -/
def Scratch (m₀ : MachineData) (p : BitVec 64) : Prop :=
  InRange (frame m₀) layerReadStack p ∨ InRange (cur m₀) 16 p

/-- Facts preserved from the chain loop through the last copy. -/
structure Common (m₀ m : MachineData) : Prop where
  x19 : (m.regs.getXReg .X19).toBitVec = out m₀
  x20 : (m.regs.getXReg .X20).toBitVec = cur m₀
  x21 : (m.regs.getXReg .X21).toBitVec = sig m₀
  keep : ∀ r ∈ [XReg.X25, .X26, .X27, .X28], m.regs.getXReg r = m₀.regs.getXReg r
  x29 : (m.regs.getXReg .X29).toBitVec = frame m₀ + BitVec.ofNat 64 1856
  sp : m.regs.SP.toBitVec = frame m₀
  same : SameOutside m₀.dmem m.dmem (Scratch m₀)
  kept : Kept m₀.dmem m.dmem
  save : ∀ j < 10, j ≠ 3 → BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 (1856 + 8 * j))
    (regBytes (m₀.regs.getXReg (saveRegs.getD j .X0)).toBitVec)

/-- At the head of the loop over the chain values, before value `i`. -/
structure LoopAt (m₀ m : MachineData) (i : Nat) : Prop where
  common : Common m₀ m
  x8 : (m.regs.getXReg .X8).toBitVec = BitVec.ofNat 64 ((remaining m₀ - 16) / 16 - i)
  x9 : (m.regs.getXReg .X9).toBitVec = frame m₀ + BitVec.ofNat 64 928
  x22 : (m.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 (remaining m₀ - 16 * i)
  x23 : (m.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 (16 * i)
  chain : ∀ j < i, BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 (928 + 16 * j)) (chainSlot m₀ j)

/-- The facts of the precondition the proof uses, as arithmetic on addresses. -/
structure Pre (m₀ : MachineData) : Prop where
  sp16 : m₀.regs.SP.toNat % 16 = 0
  spLe : layerReadStack ≤ m₀.regs.SP.toNat
  frameNat : (frame m₀).toNat = m₀.regs.SP.toNat - layerReadStack
  frameMapped : Mapped m₀.dmem (frame m₀) layerReadStack
  remaining : 1200 ≤ remaining m₀
  outMapped : Mapped m₀.dmem (out m₀) 1200
  curMapped : Mapped m₀.dmem (cur m₀) 16
  sigMapped : Mapped m₀.dmem (sig m₀) 1200
  outNW : (out m₀).toNat + 1200 ≤ 2 ^ 64
  curNW : (cur m₀).toNat + 16 ≤ 2 ^ 64
  sigNW : (sig m₀).toNat + 1200 ≤ 2 ^ 64
  outF : Apart (out m₀) 1200 (frame m₀) layerReadStack
  curF : Apart (cur m₀) 16 (frame m₀) layerReadStack
  sigF : Apart (sig m₀) 1200 (frame m₀) layerReadStack
  outCur : Apart (out m₀) 1200 (cur m₀) 16
  outSig : Apart (out m₀) 1200 (sig m₀) 1200
  curSig : Apart (cur m₀) 16 (sig m₀) 1200

theorem pre_of {m₀ : MachineData} (h : LayerReadPre m₀) : Pre m₀ := by
  obtain ⟨⟨h16, hle, hmap⟩, hpos, ⟨ho1, ho2, ho3⟩, ⟨hc1, hc2, hc3⟩, ⟨hs1, hs2, hs3⟩, hoc, hos, hcs⟩ := h
  have hF : (frame m₀).toNat = m₀.regs.SP.toNat - layerReadStack := by
    unfold frame stackBelow
    rw [BitVec.toNat_sub]
    have := m₀.regs.SP.toBitVec.isLt
    simp only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat] at *
    unfold layerReadStack at *
    omega
  exact ⟨h16, hle, hF, hmap, hpos, ho1, hc1, hs1, ho2, hc2, hs2, ho3, hc3, hs3, hoc, hos, hcs⟩

theorem Pre.frameNW {m₀ : MachineData} (P : Pre m₀) : NoWrap (frame m₀) layerReadStack := by
  have := m₀.regs.SP.toBitVec.isLt
  have := P.frameNat
  have := P.spLe
  unfold NoWrap
  simp only [UInt64.toNat_toBitVec] at *
  omega

theorem Pre.frame16 {m₀ : MachineData} (P : Pre m₀) : (frame m₀).toNat % 16 = 0 := by
  rw [P.frameNat]
  have := P.sp16
  have := P.spLe
  unfold layerReadStack at *
  omega

/-- The signature's bytes are not scratch. -/
theorem Pre.sig_not_scratch {m₀ : MachineData} (P : Pre m₀) {x : Nat} (hx : x < 1200) :
    ¬Scratch m₀ (sig m₀ + BitVec.ofNat 64 x) := by
  rintro (h | h)
  · exact not_inRange_of_apart P.frameNW
      ((P.sigF.symm.sub_right P.sigNW (by omega) (by omega))) h
  · exact not_inRange_of_apart P.curNW ((P.curSig.sub_right P.sigNW (by omega) (by omega))) h

/-- After the loop over the chain values. -/
structure LoopDone (m₀ m : MachineData) : Prop where
  common : Common m₀ m
  x22 : (m.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 (remaining m₀ - 928)
  x23 : (m.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 928
  x24 : (m.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (remaining m₀ - 944)
  chain : ∀ j < 58, BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 (928 + 16 * j)) (chainSlot m₀ j)

theorem remaining_lt (m₀ : MachineData) : remaining m₀ < 2 ^ 64 :=
  (BitVec.ofNat 64 (NativeRustc.leNat (bytesOf m₀.dmem (m₀.regs.X1.toBitVec + 8) 8))).isLt

theorem Pre.slice_length {m₀ : MachineData} (_P : Pre m₀) {x : Nat} (hx : x + 16 ≤ 1200) :
    (NativeRustc.slice (LayerReadPre.bytes m₀) x 16).length = 16 := by
  simp [NativeRustc.slice, LayerReadPre.bytes, length_bytesOf]
  omega

theorem Pre.rand_length {m₀ : MachineData} (P : Pre m₀) : (rand m₀).length = 16 :=
  P.slice_length (by omega)

theorem Pre.chainSlot_length {m₀ : MachineData} (P : Pre m₀) {j : Nat} (hj : j < 58) :
    (chainSlot m₀ j).length = 16 :=
  P.slice_length (by omega)

theorem Pre.pathSlot_length {m₀ : MachineData} (P : Pre m₀) {j : Nat} (hj : j < 16) :
    (pathSlot m₀ j).length = 16 :=
  P.slice_length (by omega)

/-- The chain values' bytes. -/
def chainBytes (m₀ : MachineData) : List UInt8 := ((List.range 58).map (chainSlot m₀)).flatten

/-- The path's bytes. -/
def pathBytes (m₀ : MachineData) : List UInt8 := ((List.range 16).map (pathSlot m₀)).flatten

/-- `Common` after a step that keeps the callee-saved registers and SP. -/
theorem common_of_saved {m₀ m m' : MachineData} (C : Common m₀ m) (hs : Saved m m')
    (hsame : SameOutside m₀.dmem m'.dmem (Scratch m₀))
    (hsave : ∀ j < 10, j ≠ 3 → BytesAt m'.dmem (frame m₀ + BitVec.ofNat 64 (1856 + 8 * j))
      (regBytes (m₀.regs.getXReg (saveRegs.getD j .X0)).toBitVec)) : Common m₀ m' where
  x19 := by rw [hs.1 .X19 rfl]; exact C.x19
  x20 := by rw [hs.1 .X20 rfl]; exact C.x20
  x21 := by rw [hs.1 .X21 rfl]; exact C.x21
  keep r hr := by
    have := C.keep r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hs.1 r (by rcases hr with rfl | rfl | rfl | rfl <;> rfl)]
    exact this
  x29 := by rw [hs.1 .X29 rfl]; exact C.x29
  sp := by rw [hs.2.1]; exact C.sp
  same := hsame
  kept := C.kept.trans hs.2.2
  save := hsave

/-- Saved state across a call that changes scratch but not the register spill slots. -/
theorem Common.transfer {m₀ m m' : MachineData} (_P : Pre m₀) (C : Common m₀ m) (hs : Saved m m')
    {R : BitVec 64 → Prop} (hsame : SameOutside m.dmem m'.dmem R) (hR : ∀ p, R p → Scratch m₀ p)
    (hsave : ∀ j < 10, j ≠ 3 → ∀ t < 8, ¬R (frame m₀ + BitVec.ofNat 64 (1856 + 8 * j) + BitVec.ofNat 64 t)) :
    Common m₀ m' where
  x19 := by rw [hs.1 .X19 rfl]; exact C.x19
  x20 := by rw [hs.1 .X20 rfl]; exact C.x20
  x21 := by rw [hs.1 .X21 rfl]; exact C.x21
  keep r hr := by
    have := C.keep r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hs.1 r (by rcases hr with rfl | rfl | rfl | rfl <;> rfl)]
    exact this
  x29 := by rw [hs.1 .X29 rfl]; exact C.x29
  sp := by rw [hs.2.1]; exact C.sp
  same := (C.same.trans hsame).mono fun p hp => hp.elim id (hR p)
  kept := C.kept.trans hs.2.2
  save j hj hj3 := (C.save j hj hj3).sameOutside hsame fun t ht =>
    hsave j hj hj3 t (by rw [length_regBytes] at ht; exact ht)

/-- After the `memcpy` of the chain values. -/
structure MidAt (m₀ m : MachineData) : Prop where
  common : Common m₀ m
  x22 : (m.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 (remaining m₀ - 928)
  x23 : (m.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 928
  x24 : (m.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (remaining m₀ - 944)
  chain : BytesAt m.dmem (frame m₀) (chainBytes m₀)

/-- At the `memcpy` of the path to the output. -/
structure PathCall (m₀ m : MachineData) : Prop where
  common : Common m₀ m
  x0 : (m.regs.getXReg .X0).toBitVec = out m₀
  x1 : (m.regs.getXReg .X1).toBitVec = frame m₀ + BitVec.ofNat 64 928
  x2 : (m.regs.getXReg .X2).toBitVec = BitVec.ofNat 64 256
  cursorData : BytesAt m.dmem (cur m₀) (regBytes (sig m₀ + 1200))
  cursorLength : BytesAt m.dmem (cur m₀ + 8) (regBytes (BitVec.ofNat 64 (remaining m₀ - 1200)))
  chain : BytesAt m.dmem (frame m₀) (chainBytes m₀)
  path : BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 928) (pathBytes m₀)

end

end NativeRustcArm.Xmss.LayerRead
