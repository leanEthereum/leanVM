module

public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfComputedBytecodeValue.Names
public import NativeRustcVmArm.Arrays.MultilinearEvalByOfComputedBytecodeValue.Exec
public import NativeRustcVmArm.Arrays.MultilinearEvalBy.Frame

/-!
# `multilinear_eval_by` (`computed_bytecode_value`'s closure): the loops

The frame (`Fr`: the body, `point + 8` at `fb + 24`, the flags `0` or `1`); the outer loop's head
`.LMultilinearEvalByOfComputedBytecodeValue_4` (`Outer`: `i` entries streamed, the pending entries the
frame's) and the inner loop's `.LMultilinearEvalByOfComputedBytecodeValue_8` (`Inner`: entry `i`
carried to level `k` with value `v` in X22, X23, `Mle.cont` the target). A turn of the inner loop
(`inner`): a pending entry pairs with `v` (`pair`, two calls of `EW::mul`) or `v` waits at level
`k` (`push`); the outer loop's set-up (`outer`) loads `words[i]`; the epilogue (`finish`). Inside
the loops `|point| < 64` and there are words (`LPre`).
-/

namespace NativeRustcVmArm.Arrays.MleOfComputedBytecodeValue

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue
open NativeVm.Model NativeRustcArm NativeRustcVmArm.Arrays.MleFrame
open NativeRustcVm (wordOf wordsOf ewOf ewsOf)
open NativeRustcVm.Mle (stream cont setP)

public section

/-- The point. -/
abbrev pts (m0 : MachineData) : List EW := ewsOf m0.dmem m0.regs.X3.toBitVec m0.regs.X4.toNat
/-- The entries: the words, each in limb `0`. -/
abbrev ents (m0 : MachineData) : List EW :=
  (wordsOf m0.dmem m0.regs.X1.toBitVec m0.regs.X2.toNat).map EW.ofK
/-- The streamed value. -/
abbrev target (m0 : MachineData) : EW := stream (pts m0) (ents m0) fun _ ↦ none
/-- `|words|` (`= n`). -/
abbrev nn (m0 : MachineData) : Nat := m0.regs.X2.toNat
/-- `|point|`. -/
abbrev mm (m0 : MachineData) : Nat := m0.regs.X4.toNat

theorem target_eq (m0 : MachineData) :
    target m0 = multilinearEval (wordSliceE m0 m0.regs.X1 m0.regs.X2)
      (slice m0 m0.regs.X3 m0.regs.X4) :=
  NativeRustcVm.Mle.stream_eq _ _

/-- The precondition inside the loops: `|point| < 64`, the words apart from the stack. -/
@[expose] def LPre (m0 : MachineData) : Prop :=
  StackOk m0 mleStack ∧ m0.regs.X0 = m0.regs.X2 ∧ m0.regs.X4.toNat < 64 ∧
    (Readable m0 m0.regs.X1.toBitVec (8 * m0.regs.X2.toNat) ∧
      OffStack m0 m0.regs.X1.toBitVec (8 * m0.regs.X2.toNat) mleStack) ∧
    SliceOk m0 m0.regs.X3 m0.regs.X4 mleStack

/-- The frame in the loops. -/
structure Fr (m0 s : MachineData) : Prop where
  body : Body m0 1232 mleStack slots 0 0 s
  w24 : (wordOf s.dmem (fbOf m0 + BitVec.ofNat 64 24)).toBitVec =
    m0.regs.X3.toBitVec + BitVec.ofNat 64 8
  flags : FlagsOk s.dmem (fbOf m0)

theorem Fr.call {m0 st st' : MachineData} (h : Fr m0 st) (hS : StackOk m0 mleStack)
    (hpost : EWMulPost st st') :
    Fr m0 st' ∧ pendOf st'.dmem (fbOf m0) = pendOf st.dmem (fbOf m0) := by
  have hj : ∀ j, j < 1232 → st'.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) =
      st.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) := fun j hj ↦ frame_call h.body hpost hj
  refine ⟨⟨h.body.call hS (by decide) (by decide) hpost, ?_,
    flagsOk_congr h.flags fun j _ hj' ↦ hj j (by omega)⟩, pendOf_congr fun j _ hj' ↦ hj j (by omega)⟩
  rw [NativeRustcVm.wordOf_congr (d := st.dmem) fun i hi ↦ by
    rw [NativeRustcVm.addr_add]; exact hj _ (by omega)]
  exact h.w24

theorem Fr.block [Labels] {m0 st st' : MachineData} {env : Env} {S₀ S₁ : SState} (h : Fr m0 st)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hk : keepsAll S₀ S₁ [] = true) : Fr m0 st' ∧ st'.dmem = st.dmem := by
  have hk' : keepsAll S₀ S₁ (calleeRegs.filter fun r ↦ !inSlots slots r) = true := by
    rw [kept_nil.1]; exact hk
  have hmem : S₁.mem = [] := by
    simp only [keepsAll, Bool.and_eq_true, List.isEmpty_iff] at hk; exact hk.2
  have hdm : st'.dmem = st.dmem := (hm.dmem_eq hwf hmem).trans hd.symm
  refine ⟨⟨h.body.of_block hm₀ hm hwf hd hk', ?_, ?_⟩, hdm⟩
  · rw [hdm]; exact h.w24
  · rw [hdm]; exact h.flags

/-- **The outer loop's head**, `i` entries streamed. -/
structure Outer (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  fr : Fr m0 s
  hi : i < nn m0
  pos : 0 < mm m0
  x29 : s.regs.X29.toNat = i
  val : stream (pts m0) ((ents m0).drop i) (pendOf s.dmem (fbOf m0)) = target m0

/-- **The inner loop's head**: entry `i` carried to level `kk`. -/
structure Inner (m0 : MachineData) (i kk : Nat) (s : MachineData) : Prop where
  fr : Fr m0 s
  hi : i < nn m0
  hk : kk < mm m0
  x21 : s.regs.X21.toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * kk + 8)
  x20 : s.regs.X20.toBitVec = fbOf m0 + BitVec.ofNat 64 (1072 + kk)
  x28 : s.regs.X28.toBitVec = fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk)
  x19 : s.regs.X19.toNat = mm m0 - kk
  x29 : s.regs.X29.toNat = i + 1
  val : cont (pts m0) ((ents m0).drop (i + 1)) (pendOf s.dmem (fbOf m0)) kk
    ⟨s.regs.X22, s.regs.X23⟩ = target m0

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b9Offset) :=
  b9_in_code.trans hp.1 (by simp [b9])
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b10Offset) :=
  b10_in_code.trans hp.1 (by simp [b10])
theorem hb11 (hp : Placed code k) : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b11Offset) :=
  b11_in_code.trans hp.1 (by simp [b11])
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b12Offset) :=
  b12_in_code.trans hp.1 (by simp [b12])
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b13Offset) :=
  b13_in_code.trans hp.1 (by simp [b13])
theorem hb14 (hp : Placed code k) : b14.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b14Offset) :=
  b14_in_code.trans hp.1 (by simp [b14])
theorem hb15 (hp : Placed code k) : b15.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b15Offset) :=
  b15_in_code.trans hp.1 (by simp [b15])
theorem hb16 (hp : Placed code k) : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b16Offset) :=
  b16_in_code.trans hp.1 (by simp [b16])
theorem hb17 (hp : Placed code k) : b17.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b17Offset) :=
  b17_in_code.trans hp.1 (by simp [b17])
theorem hb18 (hp : Placed code k) : b18.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b18Offset) :=
  b18_in_code.trans hp.1 (by simp [b18])

theorem lbl_entry (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b0Offset) := hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.entryOffset) NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.entry_at
theorem lbl_4 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b4Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b4Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_4_at
theorem lbl_7 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b7Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b7Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_7_at
theorem lbl_8 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b8Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b8Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_8_at
theorem lbl_10 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b13Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b13Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_10_at
theorem lbl_11 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_11 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b15Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b15Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_11_at
theorem lbl_13 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_13 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b17Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b17Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_13_at
theorem lbl_14 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_14 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b18Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b18Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.label_14_at

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ MleOfComputedBytecodeValuePost m0 s.data

/-- **The epilogue** (`b18`): the value in X22, X23 returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 mleStack)
    {sl : List (Nat × XReg)} (hres : restores sl 1232 (after b18 frameS) = true)
    (hx30 : XReg.X30 ∈ sl.map (·.2)) {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b18Offset))
    (hb : Body m0 1232 mleStack sl 0 0 s.data)
    (hv : (⟨s.data.regs.X22, s.data.regs.X23⟩ : EW) = target m0) :
    Eventually (step1 Host.exe) (Post m0) s := by
  obtain ⟨hwf, hm⟩ := hb.exit_match hS (by decide) rfl
  refine exec_at (hb18 hp) run_b18 hwf hpc hm fun s' hm' hpc' ↦ ?_
  obtain ⟨hsaved, hx30', hdm⟩ := hb.saved hm' hwf hx30 (after_eq run_b18 ▸ hres) rfl
  simp only [PcOk] at hpc'
  refine .done _ ⟨by rw [hpc']; simp only [retOf, hx30'], ?_,
    fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  rw [← target_eq, ← hv]
  show (⟨s'.data.regs.getXReg .X0, s'.data.regs.getXReg .X1⟩ : EW) =
    ⟨s.data.regs.getXReg .X22, s.data.regs.getXReg .X23⟩
  rw [reg_of hm' (r := .X0) rfl, reg_of hm' (r := .X1) rfl]
  rfl

end

end NativeRustcVmArm.Arrays.MleOfComputedBytecodeValue
