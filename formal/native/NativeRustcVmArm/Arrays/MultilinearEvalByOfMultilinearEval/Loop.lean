module

public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Arrays.MultilinearEvalByOfMultilinearEval.Exec
public import NativeRustcVmArm.Arrays.MultilinearEvalBy.Frame

/-!
# `multilinear_eval_by` (`multilinear_eval`'s closure): the loops

The frame (`Fr`: the body, `point + 8` at `fb + 24`, the flags `0` or `1`); the outer loop's head
`.LMultilinearEvalByOfMultilinearEval_3` (`Outer`: `i` entries streamed, the pending entries the
frame's) and the inner loop's `.LMultilinearEvalByOfMultilinearEval_7` (`Inner`: entry `i`
carried to level `k` with value `v` in X23, X24, `Mle.cont` the target). A turn of the inner loop
(`inner`): a pending entry pairs with `v` (`pair`, two calls of `EW::mul`) or `v` waits at level
`k` (`push`); the outer loop's set-up (`outer`) loads `mle[i]`; the epilogue (`finish`).
-/

namespace NativeRustcVmArm.Arrays.MleOfMultilinearEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval
open NativeVm.Model NativeRustcArm NativeRustcVmArm.Arrays.MleFrame
open NativeRustcVm (wordOf ewOf ewsOf)
open NativeRustcVm.Mle (stream cont setP)

public section

/-- The point. -/
abbrev pts (m0 : MachineData) : List EW := ewsOf m0.dmem m0.regs.X3.toBitVec m0.regs.X4.toNat
/-- The entries. -/
abbrev ents (m0 : MachineData) : List EW := ewsOf m0.dmem m0.regs.X1.toBitVec m0.regs.X2.toNat
/-- The streamed value. -/
abbrev target (m0 : MachineData) : EW := stream (pts m0) (ents m0) fun _ ↦ none
/-- `|mle|` (`= n`). -/
abbrev nn (m0 : MachineData) : Nat := m0.regs.X2.toNat
/-- `|point|`. -/
abbrev mm (m0 : MachineData) : Nat := m0.regs.X4.toNat

theorem target_eq (m0 : MachineData) :
    target m0 = multilinearEval (slice m0 m0.regs.X1 m0.regs.X2) (slice m0 m0.regs.X3 m0.regs.X4) :=
  NativeRustcVm.Mle.stream_eq _ _

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
  x19 : s.regs.X19.toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * kk + 8)
  x20 : s.regs.X20.toBitVec = fbOf m0 + BitVec.ofNat 64 (1072 + kk)
  x21 : s.regs.X21.toBitVec = fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk)
  x22 : s.regs.X22.toNat = mm m0 - kk
  x29 : s.regs.X29.toNat = i + 1
  val : cont (pts m0) ((ents m0).drop (i + 1)) (pendOf s.dmem (fbOf m0)) kk
    ⟨s.regs.X23, s.regs.X24⟩ = target m0

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b9Offset) :=
  b9_in_code.trans hp.1 (by simp [b9])
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b10Offset) :=
  b10_in_code.trans hp.1 (by simp [b10])
theorem hb11 (hp : Placed code k) : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b11Offset) :=
  b11_in_code.trans hp.1 (by simp [b11])
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b12Offset) :=
  b12_in_code.trans hp.1 (by simp [b12])
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b13Offset) :=
  b13_in_code.trans hp.1 (by simp [b13])
theorem hb14 (hp : Placed code k) : b14.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b14Offset) :=
  b14_in_code.trans hp.1 (by simp [b14])
theorem hb15 (hp : Placed code k) : b15.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b15Offset) :=
  b15_in_code.trans hp.1 (by simp [b15])
theorem hb16 (hp : Placed code k) : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b16Offset) :=
  b16_in_code.trans hp.1 (by simp [b16])
theorem hb17 (hp : Placed code k) : b17.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b17Offset) :=
  b17_in_code.trans hp.1 (by simp [b17])

theorem lbl_entry (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b0Offset) := hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryOffset) NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entry_at
theorem lbl_3 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b3Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b3Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_3_at
theorem lbl_6 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_6 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b6Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b6Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_6_at
theorem lbl_7 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b7Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b7Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_7_at
theorem lbl_9 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_9 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b12Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b12Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_9_at
theorem lbl_10 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b14Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b14Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_10_at
theorem lbl_12 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_12 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b16Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b16Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_12_at
theorem lbl_13 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_13 = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b17Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b17Offset) NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.label_13_at

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ MleOfMultilinearEvalPost m0 s.data

/-- **The epilogue** (`b17`): the value in X23, X24 returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 mleStack)
    {sl : List (Nat × XReg)} (hres : restores sl 1232 (after b17 frameS) = true)
    (hx30 : XReg.X30 ∈ sl.map (·.2)) {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b17Offset))
    (hb : Body m0 1232 mleStack sl 0 0 s.data)
    (hv : (⟨s.data.regs.X23, s.data.regs.X24⟩ : EW) = target m0) :
    Eventually (step1 Host.exe) (Post m0) s := by
  obtain ⟨hwf, hm⟩ := hb.exit_match hS (by decide) rfl
  refine exec_at (hb17 hp) run_b17 hwf hpc hm fun s' hm' hpc' ↦ ?_
  obtain ⟨hsaved, hx30', hdm⟩ := hb.saved hm' hwf hx30 (after_eq run_b17 ▸ hres) rfl
  simp only [PcOk] at hpc'
  refine .done _ ⟨by rw [hpc']; simp only [retOf, hx30'], ?_,
    fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  rw [← target_eq, ← hv]
  show (⟨s'.data.regs.getXReg .X0, s'.data.regs.getXReg .X1⟩ : EW) =
    ⟨s.data.regs.getXReg .X23, s.data.regs.getXReg .X24⟩
  rw [reg_of hm' (r := .X0) rfl, reg_of hm' (r := .X1) rfl]
  rfl

end

end NativeRustcVmArm.Arrays.MleOfMultilinearEval
