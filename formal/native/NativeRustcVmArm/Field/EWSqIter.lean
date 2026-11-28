module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EWSqIter.Names
public import NativeRustcVmArm.Field.EWSqIter.Exec
public import NativeRustcVmArm.Field.Prologue
public import NativeRustcVmArm.Field.W32

/-!
# `EW::sq_iter` on AArch64

`ewSqIter_spec`: rustc's `EW::sq_iter(k, x)`, placed anywhere in the program, given `EW::mul`'s
contract, returns `EW.sqIter k x` (`x^(2^k)`). The prologue saves X30 and X19 and keeps the count in
X19; the loop's head (`Inv`) holds the element squared `i` times in X0, X3 and `k - i` in X19.
-/

namespace NativeRustcVmArm.Field.EWSqIter

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Field NativeRustcVmArm.Vm.EWSqIter
open NativeVm.Model (EW)

@[expose] public section

/-- The saved registers' slots. -/
def slots : List (XReg × Nat) := [(.X30, 0), (.X19, 8)]

/-- The callee-saved registers it uses. -/
def used : List XReg := [.X19]

/-- The count. -/
def cnt (m0 : MachineData) : Nat := m0.regs.X0.toNat

/-- The result. -/
def target (m0 : MachineData) : EW := EW.sqIter (cnt m0) ⟨m0.regs.X1, m0.regs.X2⟩

end

public section

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EWSqIter.b0Offset) :=
  b0_in_code.trans hp.1 (by rw [b0]; exact List.cons_ne_nil _ _)
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EWSqIter.b1Offset) :=
  b1_in_code.trans hp.1 (by rw [b1]; exact List.cons_ne_nil _ _)
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EWSqIter.b2Offset) :=
  b2_in_code.trans hp.1 (by rw [b2]; exact List.cons_ne_nil _ _)
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EWSqIter.b3Offset) :=
  b3_in_code.trans hp.1 (by rw [b3]; exact List.cons_ne_nil _ _)

/-- **The loop's head** `.LEWSqIter_1`, `j ≥ 1` squarings left. -/
structure Inv (m0 m1 : MachineData) (k j : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EWSqIter.b1Offset)
  pos : 0 < j
  fr : Fr m0 m1 16 ewSqIterStack used st.data
  x19 : st.data.regs.X19.toNat = j
  val : EW.sqIter j ⟨st.data.regs.X0, st.data.regs.X3⟩ = target m0

/-- `EW::sq_iter`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ EWSqIterPost m0 st.data

omit [Host] in
theorem geo {m0 : MachineData} (hpre : EWSqIterPre m0) : Geo m0 16 ewSqIterStack :=
  ⟨hpre, rfl, by decide⟩

omit [Host] in
theorem keep [Labels] {d : MachineData} {S : SState} {st : MachineData}
    (hm : Match (Env.ofMachine d []) S st) {r r' : XReg} (h : S.reg r = some (.reg r')) :
    st.regs.getXReg r = d.regs.getXReg r' :=
  UInt64.toBitVec_inj.mp (hm.regs r _ h)

/-- From the epilogue, with the result in X0, X3. -/
theorem finish (hp : Placed code k) {m0 m1 d : MachineData} (hpre : EWSqIterPre m0)
    (hsl : Slots m0 m1 16 slots) (hF : Fr m0 m1 16 ewSqIterStack used d)
    (hv : (⟨d.regs.X0, d.regs.X3⟩ : EW) = target m0) :
    Eventually (step1 Host.exe) (Post m0) ⟨d, Host.addrOf (k + NativeRustcVmArm.Vm.EWSqIter.b3Offset)⟩ := by
  have g := geo hpre
  refine Eventually.mono (epilogue g hF hsl (hb3 hp) run_b3 (by decide +kernel) rfl rfl)
    fun st ⟨hret, hso, hsv, hm⟩ ↦ ⟨hret, ?_, ?_, hso, hsv⟩
  · have hx0 : st.data.regs.X0.toBitVec = d.regs.X0.toBitVec := hm.regs .X0 (.reg .X0) rfl
    rw [UInt64.toBitVec_inj.mp hx0]
    exact congrArg EW.c0 hv
  · have hx1 : st.data.regs.X1.toBitVec = d.regs.X3.toBitVec := hm.regs .X1 (.reg .X3) rfl
    rw [UInt64.toBitVec_inj.mp hx1]
    exact congrArg EW.c1 hv

/-- **One squaring**: from the loop's head, back to it or returned. -/
theorem step (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 m1 : MachineData} (hpre : EWSqIterPre m0) (hsl : Slots m0 m1 16 slots) {j : Nat}
    {st : MachineState} (hI : Inv m0 m1 k j st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨ Inv m0 m1 k (j - 1) st') st := by
  have g := geo hpre
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hj, hF, hx19, hv⟩ := hI
  simp only at hpc hF hx19 hv
  subst hpc
  refine block hF (hb1 hp) run_b1 rfl rfl (by decide +kernel) fun st1 hm1 hpc1 hF1 ↦ ?_
  have h10 : st1.data.regs.X0 = d.regs.X0 := keep hm1 (r := .X0) rfl
  have h11 : st1.data.regs.X1 = d.regs.X3 := keep hm1 (r := .X1) (r' := .X3) rfl
  have h12 : st1.data.regs.X2 = d.regs.X0 := keep hm1 (r := .X2) (r' := .X0) rfl
  have h13 : st1.data.regs.X3 = d.regs.X3 := keep hm1 (r := .X3) rfl
  have h119 : st1.data.regs.X19 = d.regs.X19 := keep hm1 (r := .X19) rfl
  refine call g hF1 hpc1 (S := ewMulStack) (by decide) hmul id (fun _ _ h ↦ h.2.2)
    fun st2 hpc2 hq hF2 ↦ ?_
  have hsq : (⟨st2.data.regs.X0, st2.data.regs.X1⟩ : EW) =
      (⟨d.regs.X0, d.regs.X3⟩ : EW) * ⟨d.regs.X0, d.regs.X3⟩ := by
    rw [hq.1, hq.2.1, h10, h11, h12, h13]
    rfl
  have h219 : st2.data.regs.X19 = d.regs.X19 := (hq.2.2.2.1 .X19 rfl).trans h119
  obtain ⟨d2, pc2⟩ := st2
  simp only [show k + NativeRustcVmArm.Vm.EWSqIter.b1Offset + b1.length = k + NativeRustcVmArm.Vm.EWSqIter.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.EWSqIter.b1_next]] at hpc2
  subst hpc2
  simp only at hF2 hsq h219
  refine block hF2 (hb2 hp) run_b2 rfl rfl (by decide +kernel) fun st3 hm3 hpc3 hF3 ↦ ?_
  have h30 : st3.data.regs.X0 = d2.regs.X0 := keep hm3 (r := .X0) rfl
  have h33 : st3.data.regs.X3 = d2.regs.X1 := keep hm3 (r := .X3) (r' := .X1) rfl
  have h319 : st3.data.regs.X19.toNat = j - 1 := by
    show (st3.data.regs.getXReg .X19).toBitVec.toNat = _
    rw [hm3.regs .X19 _ rfl]
    show (BinOp.apply .sub .W64 (d2.regs.getXReg .X19).toBitVec (BitVec.ofNat 64 1)).toNat = _
    rw [sub64_toNat] <;> simp only [Reg64s.getXReg, h219, UInt64.toNat_toBitVec, hx19]
    omega
  have hv' : EW.sqIter (j - 1) ⟨st3.data.regs.X0, st3.data.regs.X3⟩ = target m0 := by
    rw [h30, h33, hsq, ← hv]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rfl
  simp only [PcOk] at hpc3
  have hc : (SBool.not (.cmp .eq .W64 (.reg .X19) (.lit 1))).eval (Env.ofMachine d2 []) =
      !decide (j = 1) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, eq64_lit _ 1 (by decide)]
    show (!decide (d2.regs.X19.toBitVec.toNat = 1)) = _
    rw [h219, UInt64.toNat_toBitVec, hx19]
  rw [hc] at hpc3
  by_cases hlast : j = 1
  · simp only [hlast, decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at hpc3
    obtain ⟨d3, pc3⟩ := st3
    simp only [show k + NativeRustcVmArm.Vm.EWSqIter.b2Offset + b2.length = k + NativeRustcVmArm.Vm.EWSqIter.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.EWSqIter.b2_next]] at hpc3
    subst hpc3
    simp only at hF3 hv'
    refine Eventually.mono (finish hp hpre hsl hF3 ?_) fun _ h ↦ Or.inl h
    rw [← hv', hlast]
    rfl
  · simp only [hlast, decide_false, Bool.not_false, ite_true] at hpc3
    exact .done _ (Or.inr ⟨hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.EWSqIter.b1Offset) NativeRustcVmArm.Vm.EWSqIter.label_1_at), by omega, hF3, h319, hv'⟩)

/-- **`EW::sq_iter` squares `k` times.** -/
theorem ewSqIter_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost := by
  intro m0 hpre
  have g := geo hpre
  rw [show Labels.label NativeRustcVmArm.Vm.EWSqIter.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.EWSqIter.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.EWSqIter.entryOffset) NativeRustcVmArm.Vm.EWSqIter.entry_at]
  refine prologue (used := used) (slots := slots) g (hb0 hp) run_b0 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) fun st1 hm1 hpc1 hF1 hsl ↦ ?_
  have h10 : st1.data.regs.X0 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X0 (.reg .X1) rfl)
  have h13 : st1.data.regs.X3 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X3 (.reg .X2) rfl)
  have h119 : st1.data.regs.X19 = m0.regs.X0 :=
    UInt64.toBitVec_inj.mp (hm1.regs .X19 (.reg .X0) rfl)
  simp only [PcOk] at hpc1
  have hc : (SBool.cmp .eq .W64 (.reg .X0) (.lit 0)).eval (frameEnv m0 m0 16) =
      decide (cnt m0 = 0) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, eq64_lit _ 0 (by decide)]
    rfl
  rw [hc] at hpc1
  obtain ⟨d1, pc1⟩ := st1
  simp only at hF1 hsl h10 h13 h119 hpc1
  by_cases hz : cnt m0 = 0
  · simp only [hz, decide_true, ite_true] at hpc1
    rw [hp.label (j := NativeRustcVmArm.Vm.EWSqIter.b3Offset) NativeRustcVmArm.Vm.EWSqIter.label_2_at] at hpc1
    subst hpc1
    refine finish hp hpre hsl hF1 ?_
    rw [h10, h13, target, hz]
    rfl
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false,
      show k + NativeRustcVmArm.Vm.EWSqIter.b0Offset + b0.length = k + NativeRustcVmArm.Vm.EWSqIter.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.EWSqIter.b0_next]] at hpc1
    subst hpc1
    have hI : Inv m0 d1 k (cnt m0) ⟨d1, Host.addrOf (k + NativeRustcVmArm.Vm.EWSqIter.b1Offset)⟩ :=
      ⟨rfl, Nat.pos_of_ne_zero hz, hF1, by rw [h119]; rfl, by rw [h10, h13]; rfl⟩
    exact Sym.loop (fun μ st ↦ ∃ j, μ = j ∧ Inv m0 d1 k j st)
      (fun _ _ ⟨j, hμ, hI⟩ ↦ Eventually.mono (step hp hmul hpre hsl hI) fun st' h ↦
        h.imp_right fun h' ↦ ⟨j - 1, by have := hI.pos; omega, j - 1, rfl, h'⟩)
      ⟨_, rfl, hI⟩

end

end NativeRustcVmArm.Field.EWSqIter
