module

public import NativeRustcVmArm.Code.Vm.KinvSq.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Field.KinvSq.Exec
public import NativeRustcVmArm.Field.Prologue
public import NativeRustcVmArm.Field.W32

/-!
# `kinv::sq` on AArch64

`kinvSq_spec`: rustc's `kinv::sq(v, n)`, placed anywhere in the program, given `kmul`'s contract,
returns `v` squared `n` times for a nonzero `n` (W1). The prologue saves X30 and X19 and keeps the
count in W19; the loop's head (`Inv`) holds `v` squared `i` times in X0 and `n - i` in X19.
-/

namespace NativeRustcVmArm.Field.KinvSq

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Field NativeRustcVmArm.Vm.KinvSq

@[expose] public section

/-- The saved registers' slots. -/
def slots : List (XReg × Nat) := [(.X30, 0), (.X19, 8)]

/-- The callee-saved registers it uses. -/
def used : List XReg := [.X19]

end

public section

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.KinvSq.b0Offset) :=
  b0_in_code.trans hp.1 (by rw [b0]; exact List.cons_ne_nil _ _)
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.KinvSq.b1Offset) :=
  b1_in_code.trans hp.1 (by rw [b1]; exact List.cons_ne_nil _ _)
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.KinvSq.b2Offset) :=
  b2_in_code.trans hp.1 (by rw [b2]; exact List.cons_ne_nil _ _)
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.KinvSq.b3Offset) :=
  b3_in_code.trans hp.1 (by rw [b3]; exact List.cons_ne_nil _ _)

/-- **The loop's head** `.LKinvSq_1`, after `i` squarings. -/
structure Inv (m0 m1 : MachineData) (k i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KinvSq.b1Offset)
  lt : i < kinvSqCount m0
  fr : Fr m0 m1 16 kinvSqStack used st.data
  x0 : st.data.regs.X0 = ksqIter i m0.regs.X0
  x19 : st.data.regs.X19.toNat = kinvSqCount m0 - i

/-- `kinv::sq`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ KinvSqPost m0 st.data

omit [Host] in
theorem geo {m0 : MachineData} (hpre : KinvSqPre m0) : Geo m0 16 kinvSqStack :=
  ⟨hpre.1, rfl, by decide⟩

omit [Host] in
theorem count_lt (m0 : MachineData) : kinvSqCount m0 < 2 ^ 32 := Nat.mod_lt _ (by decide)

omit [Host] in
theorem ksqIter_succ (i : Nat) (v : UInt64) :
    ksqIter (i + 1) v = NativeVm.Model.kmul (ksqIter i v) (ksqIter i v) := rfl

/-- **One squaring**: from the loop's head, back to it or returned. -/
theorem step (hp : Placed code k)
    (hkmul : Spec (Labels.label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 m1 : MachineData} (hpre : KinvSqPre m0) (hsl : Slots m0 m1 16 slots) {i : Nat}
    {st : MachineState} (hI : Inv m0 m1 k i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨ Inv m0 m1 k (i + 1) st') st := by
  have g := geo hpre
  have hlt := count_lt m0
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hi, hF, hx0, hx19⟩ := hI
  simp only at hpc hF hx0 hx19
  subst hpc
  refine block hF (hb1 hp) run_b1 rfl rfl (by decide +kernel) fun st1 hm1 hpc1 hF1 ↦ ?_
  have h10 : st1.data.regs.X0 = d.regs.X0 := Match.reg_eq (r := .X0) (match_nil d) hm1 rfl rfl
  have h11 : st1.data.regs.X1 = d.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl)
  have h119 : st1.data.regs.X19 = d.regs.X19 := Match.reg_eq (r := .X19) (match_nil d) hm1 rfl rfl
  refine call g hF1 hpc1 (S := kmulStack) (by decide) hkmul id (fun _ _ h ↦ h.2)
    fun st2 hpc2 hq hF2 ↦ ?_
  have h20 : st2.data.regs.X0 = ksqIter (i + 1) m0.regs.X0 := by
    rw [hq.1, h10, h11, hx0]; rfl
  have h219 : st2.data.regs.X19 = d.regs.X19 := (hq.2.2.1 .X19 rfl).trans h119
  obtain ⟨d2, pc2⟩ := st2
  simp only [show k + NativeRustcVmArm.Vm.KinvSq.b1Offset + b1.length = k + NativeRustcVmArm.Vm.KinvSq.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.KinvSq.b1_next]] at hpc2
  subst hpc2
  simp only at hq hF2 h20 h219
  refine block hF2 (hb2 hp) run_b2 rfl rfl (by decide +kernel) fun st3 hm3 hpc3 hF3 ↦ ?_
  have h30 : st3.data.regs.X0 = d2.regs.X0 := Match.reg_eq (r := .X0) (match_nil d2) hm3 rfl rfl
  have h319 : st3.data.regs.X19.toNat = kinvSqCount m0 - (i + 1) := by
    show (st3.data.regs.getXReg .X19).toBitVec.toNat = _
    rw [hm3.regs .X19 _ rfl]
    show (BinOp.apply .sub .W32 (d2.regs.getXReg .X19).toBitVec (BitVec.ofNat 64 1)).toNat = _
    rw [sub32_toNat] <;> simp only [Reg64s.getXReg, h219, UInt64.toNat_toBitVec, hx19] <;> omega
  simp only [PcOk] at hpc3
  have hc : (SBool.not (.cmp .eq .W32 (.reg .X19) (.lit 1))).eval (Env.ofMachine d2 []) =
      !decide (kinvSqCount m0 - i = 1) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, eq32_one]
    show (!decide (d2.regs.X19.toBitVec.toNat % 2 ^ 32 = 1)) = _
    rw [h219, UInt64.toNat_toBitVec, hx19, Nat.mod_eq_of_lt (by omega)]
  rw [hc] at hpc3
  by_cases hlast : kinvSqCount m0 - i = 1
  · rw [hlast] at hpc3
    simp only [decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at hpc3
    obtain ⟨d3, pc3⟩ := st3
    simp only [show k + NativeRustcVmArm.Vm.KinvSq.b2Offset + b2.length = k + NativeRustcVmArm.Vm.KinvSq.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.KinvSq.b2_next]] at hpc3
    subst hpc3
    simp only at hF3 h30
    refine Eventually.mono (epilogue g hF3 hsl (hb3 hp) run_b3 (by decide +kernel) rfl rfl)
      fun st ⟨hret, hso, hsv, hm⟩ ↦ Or.inl ⟨hret, ?_, hso, hsv⟩
    show st.data.regs.getXReg .X0 = _
    rw [Match.reg_eq (r := .X0) (match_epi g hF3) hm rfl rfl]
    show d3.regs.X0 = _
    rw [h30, h20]
    congr 1
    omega
  · simp only [hlast, decide_false, Bool.not_false, ite_true] at hpc3
    refine .done _ (Or.inr ⟨hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.KinvSq.b1Offset) NativeRustcVmArm.Vm.KinvSq.label_1_at), by omega, hF3, h30.trans h20,
      h319⟩)

/-- **`kinv::sq` squares `n` times.** -/
theorem kinvSq_spec (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.KinvSq.entryLabel) KinvSqPre KinvSqPost := by
  intro m0 hpre
  have g := geo hpre
  have hlt := count_lt m0
  rw [show Labels.label NativeRustcVmArm.Vm.KinvSq.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.KinvSq.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.KinvSq.entryOffset) NativeRustcVmArm.Vm.KinvSq.entry_at]
  refine prologue (used := used) (slots := slots) g (hb0 hp) run_b0 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) fun st1 hm1 hpc1 hF1 hsl ↦ ?_
  have hI : Inv m0 st1.data k 0 st1 := by
    refine ⟨hpc1, Nat.pos_of_ne_zero hpre.2, hF1, ?_, ?_⟩
    · exact UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl)
    · show (st1.data.regs.getXReg .X19).toBitVec.toNat = _
      rw [hm1.regs .X19 _ rfl]
      exact trunc32_toNat _
  exact Sym.loop (fun μ st ↦ ∃ i, μ = kinvSqCount m0 - i ∧ Inv m0 st1.data k i st)
    (fun _ _ ⟨i, hμ, hI⟩ ↦ Eventually.mono (step hp hkmul hpre hsl hI) fun st' h ↦
      h.imp_right fun h' ↦ ⟨kinvSqCount m0 - (i + 1), by have := hI.lt; omega, i + 1, rfl, h'⟩)
    ⟨0, rfl, hI⟩

end

end NativeRustcVmArm.Field.KinvSq
