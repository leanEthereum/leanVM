module

public import NativeRustcVmX64.Field.KinvSq.Exec
public import NativeRustcVmX64.Field.Call
public import NativeRustcVmX64.Field.W32
public import NativeRustcVmX64.Code.Vm.KinvSq.Names
public import NativeRustcVmX64.Code.Vm.Kmul.Names

/-!
# `kinv::sq` on x86-64

`kinvSq_spec`: rustc's `kinv::sq(v, n)`, placed anywhere in the program, given `kmul`'s contract,
returns `v` squared `n` times for a nonzero `n` (ESI). The prologue pushes RBX and keeps the count
in EBX; the loop's head (`Inv`) holds `v` squared `i` times in RAX and `n - i` in RBX.
-/

namespace NativeRustcVmX64.Field.KinvSq

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.KinvSq

@[expose] public section

/-- The pushed registers' slots. -/
def slots : List (Reg64 × Nat) := [(.rbx, 8)]

/-- The callee-saved registers it uses. -/
def used : List Reg64 := [.rbx]

end

public section

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.KinvSq.b0Offset) :=
  b0_in_code.trans hp.1 (by rw [b0]; exact List.cons_ne_nil _ _)
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.KinvSq.b1Offset) :=
  b1_in_code.trans hp.1 (by rw [b1]; exact List.cons_ne_nil _ _)
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.KinvSq.b2Offset) :=
  b2_in_code.trans hp.1 (by rw [b2]; exact List.cons_ne_nil _ _)
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.KinvSq.b3Offset) :=
  b3_in_code.trans hp.1 (by rw [b3]; exact List.cons_ne_nil _ _)

/-- **The loop's head** `NativeRustcVmX64.Vm.KinvSq.label_1`, after `i` squarings. -/
structure Inv (m0 m1 : MachineData) (k i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KinvSq.b1Offset)
  lt : i < kinvSqCount m0
  fr : Fr m0 m1 16 kinvSqStack 8 used st.data
  rax : reg st.data .rax = (ksqIter i (.ofBitVec (reg m0 .rdi))).toBitVec
  rbx : (reg st.data .rbx).toNat = kinvSqCount m0 - i

/-- `kinv::sq`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ KinvSqPost m0 st.data

omit [Host] in
theorem geo {m0 : MachineData} (hpre : KinvSqPre m0) : Geo m0 16 kinvSqStack :=
  ⟨hpre.1, by decide, by decide⟩

omit [Host] in
theorem count_lt (m0 : MachineData) : kinvSqCount m0 < 2 ^ 32 := Nat.mod_lt _ (by decide)

/-- **One squaring**: from the loop's head, back to it or returned. -/
theorem step (hp : Placed code k)
    (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 m1 : MachineData} (hpre : KinvSqPre m0) (hsl : Slots m0 m1 16 slots) {i : Nat}
    {st : MachineState} (hI : Inv m0 m1 k i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨ Inv m0 m1 k (i + 1) st') st := by
  have g := geo hpre
  have hlt := count_lt m0
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hi, hF, hax, hbx⟩ := hI
  simp only at hpc hF hax hbx
  subst hpc
  refine block g hF (vars := fun _ ↦ 0) (hb1 hp) run_b1 (o := 0) rfl (by decide)
    (by decide +kernel) fun st1 hm1 hpc1 hF1 ↦ ?_
  have h1di : reg st1.data .rdi = reg d .rax := hm1.regs .rdi _ rfl
  have h1si : reg st1.data .rsi = reg d .rax := hm1.regs .rsi _ rfl
  have h1bx : reg st1.data .rbx = reg d .rbx := hm1.regs .rbx _ rfl
  refine call g hF1 hpc1 (S := kmulStack) (by decide) hkmul id (fun _ _ h ↦ h.2)
    fun st2 hpc2 hq hF2 ↦ ?_
  have h2ax : reg st2.data .rax = (ksqIter (i + 1) (.ofBitVec (reg m0 .rdi))).toBitVec := by
    rw [hq.1, h1di, h1si, hax, UInt64.ofBitVec_toBitVec]
    rfl
  have h2bx : reg st2.data .rbx = reg d .rbx := (hq.2.2.1 .rbx rfl).trans h1bx
  obtain ⟨d2, pc2⟩ := st2
  simp only [show k + NativeRustcVmX64.Vm.KinvSq.b1Offset + b1.length = k + NativeRustcVmX64.Vm.KinvSq.b2Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.KinvSq.b1_next]] at hpc2
  subst hpc2
  simp only at hF2 h2ax h2bx
  refine block g hF2 (vars := fun _ ↦ 0) (hb2 hp) run_b2 (o := 8) rfl (by decide)
    (by decide +kernel) fun st3 hm3 hpc3 hF3 ↦ ?_
  have h3ax : reg st3.data .rax = reg d2 .rax := hm3.regs .rax _ rfl
  have h3bx : (reg st3.data .rbx).toNat = kinvSqCount m0 - (i + 1) := by
    rw [show reg st3.data .rbx = _ from hm3.regs .rbx _ rfl]
    show (BinOp.apply .sub .W32 (reg d2 .rbx) (BitVec.ofNat 64 1)).toNat = _
    rw [sub32_toNat] <;> rw [h2bx, hbx] <;> omega
  simp only [PcOk] at hpc3
  have hc : (SBool.not (.cmp .eq .W32 (.bin .sub .W32 (.reg .rbx) (.lit 1)) (.lit 0))).eval
      (frameEnv m0 d2 16 (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.KinvSq.b2Offset + b2.length)).toBitVec) =
      !decide (kinvSqCount m0 - i = 1) := by
    have hb2 : (d2.regs.get64 .rbx).toNat = kinvSqCount m0 - i :=
      (congrArg BitVec.toNat h2bx).trans hbx
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, eq32_zero]
    rw [sub32_toNat (by rw [hb2]; omega) (by rw [hb2]; omega), hb2]
    congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega
  rw [hc] at hpc3
  by_cases hlast : kinvSqCount m0 - i = 1
  · rw [hlast] at hpc3
    simp only [decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at hpc3
    obtain ⟨d3, pc3⟩ := st3
    simp only [show k + NativeRustcVmX64.Vm.KinvSq.b2Offset + b2.length = k + NativeRustcVmX64.Vm.KinvSq.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.KinvSq.b2_next]] at hpc3
    subst hpc3
    simp only at hF3 h3ax
    refine Eventually.mono (epilogue_ret g hF3 hsl (vars := fun _ ↦ 0) (hb3 hp) run_b3
      (by decide +kernel) rfl rfl) fun st ⟨hm, hret, hrsp, hso, hsv⟩ ↦ Or.inl ⟨hret, hrsp, ?_, hso, hsv⟩
    rw [show reg st.data .rax = _ from hm.regs .rax _ rfl]
    show reg d3 .rax = _
    rw [h3ax, h2ax]
    congr 2
    omega
  · simp only [hlast, decide_false, Bool.not_false, ite_true] at hpc3
    exact .done _ (Or.inr ⟨hpc3.trans (hp.label NativeRustcVmX64.Vm.KinvSq.label_1_at), by omega, hF3, h3ax.trans h2ax,
      h3bx⟩)

/-- **`kinv::sq` squares `n` times.** -/
theorem kinvSq_spec (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.KinvSq.entryLabel) KinvSqPre KinvSqPost := by
  intro m0 hpre
  have g := geo hpre
  have hlt := count_lt m0
  rw [show Labels.label NativeRustcVmX64.Vm.KinvSq.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.KinvSq.b0Offset) from hp.label NativeRustcVmX64.Vm.KinvSq.entry_at]
  refine prologue (used := used) (slots := slots) (vars := fun _ ↦ 0) g (hb0 hp) run_b0 (o := 8)
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) fun st1 hm1 hpc1 hF1 hsl ↦ ?_
  have hI : Inv m0 st1.data k 0 st1 := by
    refine ⟨hpc1, Nat.pos_of_ne_zero hpre.2, hF1, hm1.regs .rax _ rfl, ?_⟩
    rw [show reg st1.data .rbx = _ from hm1.regs .rbx _ rfl]
    exact trunc32_toNat _
  exact Sym.loop (fun μ st ↦ ∃ i, μ = kinvSqCount m0 - i ∧ Inv m0 st1.data k i st)
    (fun _ _ ⟨i, hμ, hI⟩ ↦ Eventually.mono (step hp hkmul hpre hsl hI) fun st' h ↦
      h.imp_right fun h' ↦ ⟨kinvSqCount m0 - (i + 1), by have := hI.lt; omega, i + 1, rfl, h'⟩)
    ⟨0, rfl, hI⟩

end

end NativeRustcVmX64.Field.KinvSq
