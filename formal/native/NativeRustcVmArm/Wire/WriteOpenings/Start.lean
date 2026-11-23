module

public import NativeRustcVmArm.Code.Vm.Find.Names
public import NativeRustcVmArm.Wire.WriteOpenings.Entry

/-!
# `write_openings`' queries' loops set up

After the prologue (`Ent`): with levels, `b1` (from `argS`, reading the sibling counts' address
above the frame) to `HeadA` (`b1_step`); without, `b23` and a leaf (`b24`, `HeadB`) or none
(`b38`, `HeadZ`) (`b23_step`). Hence the postcondition from the entry (`entry_spec`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

public section

/-- `Ent`'s registers. -/
abbrev entRegs : List XReg := [.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7, .X10, .X19, .X21]

variable {R : Run}

theorem Ent.keep {m m' : MachineData} (h : Ent R m) (hfr : Frm R m') (hd : m'.dmem = m.dmem)
    (hk : ∀ r ∈ entRegs, m'.regs.getXReg r = m.regs.getXReg r) : Ent R m' :=
  ⟨hfr, by rw [hk .X0 (by simp)]; exact h.x0, by rw [hk .X1 (by simp)]; exact h.x1,
    by rw [hk .X2 (by simp)]; exact h.x2, by rw [hk .X3 (by simp)]; exact h.x3,
    by rw [hk .X4 (by simp)]; exact h.x4, by rw [hk .X5 (by simp)]; exact h.x5,
    by rw [hk .X6 (by simp)]; exact h.x6, by rw [hk .X7 (by simp)]; exact h.x7,
    by rw [hk .X10 (by simp)]; exact h.x10, by rw [hk .X19 (by simp)]; exact h.x19,
    by rw [hk .X21 (by simp)]; exact h.x21, hd ▸ h.done⟩

variable [Host]

/-- **With levels** (`b1`): the queries' loop head at the first query. -/
theorem b1_step (hp : Placed code R.k) (G : Geo R) {st : MachineState}
    (hpc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b1Offset) (E : Ent R st.data) (hh : 0 < R.h) :
    Eventually (step1 Host.exe) (HeadA R 0) st := by
  have hwf : (Env.ofMachine st.data [(base R.m0 176, 192)]).WF :=
    Env.wf_of ⟨⟨fun t ht ↦ E.fr.kept _ (G.args_mapped t ht), G.args_noWrap⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine st.data [(base R.m0 176, 192)]) argS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, trivial⟩ (by rw [E.fr.sp]; simp [Sym.eval])
      trivial trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf hpc hm fun s1 hm1 hpc1 ↦
    .done _ ?_
  have hfr1 : Frm R s1.data := Fr.ofBlock E.fr hm hm1 hwf rfl rfl rfl fun r hr ↦ by cases hr
  have hk := regs_keep hm hm1 (rs := [.X1, .X2, .X3, .X4, .X5, .X19, .X21]) (by decide)
  have hlw := G.lw64
  have hh32 := G.h32
  have hin : Inside R.m0.regs.SP.toBitVec 8 (R.big 1) := by
    rw [big1]; exact ⟨le_refl _, Nat.add_le_add_left (show (8 : Nat) ≤ 16 by decide) _⟩
  refine ⟨hpc1.trans (congrArg Host.addrOf rfl), hfr1, ⟨by rw [hk .X19 (by simp)]; exact E.x19,
    by rw [hk .X21 (by simp)]; exact E.x21, by rw [hm1.regs .X22 _ rfl]; rfl, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩, ⟨by rw [hk .X1 (by simp)]; exact E.x1, by rw [hk .X3 (by simp)]; exact E.x3,
    by rw [hk .X4 (by simp)]; exact E.x4, by rw [hk .X5 (by simp)]; exact E.x5⟩, ?_,
    by rw [hm1.regs .X9 _ rfl]; rfl, by rw [hm1.regs .X11 _ rfl]; rfl, G.nq0, hh,
    by rw [hm1.dmem_eq hwf rfl]; exact E.done⟩
  · rw [hm1.regs .X23 _ rfl]; exact E.x7
  · rw [hm1.regs .X26 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, lsl11, lslS]
    rw [E.x6, ofNat_toNat (by omega), ofNat_add, ofNat_toNat (by omega)]
    congr 1
    show 2048 * (R.h + R.h * 4) = 10240 * R.h
    omega
  · rw [hm1.regs .X29 _ rfl]
    simp only [Sym.eval, Ring.load_eq_wordOf, Env.ofMachine_mem0, Env.base_ofMachine_eq,
      List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    rw [Ring.base_add_eq, G.wordOf_keep E.fr (i := 1) (by omega) (by omega) hin,
      NativeRustcVm.wordOf_of_wordAt G.cntW]
  · rw [hm1.regs .X15 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [E.x21, and124 (by omega)]
  · rw [hm1.regs .X16 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [E.x10]
  · rw [hm1.regs .X17 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [E.x10]
  · rw [hm1.regs .X20 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [E.x10]
  · rw [hk .X2 (by simp), E.x2, Nat.mul_zero, NativeRustcVm.addr_add_zero]

/-- **Without levels** (`b23`, then `b24` or `b38`): the epilogue. -/
theorem b23_step (hp : Placed code R.k) (G : Geo R) {st : MachineState}
    (hpc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b23Offset) (E : Ent R st.data) (hh : R.h = 0) :
    Eventually (step1 Host.exe) (Post R) st := by
  have hlw := G.lw64
  have hwf := G.wf0 E.fr.kept
  have hm := frMatch G E.fr
  refine run_block G hp b23_in_code (by simp [b23]) run_b23 E.fr hpc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have E1 : Ent R s1.data := E.keep hfr1 (hm1.dmem_eq hwf rfl) (regs_keep hm hm1 (by decide))
  have hc : (SBool.cmp .eq .W64 (.reg .X21) (.lit 0)).eval (envOf R st.data []) =
      decide (R.lw = 0) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [E.x21, ofNat_toNat (by omega)]
    rfl
  simp only [PcOk, hc] at hpc1
  have hwf2 := G.wf0 hfr1.kept
  have hm2 := frMatch G hfr1
  by_cases hl : R.lw = 0
  · simp only [hl, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b38Offset) NativeRustcVmArm.Vm.WriteOpenings.label_33_at] at hpc1
    refine run_block G hp b38_in_code (by simp [b38]) run_b38 hfr1 hpc1 hwf2 hm2 rfl
      (writesOk_frame (by decide)) fun s2 hfr2 hm2' hpc2 ↦ queryZ_loop (j := 0) hp G ?_
    have hk := regs_keep hm2 hm2' (rs := [.X1, .X2, .X3, .X5, .X19]) (by decide)
    refine ⟨hpc2.trans (congrArg Host.addrOf rfl), hfr2, by rw [hm2'.regs .X0 _ rfl]; rfl,
      by rw [hk .X1 (by simp)]; exact E1.x1, ?_, by rw [hk .X3 (by simp)]; exact E1.x3,
      by rw [hk .X5 (by simp)]; exact E1.x5, by rw [hm2'.regs .X8 _ rfl]; rfl,
      by rw [hm2'.regs .X9 _ rfl]; rfl, by rw [hk .X19 (by simp)]; exact E1.x19, G.nq0, hh, hl,
      by rw [hm2'.dmem_eq hwf2 rfl]; exact E1.done⟩
    rw [hk .X2 (by simp), E1.x2, Nat.mul_zero, NativeRustcVm.addr_add_zero]
  · simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine run_block G hp b24_in_code (by simp [b24]) run_b24 hfr1
      (hpc1.trans (congrArg Host.addrOf rfl)) hwf2 hm2 rfl (writesOk_frame (by decide))
      fun s2 hfr2 hm2' hpc2 ↦ queryB_loop (j := 0) hp G ?_
    have hk := regs_keep hm2 hm2' (rs := [.X1, .X2, .X3, .X4, .X5, .X19, .X21]) (by decide)
    refine ⟨hpc2.trans (congrArg Host.addrOf rfl), hfr2, by rw [hk .X1 (by simp)]; exact E1.x1,
      ?_, by rw [hk .X3 (by simp)]; exact E1.x3, by rw [hk .X4 (by simp)]; exact E1.x4,
      by rw [hk .X5 (by simp)]; exact E1.x5, ?_, ?_, ?_, by rw [hm2'.regs .X11 _ rfl]; rfl,
      by rw [hm2'.regs .X12 _ rfl]; rfl, by rw [hk .X19 (by simp)]; exact E1.x19,
      by rw [hk .X21 (by simp)]; exact E1.x21, G.nq0, hh, by omega,
      by rw [hm2'.dmem_eq hwf2 rfl]; exact E1.done⟩
    · rw [hk .X2 (by simp), E1.x2, Nat.mul_zero, NativeRustcVm.addr_add_zero]
    · rw [hm2'.regs .X8 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [E1.x21, and124 (by omega)]
    · rw [hm2'.regs .X9 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [E1.x10]
    · rw [hm2'.regs .X10 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [E1.x10]

/-- **From the entry**: the postcondition. -/
theorem entry_spec (hp : Placed code R.k) (G : Geo R)
    (hfind : Spec (Labels.label NativeRustcVmArm.Vm.Find.entryLabel) FindPre FindPost) :
    Eventually (step1 Host.exe) (Post R) ⟨R.m0, Host.addrOf (R.k + NativeRustcVmArm.Vm.WriteOpenings.b0Offset)⟩ :=
  b0_step hp G (fun _ hpc E hh ↦ eventually_trans _ _ _ _ (b1_step hp G hpc E hh)
    fun _ H ↦ query_loop hp G hfind H) fun _ hpc E hh ↦ b23_step hp G hpc E hh

end

end NativeRustcVmArm.Wire.WriteOpenings
