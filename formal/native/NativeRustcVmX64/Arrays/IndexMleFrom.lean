module

public import NativeRustcVmX64.Arrays.IndexMleFrom.Exec
public import NativeRustcVm.Arrays.Folds
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.IndexMleFrom.Names

/-!
# `index_mle_from` on x86-64

**`indexMleFrom_spec`**: rustc's `index_mle_from` (specialised to `GEN`), placed anywhere in the
program, meets `IndexMleFromPre`/`IndexMleFromPost` given `EW::mul`'s contract. The prologue
(`b0`) pushes RBP, R15-R12, RBX, RAX; at `|point| = 0` it returns `1` (`b7`, `b8`); else (`b1`) the
loop (`b2`-`b5`, three calls of `EW::mul`) folds the coordinates at R14 into the accumulator
(R15, R12) and the generator power (R13, RBP) (`Inv`), and the epilogue (`b6`, `b8`) returns the
accumulator.
-/

namespace NativeRustcVmX64.Arrays.IndexMleFrom

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.IndexMleFrom NativeVm.Model
  NativeRustcVmX64.Field
open NativeRustcVm (ewsOf)

public section

/-- The point at the entry. -/
abbrev pts (m : MachineData) : List EW := ewsOf m.dmem (reg m .rdi) (reg m .rsi).toNat
/-- Its length. -/
abbrev len (m : MachineData) : Nat := (reg m .rsi).toNat

/-- The model's step. -/
def f (acc : EW × EW) (r : EW) : EW × EW := (acc.1 * (1 + r * (1 + acc.2)), acc.2 * acc.2)

/-- The model's fold after `i` coordinates. -/
def st (m : MachineData) (i : Nat) : EW × EW := ((pts m).take i).foldl f (1, gen)

theorem indexMleFrom_eq_st (m : MachineData) :
    indexMleFrom gen (slice m (reg m .rdi) (reg m .rsi)) = (st m (len m)).1 := by
  unfold slice st indexMleFrom
  rw [← Array.foldl_toList, List.take_of_length_le (by simp)]
  rfl

theorem lt_len {m : MachineData} {i : Nat} (h : i < len m) : i < (pts m).length := by
  simp only [pts, len, NativeRustcVm.length_ewsOf] at h ⊢; exact h

theorem st_succ (m : MachineData) {i : Nat} (h : i < len m) :
    st m (i + 1) = f (st m i) ((pts m)[i]'(lt_len h)) :=
  NativeRustcVm.foldl_take_succ _ _ _ _

/-- **The loop head** `NativeRustcVmX64.Vm.IndexMleFrom.label_3`, `i` coordinates folded. -/
structure Inv (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  body : Body m0 64 indexMleFromStack slots 0 0 s
  lt : i < len m0
  r14 : reg s .r14 = reg m0 .rdi + BitVec.ofNat 64 (16 * i)
  rbx : reg s .rbx = reg m0 .rdi + BitVec.ofNat 64 (16 * len m0)
  acc : ewArg (reg s .r15) (reg s .r12) = (st m0 i).1
  pow : ewArg (reg s .r13) (reg s .rbp) = (st m0 i).2

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.IndexMleFrom.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.IndexMleFrom.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.IndexMleFrom.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.IndexMleFrom.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.IndexMleFrom.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.IndexMleFrom.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.IndexMleFrom.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.IndexMleFrom.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.IndexMleFrom.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.IndexMleFrom.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.IndexMleFrom.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.IndexMleFrom.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.IndexMleFrom.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.IndexMleFrom.b7Offset) :=
  hp.label NativeRustcVmX64.Vm.IndexMleFrom.label_1_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.IndexMleFrom.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.IndexMleFrom.b2Offset) :=
  hp.label NativeRustcVmX64.Vm.IndexMleFrom.label_3_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.IndexMleFrom.label_4 = Host.addrOf (k + NativeRustcVmX64.Vm.IndexMleFrom.b8Offset) :=
  hp.label NativeRustcVmX64.Vm.IndexMleFrom.label_4_at

/-- `index_mle_from`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ IndexMleFromPost m0 s.data

/-- **The epilogue** `b8`: the accumulator returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : IndexMleFromPre m0)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.IndexMleFrom.b8Offset))
    (hb : Body m0 64 indexMleFromStack slots 0 0 s.data)
    (hacc : ewArg (reg s.data .r15) (reg s.data .r12) = (st m0 (len m0)).1) :
    Eventually (step1 Host.exe) (Post m0) s := by
  have hS := hpre.1
  have h64 : 64 ≤ indexMleFromStack := by decide
  refine exec_at (hb8 hp) run_b8 (hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h64)
    (by intro l h; cases h) hpc hb.mid_match fun s' hm' hpc' ↦ .done _ ?_
  obtain ⟨hpc'', hrsp, hdm, hsaved⟩ := hb.done hS h64 hm' hpc'
    (after_eq run_b8 ▸ b8_restores).1 (after_eq run_b8 ▸ b8_restores).2
    (fun _ _ ↦ not_inRange_zero _)
  refine ⟨hpc'', hrsp, ?_, fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  rw [indexMleFrom_eq_st, ← hacc, ← ewRet_eq,
    show reg s'.data .rax = reg s.data .r15 from hm'.regs .rax (.reg .r15) rfl,
    show reg s'.data .rdx = reg s.data .r12 from hm'.regs .rdx (.reg .r12) rfl]

/-- **A turn of the loop**: coordinate `i` folded in, back at the head or out of the loop and
returned. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : IndexMleFromPre m0) {i : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.IndexMleFrom.b2Offset)) (hI : Inv m0 i s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post m0 s' ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.IndexMleFrom.b2Offset) ∧ Inv m0 (i + 1) s'.data)) s := by
  have hS := hpre.1
  have hA := SliceIn.of_ok hpre.2
  have h64 : 64 ≤ indexMleFromStack := by decide
  have hlt := hI.lt
  have hl : len m0 = (reg m0 .rsi).toNat := rfl
  have hlen := lt_of_offStack hpre.2.1.2 hpre.2.2
  -- `b2`: the coordinate, `r·(1 + pw)`
  obtain ⟨hwf1, hm1, hel⟩ := hI.body.elem (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.IndexMleFrom.b3Offset)).toBitVec) hS h64
    hA hlt (x := .reg .r14) (o := 0) (by rw [eval_reg, add_ofNat_zero]; exact hI.r14)
  refine exec_at (hb2 hp) run_b2 hwf1 (fun _ _ ↦ rfl) hpc hm1 fun s1 hm1' hpc1 ↦ ?_
  obtain ⟨hk1, hsp1, hw1⟩ := after_eq run_b2 ▸ b2_call
  have hargs1 : EW.mul (ewArg (reg s1.data .rdi) (reg s1.data .rsi))
      (ewArg (reg s1.data .rdx) (reg s1.data .rcx)) =
        (pts m0)[i]'(lt_len hlt) * (1 + (st m0 i).2) := by
    rw [show reg s1.data .rdi = _ from hm1'.regs .rdi (.load 1 0 8) rfl,
      show reg s1.data .rsi = _ from hm1'.regs .rsi (.load 1 8 8) rfl, eval_load, eval_load, hel,
      show reg s1.data .rdx = _ from hm1'.regs .rdx (.bin .xor .W64 (.reg .r13) (.lit 1)) rfl,
      show reg s1.data .rcx = _ from hm1'.regs .rcx (.reg .rbp) rfl, eval_xor, eval_reg, eval_lit,
      eval_reg, one_add_ewArg, ← hI.pow]
    rfl
  have e1 : ∀ r ∈ [Reg64.r12, .r13, .r14, .r15, .rbx, .rbp], reg s1.data r = reg s.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm1 hm1' rfl rfl
  refine Body.call_mul hmul hI.body hS (by decide) (by decide) slots_ok hwf1 hm1 hm1' hpc1 hk1
    hsp1 hw1 fun s2 hpc2 hb2' hprod1 hsv1 _ _ ↦ ?_
  rw [hargs1] at hprod1
  have e2 : ∀ r ∈ [Reg64.r12, .r13, .r14, .r15, .rbx, .rbp], reg s2.data r = reg s.data r := by
    intro r hr
    rw [← e1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hsv1 _ rfl
  -- `b3`: `acc·(1 + r·(1 + pw))`
  have hwf2 := hb2'.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.IndexMleFrom.b4Offset)).toBitVec) hS h64
  refine exec_at (hb3 hp) run_b3 hwf2 (fun _ _ ↦ rfl) hpc2 hb2'.mid_match fun s3 hm3 hpc3 ↦ ?_
  obtain ⟨hk3, hsp3, hw3⟩ := after_eq run_b3 ▸ b3_call
  have hargs3 : EW.mul (ewArg (reg s3.data .rdi) (reg s3.data .rsi))
      (ewArg (reg s3.data .rdx) (reg s3.data .rcx)) = (st m0 (i + 1)).1 := by
    rw [show reg s3.data .rdi = _ from hm3.regs .rdi (.reg .r15) rfl,
      show reg s3.data .rsi = _ from hm3.regs .rsi (.reg .r12) rfl,
      show reg s3.data .rdx = _ from hm3.regs .rdx (.bin .xor .W64 (.reg .rax) (.lit 1)) rfl,
      show reg s3.data .rcx = _ from hm3.regs .rcx (.reg .rdx) rfl, eval_xor, eval_reg, eval_lit,
      eval_reg, eval_reg, eval_reg, one_add_ewArg]
    show EW.mul (ewArg (reg s2.data .r15) (reg s2.data .r12)) (1 + ewRet s2.data) = _
    rw [e2 .r15 (by simp), e2 .r12 (by simp), hI.acc, hprod1, st_succ m0 hlt]
    rfl
  refine Body.call_mul (rs := []) hmul hb2' hS (by decide) (by decide) slots_ok hwf2
    hb2'.mid_match hm3 hpc3 hk3 hsp3 hw3 fun s4 hpc4 hb4' hprod3 hsv3 _ _ ↦ ?_
  rw [hargs3] at hprod3
  have e4 : ∀ r ∈ [Reg64.r13, .r14, .rbx, .rbp], reg s4.data r = reg s.data r := by
    intro r hr
    have hr' : r ∈ [Reg64.r12, .r13, .r14, .r15, .rbx, .rbp] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    rw [← e2 r hr']
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (hsv3 _ rfl).trans (Match.reg_eq hb2'.mid_match hm3 rfl rfl)
  -- `b4`: `pw·pw`, the accumulator kept
  have hwf4 := hb4'.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.IndexMleFrom.b5Offset)).toBitVec)
    hS h64
  refine exec_at (hb4 hp) run_b4 hwf4 (fun _ _ ↦ rfl) hpc4 hb4'.mid_match fun s5 hm5 hpc5 ↦ ?_
  obtain ⟨hk5, hsp5, hw5⟩ := after_eq run_b4 ▸ b4_call
  have hargs5 : EW.mul (ewArg (reg s5.data .rdi) (reg s5.data .rsi))
      (ewArg (reg s5.data .rdx) (reg s5.data .rcx)) = (st m0 (i + 1)).2 := by
    rw [show reg s5.data .rdi = _ from hm5.regs .rdi (.reg .r13) rfl,
      show reg s5.data .rsi = _ from hm5.regs .rsi (.reg .rbp) rfl,
      show reg s5.data .rdx = _ from hm5.regs .rdx (.reg .r13) rfl,
      show reg s5.data .rcx = _ from hm5.regs .rcx (.reg .rbp) rfl, eval_reg, eval_reg]
    show EW.mul (ewArg (reg s4.data .r13) (reg s4.data .rbp))
      (ewArg (reg s4.data .r13) (reg s4.data .rbp)) = _
    rw [e4 .r13 (by simp), e4 .rbp (by simp), hI.pow, st_succ m0 hlt]
    rfl
  have hacc5 : ewArg (reg s5.data .r15) (reg s5.data .r12) = (st m0 (i + 1)).1 := by
    rw [show reg s5.data .r15 = _ from hm5.regs .r15 (.reg .rax) rfl,
      show reg s5.data .r12 = _ from hm5.regs .r12 (.reg .rdx) rfl, eval_reg, eval_reg]
    exact hprod3
  refine Body.call_mul (rs := []) hmul hb4' hS (by decide) (by decide) slots_ok hwf4
    hb4'.mid_match hm5 hpc5 hk5 hsp5 hw5 fun s6 hpc6 hb6' hprod5 hsv5 _ _ ↦ ?_
  rw [hargs5] at hprod5
  have e6 : ∀ r ∈ [Reg64.r14, .rbx], reg s6.data r = reg s.data r := by
    intro r hr
    have hr' : r ∈ [Reg64.r13, .r14, .rbx, .rbp] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl <;> simp
    rw [← e4 r hr']
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      exact (hsv5 _ rfl).trans (Match.reg_eq hb4'.mid_match hm5 rfl rfl)
  have hacc6 : ewArg (reg s6.data .r15) (reg s6.data .r12) = (st m0 (i + 1)).1 := by
    rw [hsv5 .r15 rfl, hsv5 .r12 rfl]; exact hacc5
  -- `b5`: the power kept, advance, compare
  refine exec_at (hb5 hp) run_b5 (Env.wf_nil _) (by intro l h; cases h) hpc6 (match_nil _)
    fun s7 hm7 hpc7 ↦ ?_
  have hb7' := hb6'.of_block (match_nil _) hm7 (Env.wf_nil _) rfl (after_eq run_b5 ▸ b5_keeps)
  have h6 : ∀ r ∈ [Reg64.r14, .rbx], (Env.ofMachine s6.data []).regs r = reg s.data r := e6
  have hpow : ewArg (reg s7.data .r13) (reg s7.data .rbp) = (st m0 (i + 1)).2 := by
    rw [show reg s7.data .r13 = _ from hm7.regs .r13 (.reg .rax) rfl,
      show reg s7.data .rbp = _ from hm7.regs .rbp (.reg .rdx) rfl, eval_reg, eval_reg]
    exact hprod5
  have hacc : ewArg (reg s7.data .r15) (reg s7.data .r12) = (st m0 (i + 1)).1 := by
    rw [show reg s7.data .r15 = reg s6.data .r15 from Match.reg_eq (match_nil _) hm7 rfl rfl,
      show reg s7.data .r12 = reg s6.data .r12 from Match.reg_eq (match_nil _) hm7 rfl rfl]
    exact hacc6
  have hr14 : reg s7.data .r14 = reg m0 .rdi + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [show reg s7.data .r14 = (Sym.bin .add .W64 (.lit 16) (.reg .r14)).eval
      (Env.ofMachine s6.data []) from hm7.regs .r14 _ rfl, eval_add, eval_lit, eval_reg,
      h6 .r14 (by simp), hI.r14, add16]
  have hrbx : reg s7.data .rbx = reg m0 .rdi + BitVec.ofNat 64 (16 * len m0) :=
    (hm7.regs .rbx (.reg .rbx) rfl).trans ((h6 .rbx (by simp)).trans hI.rbx)
  simp only [PcOk] at hpc7
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg, h6 .r14 (by simp),
    h6 .rbx (by simp), hI.r14, hI.rbx, add16, beq_add_left,
    ofNat_beq (by omega) (by omega)] at hpc7
  obtain ⟨hT, hF⟩ := pc_cond hpc7
  by_cases hlast : 16 * (i + 1) = 16 * len m0
  · have hpc7' := hF (by simp [hlast])
    simp only [NativeRustcVmX64.Vm.IndexMleFrom.b5_length] at hpc7'
    refine exec_at (hb6 hp) run_b6 (Env.wf_nil _) (by intro l h; cases h) hpc7' (match_nil _)
      fun s8 hm8 hpc8 ↦ ?_
    have hb8' := hb7'.of_block (match_nil _) hm8 (Env.wf_nil _) rfl (after_eq run_b6 ▸ b6_keeps)
    simp only [PcOk] at hpc8
    refine Eventually.mono (finish hp hpre (hpc8.trans (lbl_4 hp)) hb8' ?_) fun _ h ↦ Or.inl h
    rw [show reg s8.data .r15 = reg s7.data .r15 from Match.reg_eq (match_nil _) hm8 rfl rfl,
      show reg s8.data .r12 = reg s7.data .r12 from Match.reg_eq (match_nil _) hm8 rfl rfl,
      hacc, show i + 1 = len m0 by omega]
  · exact .done _ (Or.inr ⟨(hT (by simp [hlast])).trans (lbl_3 hp),
      ⟨hb7', by omega, hr14, hrbx, hacc, hpow⟩⟩)

/-- **`index_mle_from` meets its contract.** -/
theorem indexMleFrom_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.IndexMleFrom.entryLabel) IndexMleFromPre IndexMleFromPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hS := hpre.1
  have h64 : 64 ≤ indexMleFromStack := by decide
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h64)
    fun _ h ↦ h
  have hl : len m0 = (reg m0 .rsi).toNat := rfl
  have hlen := lt_of_offStack hpre.2.1.2 hpre.2.2
  have hx : BitVec.ofNat 64 (len m0) = m0.regs.get64 .rsi := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine exec_then (hb0 hp) run_b0 hwf (by intro l h; cases h) match_frame fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.IndexMleFrom.b0_length] at hpc1
  rw [eval_test, eval_reg, Env.ofMachine_regs, ← hx, ofNat_beq (by omega) (by decide)] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hz : len m0 = 0
  · -- `|point| = 0`: return `1`.
    have hpc1 := hT (decide_eq_true hz)
    refine exec_at (hb7 hp) (exec_after run_b0 run_b7) hwf (by intro l h; cases h)
      (hpc1.trans (lbl_1 hp)) hm1 fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmX64.Vm.IndexMleFrom.b7_length] at hpc2
    obtain ⟨hw, hregs, hmem, hsp⟩ := after_eq run_b7 ▸ b7_entry
    refine finish hp hpre hpc2 (Body.of_entry hS h64 hm2 hsp hw hregs hmem) ?_
    rw [show reg s2.data .r15 = 1#64 from hm2.regs .r15 _ rfl,
      show reg s2.data .r12 = 0#64 from hm2.regs .r12 _ rfl, hz]
    rfl
  · -- the loop.
    have hpc1 := hF (fun h ↦ hz (of_decide_eq_true h))
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf (by intro l h; cases h) hpc1 hm1
      fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmX64.Vm.IndexMleFrom.b1_length] at hpc2
    obtain ⟨hw, hregs, hmem, hsp⟩ := after_eq run_b1 ▸ b1_entry
    have hI : Inv m0 0 s2.data := by
      have hbx := hm2.regs .rbx _ rfl
      rw [eval_add, eval_shl_lit (hj := by decide), eval_reg, eval_reg] at hbx
      refine ⟨Body.of_entry hS h64 hm2 hsp hw hregs hmem, Nat.pos_of_ne_zero hz, ?_, ?_, ?_, ?_⟩
      · show s2.data.regs.get64 .r14 = _
        rw [hm2.regs .r14 _ rfl, add_ofNat_zero]
        rfl
      · show s2.data.regs.get64 .rbx = _
        rw [hbx]
        congr 1
        apply BitVec.eq_of_toNat_eq
        show (m0.regs.get64 .rsi <<< 4).toNat = (BitVec.ofNat 64 (16 * len m0)).toNat
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        show (len m0) * 2 ^ 4 % 2 ^ 64 = _
        omega
      · show ewArg (s2.data.regs.get64 .r15) (s2.data.regs.get64 .r12) = _
        rw [hm2.regs .r15 _ rfl, hm2.regs .r12 _ rfl]
        rfl
      · show ewArg (s2.data.regs.get64 .r13) (s2.data.regs.get64 .rbp) = _
        rw [hm2.regs .r13 _ rfl, hm2.regs .rbp _ rfl]
        rfl
    refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.IndexMleFrom.b2Offset) ∧ ∃ i, len m0 - i = n ∧
      Inv m0 i s.data) (fun n s ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, hI⟩
    refine Eventually.mono (step hp hmul hpre hpc hI) fun s' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨len m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Arrays.IndexMleFrom
