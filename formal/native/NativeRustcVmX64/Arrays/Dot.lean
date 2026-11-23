module

public import NativeRustcVmX64.Arrays.Dot.Exec
public import NativeRustcVm.Arrays.Folds
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `dot` on x86-64

**`dot_spec`**: rustc's `dot`, placed anywhere in the program, meets `DotPre`/`DotPost` given
`EW::mul`'s contract. The prologue (`b0`) pushes RBP, R15-R12, RBX, RAX and takes the common length
`n`; at `n = 0` it returns `0` (`b5`, `b6`); else (`b1`) the loop (`b2`, `EW::mul`, `b3`) adds
`left[i]·right[i]` to the accumulator (R13, R12) for `i < n`, RBP the byte offset `16 i` (`Inv`),
and the epilogue (`b4`, `b6`) returns it.
-/

namespace NativeRustcVmX64.Arrays.Dot

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Dot NativeVm.Model NativeRustcVmX64.Field
open NativeRustcVm (ewsOf ewOf)

public section

/-- The left slice at the entry. -/
abbrev lft (m : MachineData) : List EW := ewsOf m.dmem (reg m .rdi) (reg m .rsi).toNat
/-- The right slice at the entry. -/
abbrev rgt (m : MachineData) : List EW := ewsOf m.dmem (reg m .rdx) (reg m .rcx).toNat
/-- The common length. -/
abbrev cnt (m : MachineData) : Nat := min (reg m .rsi).toNat (reg m .rcx).toNat

/-- The sum of the first `i` products. -/
def acc (m : MachineData) (i : Nat) : EW :=
  (List.zipWith (· * ·) ((lft m).take i) ((rgt m).take i)).foldl (· + ·) 0

theorem dot_eq_acc (m : MachineData) :
    dot (slice m (reg m .rdi) (reg m .rsi)) (slice m (reg m .rdx) (reg m .rcx)) = acc m (cnt m) := by
  unfold slice acc
  rw [NativeRustcVm.dot_eq, NativeRustcVm.zipWith_take_min]
  simp

theorem acc_succ (m : MachineData) {i : Nat} (h : i < cnt m) :
    acc m (i + 1) = acc m i + (lft m)[i]'(by simp; exact Nat.lt_of_lt_of_le h (Nat.min_le_left _ _)) *
      (rgt m)[i]'(by simp; exact Nat.lt_of_lt_of_le h (Nat.min_le_right _ _)) :=
  NativeRustcVm.zipFold_take_succ _ _ _ _ _ _ _

/-- **The loop head** `NativeRustcVmX64.Vm.Dot.label_3`, `i` products summed. -/
structure Inv (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 64 dotStack slots 0 0 st
  lt : i < cnt m0
  r14 : reg st .r14 = BitVec.ofNat 64 (16 * cnt m0)
  rbp : reg st .rbp = BitVec.ofNat 64 (16 * i)
  r15 : reg st .r15 = reg m0 .rdi
  rbx : reg st .rbx = reg m0 .rdx
  acc : ewArg (reg st .r13) (reg st .r12) = acc m0 i

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Dot.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Dot.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Dot.b2Offset) ∧
    b2b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Dot.b2Offset + b2a.length) := by
  have h := b2_in_code.trans hp.1 (by simp [b2])
  rw [← List.take_append_drop 3 b2] at h
  exact h.append
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Dot.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Dot.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Dot.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Dot.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Dot.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.Dot.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.Dot.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Dot.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.Dot.b5Offset) :=
  hp.label NativeRustcVmX64.Vm.Dot.label_1_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Dot.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.Dot.b2Offset) :=
  hp.label NativeRustcVmX64.Vm.Dot.label_3_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Dot.label_4 = Host.addrOf (k + NativeRustcVmX64.Vm.Dot.b6Offset) :=
  hp.label NativeRustcVmX64.Vm.Dot.label_4_at

/-- `dot`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ DotPost m0 st.data

/-- **The epilogue** `b6`: from a body, the accumulator returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : DotPre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Dot.b6Offset)) (hb : Body m0 64 dotStack slots 0 0 st.data)
    (hacc : ewArg (reg st.data .r13) (reg st.data .r12) = acc m0 (cnt m0)) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hS := hpre.1
  have h64 : 64 ≤ dotStack := by decide
  refine exec_at (hb6 hp) run_b6 (hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h64)
    (by intro l h; cases h) hpc hb.mid_match fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hpc'', hrsp, hdm, hsaved⟩ := hb.done hS h64 hm' hpc'
    (after_eq run_b6 ▸ b6_restores).1 (after_eq run_b6 ▸ b6_restores).2
    (fun _ _ ↦ not_inRange_zero _)
  have h0 := hm'.regs .rax _ rfl
  have h1 := hm'.regs .rdx _ rfl
  refine ⟨hpc'', hrsp, ?_, fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  rw [dot_eq_acc, ← hacc]
  show ewArg (st'.data.regs.get64 .rax) (st'.data.regs.get64 .rdx) = _
  rw [h0, h1]
  rfl

omit [Host] in
theorem sixteen_add (i : Nat) :
    BitVec.ofNat 64 16 + BitVec.ofNat 64 (16 * i) = BitVec.ofNat 64 (16 * (i + 1)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

/-- **A turn of the loop**: `left[i]·right[i]` added, back at the head or out of the loop and
returned. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : DotPre m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Dot.b2Offset)) (hI : Inv m0 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Dot.b2Offset) ∧ Inv m0 (i + 1) st'.data)) st := by
  obtain ⟨hS, ⟨hrL, hoL⟩, ⟨hrR, hoR⟩⟩ := hpre
  have h64 : 64 ≤ dotStack := by decide
  have hiL : i < (reg m0 .rsi).toNat := Nat.lt_of_lt_of_le hI.lt (Nat.min_le_left _ _)
  have hiR : i < (reg m0 .rcx).toNat := Nat.lt_of_lt_of_le hI.lt (Nat.min_le_right _ _)
  have hlen := lt_of_offStack hrL.2 hoL
  -- `left[i]`
  have hwf1 := wf_two (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h64) hI.body.kept
    (elem_mapped hrL hI.body.kept hiL) (elem_apart_frame hS h64 hrL hoL hiL)
  have hm1 : Match (Env.ofMachine st.data [(stackBelow m0 64, 64 + 8),
      (reg m0 .rdi + BitVec.ofNat 64 (16 * i), 16)]) ldS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hI.body.rsp, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg st.data .r15) (reg st.data .rbp) = _
        rw [add_eval, hI.r15, hI.rbp]
        simp, trivial⟩
  refine exec_at (hb2 hp).1 run_b2a hwf1 (by intro l h; cases h) hpc hm1 fun st1 hm1' hpc1 ↦ ?_
  simp only [PcOk, show b2a.length = 3 from rfl] at hpc1
  have hb1 := hI.body.of_block hm1 hm1' hwf1 rfl (after_eq run_b2a ▸ b2a_keeps)
  have hL : ewArg (reg st1.data .rdi) (reg st1.data .rsi) = (lft m0)[i]'(by simp; exact hiL) := by
    rw [ew_of_loads (r := 1) (off := 0) hm1' rfl rfl]
    show ewOf st.data.dmem (reg m0 .rdi + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 0) = _
    rw [add_ofNat_zero]
    exact elem_of_apart hI.body.same hS hrL.2 hoL (apart_zero _ _) noWrap_zero hiL
  have e1 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st1.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm1 hm1' rfl rfl
  -- `right[i]`, then the call
  have hwf2 := wf_two (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Dot.b3Offset)).toBitVec)
    (stackOk_mono hS h64) hb1.kept (elem_mapped hrR hb1.kept hiR)
    (elem_apart_frame hS h64 hrR hoR hiR)
  have hm2 : Match (Env.ofMachine st1.data [(stackBelow m0 64, 64 + 8),
      (reg m0 .rdx + BitVec.ofNat 64 (16 * i), 16)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.Dot.b3Offset)).toBitVec) rdS st1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb1.rsp, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg st1.data .rbx) (reg st1.data .rbp) = _
        rw [add_eval, e1 .rbx (by simp), e1 .rbp (by simp), hI.rbx, hI.rbp]
        simp, trivial⟩
  refine exec_at (hb2 hp).2 run_b2b hwf2 (fun _ _ ↦ rfl) hpc1 hm2 fun st2 hm2' hpc2 ↦ ?_
  obtain ⟨hk2, hsp2, hw2⟩ := after_eq run_b2b ▸ b2b_call
  have hR : ewArg (reg st2.data .rdx) (reg st2.data .rcx) = (rgt m0)[i]'(by simp; exact hiR) := by
    rw [ew_of_loads (r := 1) (off := 0) hm2' rfl rfl]
    show ewOf st1.data.dmem (reg m0 .rdx + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 0) = _
    rw [add_ofNat_zero]
    exact elem_of_apart hb1.same hS hrR.2 hoR (apart_zero _ _) noWrap_zero hiR
  have hL2 : ewArg (reg st2.data .rdi) (reg st2.data .rsi) = (lft m0)[i]'(by simp; exact hiL) := by
    rw [← hL, show reg st2.data .rdi = reg st1.data .rdi from Match.reg_eq hm2 hm2' rfl rfl,
      show reg st2.data .rsi = reg st1.data .rsi from Match.reg_eq hm2 hm2' rfl rfl]
  have e2 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st2.data r = reg st.data r := by
    intro r hr
    rw [← e1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm2 hm2' rfl rfl
  refine Body.call_mul hmul hb1 hS (by decide) (by decide) slots_ok hwf2 hm2 hm2' hpc2 hk2 hsp2
    hw2 fun st3 hpc3 hb3' hprod hsv _ _ ↦ ?_
  rw [hL2, hR] at hprod
  have e3 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st3.data r = reg st.data r := by
    intro r hr
    have hc : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hsv r hc, e2 r hr]
  -- `b3`: accumulate, advance, compare
  refine exec_at (hb3 hp) run_b3 (Env.wf_nil _) (by intro l h; cases h) hpc3 (match_nil _)
    fun st4 hm4 hpc4 ↦ ?_
  have hb4' := hb3'.of_block (match_nil _) hm4 (Env.wf_nil _) rfl (after_eq run_b3 ▸ b3_keeps)
  have hlt := hI.lt
  have hc1 : cnt m0 ≤ (reg m0 .rsi).toNat := Nat.min_le_left _ _
  have h3 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
      (Env.ofMachine st3.data []).regs r = reg st.data r := e3
  have h12 : reg st4.data .r12 = (Sym.bin .xor .W64 (.reg .r12) (.reg .rdx)).eval
      (Env.ofMachine st3.data []) := hm4.regs .r12 _ rfl
  have h13 : reg st4.data .r13 = (Sym.bin .xor .W64 (.reg .r13) (.reg .rax)).eval
      (Env.ofMachine st3.data []) := hm4.regs .r13 _ rfl
  have hacc : ewArg (reg st4.data .r13) (reg st4.data .r12) = acc m0 (i + 1) := by
    have hprod' : ewRet st3.data =
        (lft m0)[i]'(by simp; exact hiL) * (rgt m0)[i]'(by simp; exact hiR) := hprod
    rw [acc_succ m0 hI.lt, ← hI.acc, ← hprod', h13, h12, eval_xor, eval_xor, eval_reg, eval_reg,
      eval_reg, eval_reg, h3 .r13 (by simp), h3 .r12 (by simp)]
    rfl
  have hrbp : reg st4.data .rbp = BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [show reg st4.data .rbp = (Sym.bin .add .W64 (.lit 16) (.reg .rbp)).eval
      (Env.ofMachine st3.data []) from hm4.regs .rbp _ rfl, eval_add, eval_lit, eval_reg,
      h3 .rbp (by simp), hI.rbp]
    exact sixteen_add i
  have hr14 : reg st4.data .r14 = BitVec.ofNat 64 (16 * cnt m0) :=
    (hm4.regs .r14 (.reg .r14) rfl).trans ((h3 .r14 (by simp)).trans hI.r14)
  have hr15 : reg st4.data .r15 = reg m0 .rdi :=
    (hm4.regs .r15 (.reg .r15) rfl).trans ((h3 .r15 (by simp)).trans hI.r15)
  have hrbx : reg st4.data .rbx = reg m0 .rdx :=
    (hm4.regs .rbx (.reg .rbx) rfl).trans ((h3 .rbx (by simp)).trans hI.rbx)
  simp only [PcOk] at hpc4
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg, h3 .r14 (by simp),
    h3 .rbp (by simp), hI.r14, hI.rbp, sixteen_add, ofNat_beq (by omega) (by omega)] at hpc4
  obtain ⟨hT, hF⟩ := pc_cond hpc4
  by_cases hlast : 16 * cnt m0 = 16 * (i + 1)
  · have hpc4' := hF (by simp [hlast])
    simp only [NativeRustcVmX64.Vm.Dot.b3_length] at hpc4'
    refine exec_at (hb4 hp) run_b4 (Env.wf_nil _) (by intro l h; cases h) hpc4' (match_nil _)
      fun st5 hm5 hpc5 ↦ ?_
    have hb5' := hb4'.of_block (match_nil _) hm5 (Env.wf_nil _) rfl (after_eq run_b4 ▸ b4_keeps)
    simp only [PcOk] at hpc5
    refine Eventually.mono (finish hp ⟨hS, ⟨hrL, hoL⟩, ⟨hrR, hoR⟩⟩ (hpc5.trans (lbl_4 hp)) hb5' ?_)
      fun _ h ↦ Or.inl h
    rw [show reg st5.data .r13 = reg st4.data .r13 from Match.reg_eq (match_nil _) hm5 rfl rfl,
      show reg st5.data .r12 = reg st4.data .r12 from Match.reg_eq (match_nil _) hm5 rfl rfl,
      hacc, show i + 1 = cnt m0 by omega]
  · exact .done _ (Or.inr ⟨(hT (by simp [hlast])).trans (lbl_3 hp),
      ⟨hb4', by omega, hr14, hrbp, hr15, hrbx, hacc⟩⟩)

/-- **`dot` meets its contract.** -/
theorem dot_spec (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hS := hpre.1
  have h64 : 64 ≤ dotStack := by decide
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h64)
    fun _ h ↦ h
  have hlen := lt_of_offStack hpre.2.1.1.2 hpre.2.1.2
  have hm : Match (frameEnv m0 m0 64) entryS m0 := match_frame
  refine exec_then (hb0 hp) run_b0 hwf (by intro l h; cases h) hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.Dot.b0_length] at hpc1
  rw [eval_test, eval_min, ofNat_beq (by omega) (by decide)] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hz : cnt m0 = 0
  · -- `n = 0`: return `0`.
    have hpc1 := hT (by simp only [Env.ofMachine_regs]; exact decide_eq_true hz)
    refine exec_at (hb5 hp) (exec_after run_b0 run_b5) hwf (by intro l h; cases h)
      (hpc1.trans (lbl_1 hp)) hm1 fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmX64.Vm.Dot.b5_length] at hpc2
    obtain ⟨hw, hregs, hmem, hsp⟩ := after_eq run_b5 ▸ b5_entry
    have hb := Body.of_entry (oa := 0) (on := 0) hS h64 hm2 hsp hw hregs hmem
    refine finish hp hpre hpc2 hb ?_
    rw [show reg st2.data .r13 = 0#64 from hm2.regs .r13 _ rfl,
      show reg st2.data .r12 = 0#64 from hm2.regs .r12 _ rfl]
    unfold acc
    rw [hz]
    rfl
  · -- `n > 0`: the loop.
    have hpc1 := hF (by simp only [Env.ofMachine_regs]; exact fun h ↦ hz (of_decide_eq_true h))
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf (by intro l h; cases h) hpc1 hm1
      fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmX64.Vm.Dot.b1_length] at hpc2
    obtain ⟨hw, hregs, hmem, hsp⟩ := after_eq run_b1 ▸ b1_entry
    have hI : Inv m0 0 st2.data := by
      have h14 := hm2.regs .r14 _ rfl
      rw [eval_shl_lit (hj := by decide), eval_min] at h14
      refine ⟨Body.of_entry hS h64 hm2 hsp hw hregs hmem, Nat.pos_of_ne_zero hz, ?_,
        hm2.regs .rbp _ rfl, hm2.regs .r15 _ rfl, hm2.regs .rbx _ rfl, ?_⟩
      · show st2.data.regs.get64 .r14 = _
        rw [h14]
        apply BitVec.eq_of_toNat_eq
        have hc1 : cnt m0 ≤ (reg m0 .rsi).toNat := Nat.min_le_left _ _
        have hc2 : cnt m0 < 2 ^ 64 := by omega
        show ((BitVec.ofNat 64 (cnt m0)) <<< 4).toNat = (BitVec.ofNat 64 (16 * cnt m0)).toNat
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        omega
      · show ewArg (st2.data.regs.get64 .r13) (st2.data.regs.get64 .r12) = _
        rw [hm2.regs .r13 _ rfl, hm2.regs .r12 _ rfl]
        rfl
    refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Dot.b2Offset) ∧ ∃ i, cnt m0 - i = n ∧
      Inv m0 i st.data) (fun n st ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, hI⟩
    refine Eventually.mono (step hp hmul hpre hpc hI) fun st' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨cnt m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Arrays.Dot
