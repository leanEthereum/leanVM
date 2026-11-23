module

public import NativeRustcVmX64.Arrays.Powers.Exec
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Powers.Names

/-!
# `powers` on x86-64

**`powers_spec`**: rustc's `powers`, placed anywhere in the program, meets `PowersPre`/
`PowersPost` given `EW::mul`'s contract. At `|out| = 0` it returns at once (`b0`, `b5`); else the
prologue (`b1`) pushes R15, R14, R12, RBX, RAX, and the loop (`b2`: the stores, `EW::mul`; `b3`)
stores the power (RAX, RDX) at R14 = `out + 16 i` and multiplies it by the base for `i < |out|`
(`Inv`), and the epilogue (`b4`, `b5`) returns.
-/

namespace NativeRustcVmX64.Arrays.Powers

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Powers NativeVm.Model
  NativeRustcVmX64.Field
open NativeRustcVm (EWsAt)

public section

/-- `out`. -/
abbrev out (m : MachineData) : BitVec 64 := reg m .rdx
/-- `|out|`. -/
abbrev len (m : MachineData) : Nat := (reg m .rcx).toNat
/-- The base. -/
abbrev base (m : MachineData) : EW := ewArg (reg m .rdi) (reg m .rsi)

/-- The model's fold after `n` steps. -/
@[expose] def P (b : EW) (n : Nat) : Array EW × EW :=
  (List.range n).foldl (fun (acc : Array EW × EW) _ ↦ (acc.1.push acc.2, acc.2 * b)) (#[], 1)

theorem P_succ (b : EW) (n : Nat) : P b (n + 1) = ((P b n).1.push (P b n).2, (P b n).2 * b) := by
  unfold P
  rw [List.range_succ, List.foldl_append]
  rfl

theorem length_P (b : EW) (n : Nat) : (P b n).1.toList.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [P_succ]; simp [ih]

theorem powers_eq (b : EW) (n : Nat) : powers b n = (P b n).1 := rfl

/-- **The loop head** `NativeRustcVmX64.Vm.Powers.label_2`, `i` powers stored. -/
structure Inv (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 48 powersStack slots (out m0) (16 * len m0) st
  lt : i < len m0
  r14 : reg st .r14 = out m0 + BitVec.ofNat 64 (16 * i)
  rbx : reg st .rbx = out m0 + BitVec.ofNat 64 (16 * len m0)
  r12 : reg st .r12 = reg m0 .rdi
  r15 : reg st .r15 = reg m0 .rsi
  pw : ewArg (reg st .rax) (reg st .rdx) = (P (base m0) i).2
  written : EWsAt st.dmem (out m0) (P (base m0) i).1.toList

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Powers.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Powers.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : s1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Powers.b2Offset) ∧
    s2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Powers.b2Offset + s1.length) := by
  have h := b2_in_code.trans hp.1 (by simp [b2])
  rw [← List.take_append_drop 3 b2] at h
  exact h.append
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Powers.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb45 (hp : Placed code k) : b45.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Powers.b4Offset) :=
  isInfixAt_concat (b4_in_code.trans hp.1 (by simp [b4]))
    (b5_in_code.trans hp.1 (by simp [b5]))
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.Powers.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Powers.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.Powers.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.Powers.entry_at
theorem lbl_2 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Powers.label_2 = Host.addrOf (k + NativeRustcVmX64.Vm.Powers.b2Offset) :=
  hp.label NativeRustcVmX64.Vm.Powers.label_2_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.Powers.label_4 = Host.addrOf (k + NativeRustcVmX64.Vm.Powers.b5Offset) :=
  hp.label NativeRustcVmX64.Vm.Powers.label_4_at

/-- `powers`' postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ PowersPost m0 st.data

/-- **The epilogue** `b4`, `b5`: from a body with every power stored, returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : PowersPre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Powers.b4Offset))
    (hb : Body m0 48 powersStack slots (out m0) (16 * len m0) st.data)
    (hw : EWsAt st.data.dmem (out m0) (P (base m0) (len m0)).1.toList) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hS := hpre.1
  have h48 : 48 ≤ powersStack := by decide
  refine exec_at (hb45 hp) run_b45 (hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h48)
    (by intro l h; cases h) hpc hb.mid_match fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hpc'', hrsp, hdm, hsaved⟩ := hb.done hS h48 hm' hpc'
    (after_eq run_b45 ▸ b45_restores).1 (after_eq run_b45 ▸ b45_restores).2
    (ret_not_in hS hpre.2.1.2 hpre.2.2)
  refine ⟨hpc'', hrsp, ?_, fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  rw [hdm, powers_eq]
  exact hw

omit [Host] in
theorem sixteen_add (a : BitVec 64) (i : Nat) :
    BitVec.ofNat 64 16 + (a + BitVec.ofNat 64 (16 * i)) = a + BitVec.ofNat 64 (16 * (i + 1)) := by
  rw [BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 16 * i + 16 = 16 * (i + 1) by omega]

/-- **A turn of the loop**: the power stored in `out[i]`, multiplied by the base, back at the head
or out of the loop and returned. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : PowersPre m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Powers.b2Offset)) (hI : Inv m0 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Powers.b2Offset) ∧ Inv m0 (i + 1) st'.data)) st := by
  obtain ⟨hS, hr, ho⟩ := hpre
  have h48 : 48 ≤ powersStack := by decide
  have hlt := hI.lt
  have hlen := lt_of_offStack hr.2 ho
  have hnw := hr.2
  have hl : len m0 = (reg m0 .rcx).toNat := rfl
  have hS1 := hS.1
  have hnw' : (out m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hnw
  -- `s1`: the stores
  obtain ⟨hwf1, hm1⟩ := hI.body.at_elem (ret := 0) hS h48 hr ho hI.lt (x := .reg .r14) (o := 0)
    (by rw [eval_reg, add_ofNat_zero]; exact hI.r14)
  refine exec_at (hb2 hp).1 run_s1 hwf1 (by intro l h; cases h) hpc hm1 fun st1 hm1' hpc1 ↦ ?_
  simp only [PcOk, show s1.length = 3 from rfl] at hpc1
  obtain ⟨hk1, hw1, hu1, hv1⟩ := after_eq run_s1 ▸ s1_store
  have hb1 := hI.body.of_store hwf1 hm1 hm1' hk1 hw1
    (fun p h ↦ inRange_sub hnw (by omega) h) (fun p hp ↦ (slots_ok p hp).2)
  have hwr1 : ∀ p, ¬InRange (out m0 + BitVec.ofNat 64 (16 * i)) 16 p →
      st1.data.dmem.get? p = st.data.dmem.get? p := fun p hp ↦
    hm1'.get?_mem0 hwf1 fun h ↦ hp (written_region rfl hwf1 le_rfl hw1 h)
  have hwritten1 : EWsAt st1.data.dmem (out m0) (P (base m0) (i + 1)).1.toList := by
    rw [P_succ, Array.toList_push, NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_singleton,
      length_P]
    refine ⟨ewsAt_congr hI.written fun j hj ↦ hwr1 _ fun h ↦ ?_, ?_⟩
    · rw [length_P] at hj
      rw [Sym.inRange_iff (by unfold NoWrap at hnw; rw [toNat_add_ofNat _ _ (by omega)]; omega),
        toNat_add_ofNat _ _ (by unfold NoWrap at hnw; omega),
        toNat_add_ofNat _ _ (by unfold NoWrap at hnw; omega)] at h
      omega
    · have := ewAt_of_writes hm1' (r := 1) (o := 0) rfl le_rfl hu1 hv1
      rw [add_ofNat_zero] at this
      rw [← hI.pw]
      exact this
  have e1 : ∀ r ∈ [Reg64.rax, .rdx, .rbx, .r12, .r14, .r15], reg st1.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm1 hm1' rfl rfl
  -- `s2`: the call
  have hwf2 := hb1.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Powers.b3Offset)).toBitVec) hS h48
  refine exec_at (hb2 hp).2 run_s2 hwf2 (fun _ _ ↦ rfl) hpc1 hb1.mid_match fun st2 hm2' hpc2 ↦ ?_
  obtain ⟨hk2, hsp2, hw2⟩ := after_eq run_s2 ▸ s2_call
  have hprodArgs : EW.mul (ewArg (reg st2.data .rdi) (reg st2.data .rsi))
      (ewArg (reg st2.data .rdx) (reg st2.data .rcx)) = (P (base m0) (i + 1)).2 := by
    rw [show reg st2.data .rdi = reg st.data .rax from
        (hm2'.regs .rdi (.reg .rax) rfl).trans (e1 .rax (by simp)),
      show reg st2.data .rsi = reg st.data .rdx from
        (hm2'.regs .rsi (.reg .rdx) rfl).trans (e1 .rdx (by simp)),
      show reg st2.data .rdx = reg m0 .rdi from
        (hm2'.regs .rdx (.reg .r12) rfl).trans ((e1 .r12 (by simp)).trans hI.r12),
      show reg st2.data .rcx = reg m0 .rsi from
        (hm2'.regs .rcx (.reg .r15) rfl).trans ((e1 .r15 (by simp)).trans hI.r15),
      hI.pw, P_succ]
    rfl
  refine Body.call_mul (rs := []) hmul hb1 hS (by decide) (by decide) slots_ok hwf2
    hb1.mid_match hm2' hpc2 hk2 hsp2 hw2 fun st3 hpc3 hb3' hprod hsv hso _ ↦ ?_
  rw [hprodArgs] at hprod
  have hwritten3 : EWsAt st3.data.dmem (out m0) (P (base m0) (i + 1)).1.toList :=
    ewsAt_congr hwritten1 fun j hj ↦ hso _ fun h ↦ by
      rw [length_P] at hj
      exact not_inRange_of_apart (apart_mono ho (Nat.le_add_right _ 8)) hnw
        (by unfold NoWrap; rw [stackBelow_toNat hS.1]; have := (rspOf m0).isLt; omega)
        (by omega) h
  have e3 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg st3.data r = reg st.data r := by
    intro r hr
    have hr' : r ∈ [Reg64.rax, .rdx, .rbx, .r12, .r14, .r15] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [← e1 r hr']
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (hsv _ rfl).trans (Match.reg_eq hb1.mid_match hm2' rfl rfl)
  -- `b3`: advance, compare
  refine exec_at (hb3 hp) run_b3 (Env.wf_nil _) (by intro l h; cases h) hpc3 (match_nil _)
    fun st4 hm4 hpc4 ↦ ?_
  have hb4' := hb3'.of_block (match_nil _) hm4 (Env.wf_nil _) rfl (after_eq run_b3 ▸ b3_keeps)
  have hdm4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq (Env.wf_nil _) rfl
  have h3 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15],
      (Env.ofMachine st3.data []).regs r = reg st.data r := e3
  have hpw : ewArg (reg st4.data .rax) (reg st4.data .rdx) = (P (base m0) (i + 1)).2 := by
    rw [← hprod]
    rw [show reg st4.data .rax = reg st3.data .rax from Match.reg_eq (match_nil _) hm4 rfl rfl,
      show reg st4.data .rdx = reg st3.data .rdx from Match.reg_eq (match_nil _) hm4 rfl rfl]
    rfl
  have hr14 : reg st4.data .r14 = out m0 + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [show reg st4.data .r14 = (Sym.bin .add .W64 (.lit 16) (.reg .r14)).eval
      (Env.ofMachine st3.data []) from hm4.regs .r14 _ rfl, eval_add, eval_lit, eval_reg,
      h3 .r14 (by simp), hI.r14]
    exact sixteen_add _ i
  have hrbx : reg st4.data .rbx = out m0 + BitVec.ofNat 64 (16 * len m0) :=
    (hm4.regs .rbx (.reg .rbx) rfl).trans ((h3 .rbx (by simp)).trans hI.rbx)
  have hr12 : reg st4.data .r12 = reg m0 .rdi :=
    (hm4.regs .r12 (.reg .r12) rfl).trans ((h3 .r12 (by simp)).trans hI.r12)
  have hr15 : reg st4.data .r15 = reg m0 .rsi :=
    (hm4.regs .r15 (.reg .r15) rfl).trans ((h3 .r15 (by simp)).trans hI.r15)
  simp only [PcOk] at hpc4
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg, h3 .r14 (by simp),
    h3 .rbx (by simp), hI.r14, hI.rbx, sixteen_add, beq_add_left,
    ofNat_beq (by omega) (by omega)] at hpc4
  obtain ⟨hT, hF⟩ := pc_cond hpc4
  by_cases hlast : 16 * (i + 1) = 16 * len m0
  · have hpc4' := hF (by simp [hlast])
    simp only [NativeRustcVmX64.Vm.Powers.b3_length] at hpc4'
    refine Eventually.mono (finish hp ⟨hS, hr, ho⟩ hpc4' hb4' ?_) fun _ h ↦ Or.inl h
    rw [hdm4, show len m0 = i + 1 by omega]
    exact hwritten3
  · exact .done _ (Or.inr ⟨(hT (by simp [hlast])).trans (lbl_2 hp),
      ⟨hb4', by omega, hr14, hrbx, hr12, hr15, hpw, hdm4 ▸ hwritten3⟩⟩)

/-- **`powers` meets its contract.** -/
theorem powers_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.Powers.entryLabel) PowersPre PowersPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hS := hpre.1
  have h48 : 48 ≤ powersStack := by decide
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h48)
    fun _ h ↦ h
  have hlen := lt_of_offStack hpre.2.1.2 hpre.2.2
  have hl : len m0 = (reg m0 .rcx).toNat := rfl
  have hx : BitVec.ofNat 64 (len m0) = m0.regs.get64 .rcx := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm : Match (frameEnv m0 m0 48) entryS m0 := match_frame
  refine exec_then (hb0 hp) run_b0 hwf (by intro l h; cases h) hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.Powers.b0_length] at hpc1
  rw [eval_test, eval_reg, Env.ofMachine_regs,
    ← hx,
    ofNat_beq (by omega) (by decide)] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hz : len m0 = 0
  · -- `|out| = 0`: return at once.
    have hpc1 := hT (decide_eq_true hz)
    refine exec_at (hb5 hp) (exec_after run_b0 run_b5) hwf (by intro l h; cases h)
      (hpc1.trans (lbl_4 hp)) hm1 fun st2 hm2 hpc2 ↦ .done _ ?_
    obtain ⟨hk, hmem, hsp⟩ := after_eq run_b5 ▸ b5_leaf
    obtain ⟨hpc', hrsp, hso, hsaved⟩ := leaf_done (stackOk_mono hS h48) hm2 hpc2 hsp hk
      (by rw [hmem]; intro w hw; cases hw)
    have hdm : st2.data.dmem = m0.dmem := hm2.dmem_eq hwf hmem
    refine ⟨hpc', hrsp, ?_, fun p _ ↦ by rw [hdm], hsaved⟩
    rw [show (reg m0 .rcx).toNat = 0 from hz]
    exact NativeRustcVm.ewsAt_nil _ _
  · -- the loop.
    have hpc1 := hF (fun h ↦ hz (of_decide_eq_true h))
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf (by intro l h; cases h) hpc1 hm1
      fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmX64.Vm.Powers.b1_length] at hpc2
    obtain ⟨hw, hregs, hmem, hsp⟩ := after_eq run_b1 ▸ b1_entry
    have hI : Inv m0 0 st2.data := by
      have hbx := hm2.regs .rbx _ rfl
      rw [eval_add, eval_shl_lit (hj := by decide), eval_reg, eval_reg] at hbx
      refine ⟨Body.of_entry hS h48 hm2 hsp hw hregs hmem, Nat.pos_of_ne_zero hz, ?_, ?_,
        hm2.regs .r12 _ rfl, hm2.regs .r15 _ rfl, ?_, NativeRustcVm.ewsAt_nil _ _⟩
      · show st2.data.regs.get64 .r14 = _
        rw [hm2.regs .r14 _ rfl, add_ofNat_zero]
        rfl
      · show st2.data.regs.get64 .rbx = _
        rw [hbx]
        congr 1
        apply BitVec.eq_of_toNat_eq
        show (m0.regs.get64 .rcx <<< 4).toNat = (BitVec.ofNat 64 (16 * len m0)).toNat
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        show (len m0) * 2 ^ 4 % 2 ^ 64 = _
        omega
      · show ewArg (st2.data.regs.get64 .rax) (st2.data.regs.get64 .rdx) = _
        rw [hm2.regs .rax _ rfl, hm2.regs .rdx _ rfl]
        rfl
    refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Powers.b2Offset) ∧ ∃ i, len m0 - i = n ∧
      Inv m0 i st.data) (fun n st ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, hI⟩
    refine Eventually.mono (step hp hmul hpre hpc hI) fun st' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨len m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Arrays.Powers
