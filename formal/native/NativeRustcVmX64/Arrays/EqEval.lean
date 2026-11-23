module

public import NativeRustcVmX64.Arrays.EqEval.Exec
public import NativeRustcVm.Arrays.Folds
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqEval.Names

/-!
# `eq_eval` on x86-64

**`eqEval_spec`**: rustc's `eq_eval`, placed anywhere in the program, meets `EqEvalPre`/
`EqEvalPost` given `EW::mul`'s contract. The prologue (`b0`) pushes R15, R14, R12, RBX, RAX and
takes the common length `n`; at `n = 0` it returns `1` (`b5`, `b6`); else (`b1`) the loop (`b2` in
three parts, `EW::mul`, `b3`) multiplies the accumulator (RAX, RDX) by `1 + left[i] + right[i]`
for `i < n`, R12 the byte offset `16 i` (`Inv`), and the epilogue (`b4`, `b6`) returns it.
-/

namespace NativeRustcVmX64.Arrays.EqEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.EqEval NativeVm.Model
  NativeRustcVmX64.Field
open NativeRustcVm (ewsOf ewOf)

public section

/-- The left slice at the entry. -/
abbrev lft (m : MachineData) : List EW := ewsOf m.dmem (reg m .rdi) (reg m .rsi).toNat
/-- The right slice at the entry. -/
abbrev rgt (m : MachineData) : List EW := ewsOf m.dmem (reg m .rdx) (reg m .rcx).toNat
/-- The common length. -/
abbrev cnt (m : MachineData) : Nat := min (reg m .rsi).toNat (reg m .rcx).toNat

/-- The product of the first `i` factors. -/
def acc (m : MachineData) (i : Nat) : EW :=
  (List.zipWith (fun x z ↦ 1 + x + z) ((lft m).take i) ((rgt m).take i)).foldl (· * ·) 1

theorem eqEval_eq_acc (m : MachineData) :
    eqEval (slice m (reg m .rdi) (reg m .rsi)) (slice m (reg m .rdx) (reg m .rcx)) =
      acc m (cnt m) := by
  unfold slice acc
  rw [NativeRustcVm.eqEval_eq, NativeRustcVm.zipWith_take_min]
  simp

theorem acc_succ (m : MachineData) {i : Nat} (h : i < cnt m) :
    acc m (i + 1) = acc m i *
      (1 + (lft m)[i]'(by simp; exact Nat.lt_of_lt_of_le h (Nat.min_le_left _ _)) +
        (rgt m)[i]'(by simp; exact Nat.lt_of_lt_of_le h (Nat.min_le_right _ _))) :=
  NativeRustcVm.zipFold_take_succ _ _ _ _ _ _ _

/-- The factor the loop forms from the limbs: `1 + l + r`. -/
theorem factor (l0 l1 r0 r1 : BitVec 64) :
    ewArg ((l0 ^^^ r0) ^^^ BitVec.ofNat 64 1) (r1 ^^^ l1) = 1 + ewArg l0 l1 + ewArg r0 r1 := by
  show (⟨_, _⟩ : EW) = ⟨(1 ^^^ _) ^^^ _, (0 ^^^ _) ^^^ _⟩
  congr 1
  · apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_xor]
    show _ = (1#64 ^^^ l0) ^^^ r0
    ac_rfl
  · apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_xor, UInt64.toBitVec_zero,
      BitVec.zero_xor]
    ac_rfl

/-- **The loop head** `NativeRustcVmX64.Vm.EqEval.label_3`, `i` factors multiplied. -/
structure Inv (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 48 eqEvalStack slots 0 0 st
  lt : i < cnt m0
  r14 : reg st .r14 = BitVec.ofNat 64 (16 * cnt m0)
  r12 : reg st .r12 = BitVec.ofNat 64 (16 * i)
  r15 : reg st .r15 = reg m0 .rdi
  rbx : reg st .rbx = reg m0 .rdx
  acc : ewArg (reg st .rax) (reg st .rdx) = acc m0 i

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEval.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEval.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : p1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEval.b2Offset) ∧
    p2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEval.b2Offset + p1.length) ∧ p3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEval.b2Offset + p1.length + p2.length) := by
  have h := b2_in_code.trans hp.1 (by simp [b2])
  rw [← List.take_append_drop 2 b2, ← List.take_append_drop 2 (b2.drop 2)] at h
  have h1 := h.append
  have h2 := h1.2.append
  exact ⟨h1.1, h2.1, by simpa [p1, p2, p3, List.drop_drop, NativeRustcVmX64.Vm.EqEval.b2_length] using h2.2⟩
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEval.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEval.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEval.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEval.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqEval.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.EqEval.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.EqEval.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqEval.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.EqEval.b5Offset) :=
  hp.label NativeRustcVmX64.Vm.EqEval.label_1_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqEval.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.EqEval.b2Offset) :=
  hp.label NativeRustcVmX64.Vm.EqEval.label_3_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqEval.label_4 = Host.addrOf (k + NativeRustcVmX64.Vm.EqEval.b6Offset) :=
  hp.label NativeRustcVmX64.Vm.EqEval.label_4_at

/-- `eq_eval`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ EqEvalPost m0 st.data

/-- **The epilogue** `b6`: from a body, the accumulator returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : EqEvalPre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqEval.b6Offset)) (hb : Body m0 48 eqEvalStack slots 0 0 st.data)
    (hacc : ewArg (reg st.data .rax) (reg st.data .rdx) = acc m0 (cnt m0)) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hS := hpre.1
  have h48 : 48 ≤ eqEvalStack := by decide
  refine exec_at (hb6 hp) run_b6 (hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h48)
    (by intro l h; cases h) hpc hb.mid_match fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hpc'', hrsp, hdm, hsaved⟩ := hb.done hS h48 hm' hpc'
    (after_eq run_b6 ▸ b6_restores).1 (after_eq run_b6 ▸ b6_restores).2
    (fun _ _ ↦ not_inRange_zero _)
  have h0 : reg st'.data .rax = reg st.data .rax := hm'.regs .rax _ rfl
  have h1 : reg st'.data .rdx = reg st.data .rdx := hm'.regs .rdx _ rfl
  refine ⟨hpc'', hrsp, ?_, fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  rw [eqEval_eq_acc, ← hacc]
  show ewArg (reg st'.data .rax) (reg st'.data .rdx) = _
  rw [h0, h1]

omit [Host] in
theorem sixteen_add (i : Nat) :
    BitVec.ofNat 64 16 + BitVec.ofNat 64 (16 * i) = BitVec.ofNat 64 (16 * (i + 1)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

/-- **A turn of the loop**: the accumulator multiplied by `1 + left[i] + right[i]`, back at the
head or out of the loop and returned. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : EqEvalPre m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqEval.b2Offset)) (hI : Inv m0 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqEval.b2Offset) ∧ Inv m0 (i + 1) st'.data)) st := by
  have hS := hpre.1
  have hL := SliceIn.of_ok hpre.2.1
  have hR := SliceIn.of_ok hpre.2.2
  have h48 : 48 ≤ eqEvalStack := by decide
  have hlt := hI.lt
  have hiL : i < (reg m0 .rsi).toNat := Nat.lt_of_lt_of_le hI.lt (Nat.min_le_left _ _)
  have hiR : i < (reg m0 .rcx).toNat := Nat.lt_of_lt_of_le hI.lt (Nat.min_le_right _ _)
  have hlen := lt_of_offStack hpre.2.1.1.2 hpre.2.1.2
  have hc1 : cnt m0 ≤ (reg m0 .rsi).toNat := Nat.min_le_left _ _
  -- `p1`: `left[i]`'s limb 0
  obtain ⟨hwf1, hm1, hel1⟩ := hI.body.elem (ret := 0) hS h48 hL hiL (x := .bin .add .W64 (.reg .r15)
    (.reg .r12)) (o := 0) (by rw [eval_add, eval_reg, eval_reg]; simp [hI.r15, hI.r12])
  refine exec_at (hb2 hp).1 run_p1 hwf1 (by intro l h; cases h) hpc hm1 fun st1 hm1' hpc1 ↦ ?_
  simp only [PcOk, show p1.length = 2 from rfl] at hpc1
  have hb1 := hI.body.of_block hm1 hm1' hwf1 rfl (after_eq run_p1 ▸ p1_keeps)
  have h8 : reg st1.data .r8 = (elemEnv m0 st.data 48 (reg m0 .rdi) i).load 1 0 8 :=
    hm1'.regs .r8 _ rfl
  have e1 : ∀ r ∈ [Reg64.rax, .rdx, .rbx, .r12, .r14, .r15], reg st1.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm1 hm1' rfl rfl
  -- `p2`: `right[i]`
  obtain ⟨hwf2, hm2, hel2⟩ := hb1.elem (ret := 0) hS h48 hR hiR (x := .bin .add .W64 (.reg .rbx)
    (.reg .r12)) (o := 0) (by
      rw [eval_add, eval_reg, eval_reg]
      simp [e1 .rbx (by simp), e1 .r12 (by simp), hI.rbx, hI.r12])
  refine exec_at (hb2 hp).2.1 run_p2 hwf2 (by intro l h; cases h) hpc1 hm2 fun st2 hm2' hpc2 ↦ ?_
  simp only [PcOk, show p2.length = 2 from rfl] at hpc2
  have hb2' := hb1.of_block hm2 hm2' hwf2 rfl (after_eq run_p2 ▸ p2_keeps)
  have h8' : reg st2.data .r8 = (Sym.bin .xor .W64 (.reg .r8) (.load 1 0 8)).eval
      (elemEnv m0 st1.data 48 (reg m0 .rdx) i) := hm2'.regs .r8 _ rfl
  have hcx : reg st2.data .rcx = (elemEnv m0 st1.data 48 (reg m0 .rdx) i).load 1 8 8 :=
    hm2'.regs .rcx _ rfl
  rw [eval_xor, eval_reg] at h8'
  have e2 : ∀ r ∈ [Reg64.rax, .rdx, .rbx, .r12, .r14, .r15], reg st2.data r = reg st.data r := by
    intro r hr
    rw [← e1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm2 hm2' rfl rfl
  -- `p3`: `left[i]`'s limb 1, the call
  obtain ⟨hwf3, hm3, hel3⟩ := hb2'.elem (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.EqEval.b3Offset)).toBitVec) hS
    h48 hL hiL (x := .bin .add .W64 (.reg .r15) (.reg .r12)) (o := 0) (by
      rw [eval_add, eval_reg, eval_reg]
      simp [e2 .r15 (by simp), e2 .r12 (by simp), hI.r15, hI.r12])
  refine exec_at (hb2 hp).2.2 run_p3 hwf3 (fun _ _ ↦ rfl) hpc2 hm3 fun st3 hm3' hpc3 ↦ ?_
  obtain ⟨hk3, hsp3, hw3⟩ := after_eq run_p3 ▸ p3_call
  have hdi : reg st3.data .rdi = reg st.data .rax :=
    (hm3'.regs .rdi (.reg .rax) rfl).trans (e2 .rax (by simp))
  have hsi : reg st3.data .rsi = reg st.data .rdx :=
    (hm3'.regs .rsi (.reg .rdx) rfl).trans (e2 .rdx (by simp))
  have hdx : reg st3.data .rdx = (Sym.bin .xor .W64 (.reg .r8) (.lit 1)).eval
      (elemEnv m0 st2.data 48 (reg m0 .rdi) i (Host.addrOf (k + NativeRustcVmX64.Vm.EqEval.b3Offset)).toBitVec) :=
    hm3'.regs .rdx _ rfl
  have hcx' : reg st3.data .rcx = (Sym.bin .xor .W64 (.reg .rcx) (.load 1 8 8)).eval
      (elemEnv m0 st2.data 48 (reg m0 .rdi) i (Host.addrOf (k + NativeRustcVmX64.Vm.EqEval.b3Offset)).toBitVec) :=
    hm3'.regs .rcx _ rfl
  rw [eval_xor, eval_reg, eval_lit] at hdx
  rw [eval_xor, eval_reg] at hcx'
  have hfac : ewArg (reg st3.data .rdx) (reg st3.data .rcx) =
      1 + (lft m0)[i]'(by simp; exact hiL) + (rgt m0)[i]'(by simp; exact hiR) := by
    rw [← hel2, ← hel1]
    have hl1 : (elemEnv m0 st.data 48 (reg m0 .rdi) i).load 1 8 8 =
        (elemEnv m0 st2.data 48 (reg m0 .rdi) i (Host.addrOf (k + NativeRustcVmX64.Vm.EqEval.b3Offset)).toBitVec).load
          1 8 8 := by
      have h := hel1.trans hel3.symm
      exact congrArg UInt64.toBitVec (congrArg EW.c1 h)
    rw [hl1, hdx, hcx']
    show ewArg ((reg st2.data .r8) ^^^ _) ((reg st2.data .rcx) ^^^ _) = _
    rw [h8', hcx, show (elemEnv m0 st1.data 48 (reg m0 .rdx) i).regs .r8 = reg st1.data .r8
      from rfl, h8]
    exact factor _ _ _ _
  refine Body.call_mul hmul hb2' hS (by decide) (by decide) slots_ok hwf3 hm3 hm3' hpc3 hk3 hsp3
    hw3 fun st4 hpc4 hb4' hprod hsv _ _ ↦ ?_
  rw [hdi, hsi, hI.acc, hfac] at hprod
  replace hprod : ewRet st4.data = acc m0 (i + 1) := by rw [acc_succ m0 hI.lt]; exact hprod
  have e4 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg st4.data r = reg st.data r := by
    intro r hr
    have hr' : r ∈ [Reg64.rax, .rdx, .rbx, .r12, .r14, .r15] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [← e2 r hr']
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (hsv _ rfl).trans (Match.reg_eq hm3 hm3' rfl rfl)
  -- `b3`: advance, compare
  refine exec_at (hb3 hp) run_b3 (Env.wf_nil _) (by intro l h; cases h) hpc4 (match_nil _)
    fun st5 hm5 hpc5 ↦ ?_
  have hb5' := hb4'.of_block (match_nil _) hm5 (Env.wf_nil _) rfl (after_eq run_b3 ▸ b3_keeps)
  have h4 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15],
      (Env.ofMachine st4.data []).regs r = reg st.data r := e4
  have hacc : ewArg (reg st5.data .rax) (reg st5.data .rdx) = acc m0 (i + 1) := by
    rw [← hprod]
    rw [show reg st5.data .rax = reg st4.data .rax from Match.reg_eq (match_nil _) hm5 rfl rfl,
      show reg st5.data .rdx = reg st4.data .rdx from Match.reg_eq (match_nil _) hm5 rfl rfl]
    rfl
  have hr12 : reg st5.data .r12 = BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [show reg st5.data .r12 = (Sym.bin .add .W64 (.lit 16) (.reg .r12)).eval
      (Env.ofMachine st4.data []) from hm5.regs .r12 _ rfl, eval_add, eval_lit, eval_reg,
      h4 .r12 (by simp), hI.r12]
    exact sixteen_add i
  have hr14 : reg st5.data .r14 = BitVec.ofNat 64 (16 * cnt m0) :=
    (hm5.regs .r14 (.reg .r14) rfl).trans ((h4 .r14 (by simp)).trans hI.r14)
  have hr15 : reg st5.data .r15 = reg m0 .rdi :=
    (hm5.regs .r15 (.reg .r15) rfl).trans ((h4 .r15 (by simp)).trans hI.r15)
  have hrbx : reg st5.data .rbx = reg m0 .rdx :=
    (hm5.regs .rbx (.reg .rbx) rfl).trans ((h4 .rbx (by simp)).trans hI.rbx)
  simp only [PcOk] at hpc5
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg, h4 .r14 (by simp),
    h4 .r12 (by simp), hI.r14, hI.r12, sixteen_add, ofNat_beq (by omega) (by omega)] at hpc5
  obtain ⟨hT, hF⟩ := pc_cond hpc5
  by_cases hlast : 16 * cnt m0 = 16 * (i + 1)
  · have hpc5' := hF (by simp [hlast])
    simp only [NativeRustcVmX64.Vm.EqEval.b3_length] at hpc5'
    refine exec_at (hb4 hp) run_b4 (Env.wf_nil _) (by intro l h; cases h) hpc5' (match_nil _)
      fun st6 hm6 hpc6 ↦ ?_
    have hb6' := hb5'.of_block (match_nil _) hm6 (Env.wf_nil _) rfl (after_eq run_b4 ▸ b4_keeps)
    simp only [PcOk] at hpc6
    refine Eventually.mono (finish hp hpre (hpc6.trans (lbl_4 hp)) hb6' ?_) fun _ h ↦ Or.inl h
    rw [show reg st6.data .rax = reg st5.data .rax from Match.reg_eq (match_nil _) hm6 rfl rfl,
      show reg st6.data .rdx = reg st5.data .rdx from Match.reg_eq (match_nil _) hm6 rfl rfl,
      hacc, show i + 1 = cnt m0 by omega]
  · exact .done _ (Or.inr ⟨(hT (by simp [hlast])).trans (lbl_3 hp),
      ⟨hb5', by omega, hr14, hr12, hr15, hrbx, hacc⟩⟩)

/-- **`eq_eval` meets its contract.** -/
theorem eqEval_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.EqEval.entryLabel) EqEvalPre EqEvalPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hS := hpre.1
  have h48 : 48 ≤ eqEvalStack := by decide
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h48)
    fun _ h ↦ h
  have hlen := lt_of_offStack hpre.2.1.1.2 hpre.2.1.2
  have hc1 : cnt m0 ≤ (reg m0 .rsi).toNat := Nat.min_le_left _ _
  have hm : Match (frameEnv m0 m0 48) entryS m0 := match_frame
  refine exec_then (hb0 hp) run_b0 hwf (by intro l h; cases h) hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.EqEval.b0_length] at hpc1
  rw [eval_test, eval_min, ofNat_beq (by omega) (by decide)] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hz : cnt m0 = 0
  · -- `n = 0`: return `1`.
    have hpc1 := hT (by simp only [Env.ofMachine_regs]; exact decide_eq_true hz)
    refine exec_at (hb5 hp) (exec_after run_b0 run_b5) hwf (by intro l h; cases h)
      (hpc1.trans (lbl_1 hp)) hm1 fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmX64.Vm.EqEval.b5_length] at hpc2
    obtain ⟨hw, hregs, hmem, hsp⟩ := after_eq run_b5 ▸ b5_entry
    have hb := Body.of_entry (oa := 0) (on := 0) hS h48 hm2 hsp hw hregs hmem
    refine finish hp hpre hpc2 hb ?_
    rw [show reg st2.data .rax = 1#64 from hm2.regs .rax _ rfl,
      show reg st2.data .rdx = 0#64 from hm2.regs .rdx _ rfl]
    unfold acc
    rw [hz]
    rfl
  · -- `n > 0`: the loop.
    have hpc1 := hF (by simp only [Env.ofMachine_regs]; exact fun h ↦ hz (of_decide_eq_true h))
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf (by intro l h; cases h) hpc1 hm1
      fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmX64.Vm.EqEval.b1_length] at hpc2
    obtain ⟨hw, hregs, hmem, hsp⟩ := after_eq run_b1 ▸ b1_entry
    have hI : Inv m0 0 st2.data := by
      have h14 := hm2.regs .r14 _ rfl
      rw [eval_shl_lit (hj := by decide), eval_min] at h14
      refine ⟨Body.of_entry hS h48 hm2 hsp hw hregs hmem, Nat.pos_of_ne_zero hz, ?_,
        hm2.regs .r12 _ rfl, hm2.regs .r15 _ rfl, hm2.regs .rbx _ rfl, ?_⟩
      · show st2.data.regs.get64 .r14 = _
        rw [h14]
        apply BitVec.eq_of_toNat_eq
        have hc2 : cnt m0 < 2 ^ 64 := by omega
        show ((BitVec.ofNat 64 (cnt m0)) <<< 4).toNat = (BitVec.ofNat 64 (16 * cnt m0)).toNat
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        omega
      · show ewArg (st2.data.regs.get64 .rax) (st2.data.regs.get64 .rdx) = _
        rw [hm2.regs .rax _ rfl, hm2.regs .rdx _ rfl]
        rfl
    refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqEval.b2Offset) ∧ ∃ i, cnt m0 - i = n ∧
      Inv m0 i st.data) (fun n st ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, hI⟩
    refine Eventually.mono (step hp hmul hpre hpc hI) fun st' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨cnt m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Arrays.EqEval
