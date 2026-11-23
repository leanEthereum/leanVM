module

public import NativeRustcVmX64.Arrays.PolyEval.Exec
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names

/-!
# `poly_eval` on x86-64

**`polyEval_spec`**: rustc's `poly_eval`, placed anywhere in the program, meets `PolyEvalPre`/
`PolyEvalPost` given `EW::mul`'s contract. The prologue (`b0`) pushes RBP, R15-R12, RBX, RAX and
starts the accumulator (RAX, RDX) at `0`, R15 at `16 |coefficients|`; the bottom-tested loop (`b1`,
`EW::mul`, `b2`) folds the coefficients from the last by Horner's rule, R15 the byte offset past
the next one (`Inv`), and the epilogue (`b3`) returns the accumulator.
-/

namespace NativeRustcVmX64.Arrays.PolyEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PolyEval NativeVm.Model
  NativeRustcVmX64.Field
open NativeRustcVm (ewsOf)

public section

/-- The coefficients at the entry. -/
abbrev coefs (m : MachineData) : List EW := ewsOf m.dmem (reg m .rdi) (reg m .rsi).toNat
/-- Their number. -/
abbrev len (m : MachineData) : Nat := (reg m .rsi).toNat
/-- The point. -/
abbrev pt (m : MachineData) : EW := ewArg (reg m .rdx) (reg m .rcx)

/-- Horner's rule on the last `t` coefficients. -/
def acc (m : MachineData) (t : Nat) : EW :=
  ((coefs m).drop (len m - t)).foldr (fun c acc ↦ acc * pt m + c) 0

theorem polyEval_eq_acc (m : MachineData) :
    polyEval (slice m (reg m .rdi) (reg m .rsi)) (ewArg (reg m .rdx) (reg m .rcx)) =
      acc m (len m) := by
  unfold slice acc polyEval
  rw [← Array.foldr_toList, Nat.sub_self, List.drop_zero]

theorem lt_len {m : MachineData} {t : Nat} (h : t < len m) :
    len m - 1 - t < (coefs m).length := by
  simp only [coefs, len, NativeRustcVm.length_ewsOf] at h ⊢; omega

theorem acc_succ (m : MachineData) {t : Nat} (h : t < len m) :
    acc m (t + 1) = acc m t * pt m + (coefs m)[len m - 1 - t]'(lt_len h) := by
  unfold acc
  rw [show len m - (t + 1) = len m - 1 - t by omega,
    List.drop_eq_getElem_cons (lt_len h), List.foldr_cons,
    show len m - 1 - t + 1 = len m - t by omega]

/-- **The loop head** `NativeRustcVmX64.Vm.PolyEval.label_1`, `t` coefficients folded. -/
structure Inv (m0 : MachineData) (t : Nat) (st : MachineData) : Prop where
  body : Body m0 64 polyEvalStack slots 0 0 st
  lt : t < len m0
  r15 : reg st .r15 = BitVec.ofNat 64 (16 * (len m0 - t))
  r12 : reg st .r12 = reg m0 .rdi
  r14 : reg st .r14 = reg m0 .rdx
  rbx : reg st .rbx = reg m0 .rcx
  acc : ewArg (reg st .rax) (reg st .rdx) = acc m0 t

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PolyEval.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PolyEval.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PolyEval.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PolyEval.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.PolyEval.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.PolyEval.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.PolyEval.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.PolyEval.b1Offset) :=
  hp.label NativeRustcVmX64.Vm.PolyEval.label_1_at

/-- `poly_eval`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ PolyEvalPost m0 st.data

/-- **The epilogue** `b3`: the accumulator returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : PolyEvalPre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PolyEval.b3Offset)) (hb : Body m0 64 polyEvalStack slots 0 0 st.data)
    (hacc : ewArg (reg st.data .rax) (reg st.data .rdx) = acc m0 (len m0)) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hS := hpre.1
  have h64 : 64 ≤ polyEvalStack := by decide
  refine exec_at (hb3 hp) run_b3 (hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h64)
    (by intro l h; cases h) hpc hb.mid_match fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hpc'', hrsp, hdm, hsaved⟩ := hb.done hS h64 hm' hpc'
    (after_eq run_b3 ▸ b3_restores).1 (after_eq run_b3 ▸ b3_restores).2
    (fun _ _ ↦ not_inRange_zero _)
  have h0 : reg st'.data .rax = reg st.data .rax := hm'.regs .rax _ rfl
  have h1 : reg st'.data .rdx = reg st.data .rdx := hm'.regs .rdx _ rfl
  refine ⟨hpc'', hrsp, ?_, fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  rw [polyEval_eq_acc, ← hacc]
  show ewArg (reg st'.data .rax) (reg st'.data .rdx) = _
  rw [h0, h1]

omit [Host] in
theorem sub16 {n : Nat} (h1 : 1 ≤ n) (h : 16 * n < 2 ^ 64) :
    BitVec.ofNat 64 18446744073709551600 + BitVec.ofNat 64 (16 * n) =
      BitVec.ofNat 64 (16 * (n - 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- **A turn of the loop**: the accumulator times the point plus coefficient `len - 1 - t`, back
at the head or out of the loop and returned. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : PolyEvalPre m0) {t : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PolyEval.b1Offset)) (hI : Inv m0 t st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PolyEval.b1Offset) ∧ Inv m0 (t + 1) st'.data)) st := by
  have hS := hpre.1
  have hC := SliceIn.of_ok hpre.2.2
  have h64 : 64 ≤ polyEvalStack := by decide
  have hlt := hI.lt
  have hl : len m0 = (reg m0 .rsi).toNat := rfl
  have hlen := lt_of_offStack hpre.2.2.1.2 hpre.2.2.2
  have hj : len m0 - 1 - t < (reg m0 .rsi).toNat := by omega
  -- `b1`: the coefficient, the call
  obtain ⟨hwf1, hm1, hel⟩ := hI.body.elem (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PolyEval.b2Offset)).toBitVec) hS h64
    hC hj (x := .bin .add .W64 (.reg .r12) (.reg .r15)) (o := 16) (by
      rw [eval_add, eval_reg, eval_reg]
      show reg st.data .r12 + reg st.data .r15 = _
      rw [hI.r12, hI.r15, addr_add, show 16 * (len m0 - 1 - t) + 16 = 16 * (len m0 - t) by omega])
  refine exec_at (hb1 hp) run_b1 hwf1 (fun _ _ ↦ rfl) hpc hm1 fun st1 hm1' hpc1 ↦ ?_
  obtain ⟨hk1, hsp1, hw1⟩ := after_eq run_b1 ▸ b1_call
  have hc : ewArg (reg st1.data .r13) (reg st1.data .rbp) =
      (coefs m0)[len m0 - 1 - t]'(lt_len hlt) := by
    rw [← hel]
    rw [show reg st1.data .r13 = _ from hm1'.regs .r13 (.load 1 0 8) rfl,
      show reg st1.data .rbp = _ from hm1'.regs .rbp (.load 1 8 8) rfl]
    rfl
  have hargs : EW.mul (ewArg (reg st1.data .rdi) (reg st1.data .rsi))
      (ewArg (reg st1.data .rdx) (reg st1.data .rcx)) = acc m0 t * pt m0 := by
    rw [show reg st1.data .rdi = reg st.data .rax from hm1'.regs .rdi (.reg .rax) rfl,
      show reg st1.data .rsi = reg st.data .rdx from hm1'.regs .rsi (.reg .rdx) rfl,
      show reg st1.data .rdx = reg m0 .rdx from (hm1'.regs .rdx (.reg .r14) rfl).trans hI.r14,
      show reg st1.data .rcx = reg m0 .rcx from (hm1'.regs .rcx (.reg .rbx) rfl).trans hI.rbx,
      hI.acc]
    rfl
  refine Body.call_mul hmul hI.body hS (by decide) (by decide) slots_ok hwf1 hm1 hm1' hpc1 hk1
    hsp1 hw1 fun st2 hpc2 hb2' hprod hsv _ _ ↦ ?_
  rw [hargs] at hprod
  have e2 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg st2.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (hsv _ rfl).trans (Match.reg_eq hm1 hm1' rfl rfl)
  -- `b2`: add the coefficient, step down, test
  refine exec_at (hb2 hp) run_b2 (Env.wf_nil _) (by intro l h; cases h) hpc2 (match_nil _)
    fun st3 hm3 hpc3 ↦ ?_
  have hb3' := hb2'.of_block (match_nil _) hm3 (Env.wf_nil _) rfl (after_eq run_b2 ▸ b2_keeps)
  have h2 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15],
      (Env.ofMachine st2.data []).regs r = reg st.data r := e2
  have hacc : ewArg (reg st3.data .rax) (reg st3.data .rdx) = acc m0 (t + 1) := by
    rw [acc_succ m0 hlt, ← hprod, ← hc,
      show reg st3.data .rax = (Sym.bin .xor .W64 (.reg .rax) (.reg .r13)).eval
        (Env.ofMachine st2.data []) from hm3.regs .rax _ rfl,
      show reg st3.data .rdx = (Sym.bin .xor .W64 (.reg .rdx) (.reg .rbp)).eval
        (Env.ofMachine st2.data []) from hm3.regs .rdx _ rfl,
      eval_xor, eval_xor, eval_reg, eval_reg, eval_reg, eval_reg]
    show ewArg (reg st2.data .rax ^^^ reg st2.data .r13) (reg st2.data .rdx ^^^ reg st2.data .rbp) = _
    rw [hsv .r13 rfl, hsv .rbp rfl]
    rfl
  have hr15 : reg st3.data .r15 = BitVec.ofNat 64 (16 * (len m0 - (t + 1))) := by
    rw [show reg st3.data .r15 = (Sym.bin .add .W64 (.lit 18446744073709551600) (.reg .r15)).eval
      (Env.ofMachine st2.data []) from hm3.regs .r15 _ rfl, eval_add, eval_lit, eval_reg,
      h2 .r15 (by simp), hI.r15, sub16 (by omega) (by omega)]
    congr 2
  have hr12 : reg st3.data .r12 = reg m0 .rdi :=
    (hm3.regs .r12 (.reg .r12) rfl).trans ((h2 .r12 (by simp)).trans hI.r12)
  have hr14 : reg st3.data .r14 = reg m0 .rdx :=
    (hm3.regs .r14 (.reg .r14) rfl).trans ((h2 .r14 (by simp)).trans hI.r14)
  have hrbx : reg st3.data .rbx = reg m0 .rcx :=
    (hm3.regs .rbx (.reg .rbx) rfl).trans ((h2 .rbx (by simp)).trans hI.rbx)
  simp only [PcOk] at hpc3
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_lit, eval_reg, h2 .r15 (by simp), hI.r15,
    sub16 (by omega) (by omega), ofNat_beq (by omega) (by decide)] at hpc3
  obtain ⟨hT, hF⟩ := pc_cond hpc3
  by_cases hlast : 16 * (len m0 - t - 1) = 0
  · have hpc3' := hF (by simp [hlast])
    simp only [NativeRustcVmX64.Vm.PolyEval.b2_length] at hpc3'
    refine Eventually.mono (finish hp hpre hpc3' hb3' ?_) fun _ h ↦ Or.inl h
    rw [hacc, show t + 1 = len m0 by omega]
  · exact .done _ (Or.inr ⟨(hT (by simp [hlast])).trans (lbl_1 hp),
      ⟨hb3', by omega, hr15, hr12, hr14, hrbx, hacc⟩⟩)

/-- **`poly_eval` meets its contract.** -/
theorem polyEval_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hS := hpre.1
  have h64 : 64 ≤ polyEvalStack := by decide
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h64)
    fun _ h ↦ h
  have hl : len m0 = (reg m0 .rsi).toNat := rfl
  have hlen := lt_of_offStack hpre.2.2.1.2 hpre.2.2.2
  have h1 := hpre.2.1
  refine exec_then (hb0 hp) run_b0 hwf (by intro l h; cases h) match_frame fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.PolyEval.b0_length] at hpc1
  obtain ⟨hw, hregs, hmem, hsp⟩ := after_eq run_b0 ▸ b0_entry
  have hI : Inv m0 0 st1.data := by
    have h15 := hm1.regs .r15 _ rfl
    rw [eval_shl_lit (hj := by decide), eval_reg] at h15
    refine ⟨Body.of_entry hS h64 hm1 hsp hw hregs hmem, by omega, ?_, hm1.regs .r12 _ rfl,
      hm1.regs .r14 _ rfl, hm1.regs .rbx _ rfl, ?_⟩
    · show st1.data.regs.get64 .r15 = _
      rw [h15]
      apply BitVec.eq_of_toNat_eq
      show (m0.regs.get64 .rsi <<< 4).toNat = (BitVec.ofNat 64 (16 * (len m0 - 0))).toNat
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      show (len m0) * 2 ^ 4 % 2 ^ 64 = _
      omega
    · show ewArg (st1.data.regs.get64 .rax) (st1.data.regs.get64 .rdx) = _
      rw [hm1.regs .rax _ rfl, hm1.regs .rdx _ rfl]
      unfold acc
      rw [Nat.sub_zero, List.drop_of_length_le (by simp)]
      rfl
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PolyEval.b1Offset) ∧ ∃ t, len m0 - t = n ∧
    Inv m0 t st.data) (fun n st ⟨hpc, t, hn, hI⟩ ↦ ?_) ⟨hpc1, 0, rfl, hI⟩
  refine Eventually.mono (step hp hmul hpre hpc hI) fun st' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨len m0 - (t + 1), by have := hI'.lt; omega, hpc', t + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Arrays.PolyEval
