module

public import NativeRustcVmX64.Arrays.ProdE.Exec
public import NativeRustcVm.Arrays.Folds
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.ProdE.Names

/-!
# `prod_e` on x86-64

**`prodE_spec`**: rustc's `prod_e(values)`, placed anywhere in the program, meets
`ProdEPre`/`ProdEPost` given `EW::mul`'s contract. The prologue (`b0`) pushes R15, R14, RBX and
starts the product at `1`; the bottom-tested loop (`b1`, `EW::mul`, `b2`) multiplies it by
`values[i]` for `i < len` (`Inv`: R15 the byte offset `16 i`, RBX `16 len`; `len ≥ 1`), and the
epilogue (`b3`) returns it.
-/

namespace NativeRustcVmX64.Arrays.ProdE

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ProdE NativeVm.Model
  NativeRustcVmX64.Field
open NativeRustcVm (ewsOf ewOf)

public section

/-- The values at the entry. -/
abbrev xs (m : MachineData) : List EW := ewsOf m.dmem (reg m .rdi) (reg m .rsi).toNat
/-- Their number. -/
abbrev len (m : MachineData) : Nat := (reg m .rsi).toNat

/-- The product of the first `i` values. -/
def acc (m : MachineData) (i : Nat) : EW := ((xs m).take i).foldl (· * ·) 1

theorem prodE_eq_acc (m : MachineData) :
    prodE (slice m (reg m .rdi) (reg m .rsi)) = acc m (len m) := by
  unfold slice acc
  rw [NativeRustcVm.prodE_eq, List.take_of_length_le (by simp)]

theorem lt_len {m : MachineData} {i : Nat} (h : i < len m) : i < (xs m).length := by
  simp only [xs, len, NativeRustcVm.length_ewsOf] at h ⊢; exact h

theorem acc_succ (m : MachineData) {i : Nat} (h : i < len m) :
    acc m (i + 1) = acc m i * (xs m)[i]'(lt_len h) :=
  NativeRustcVm.foldl_take_succ _ _ _ _

/-- **The loop head** `NativeRustcVmX64.Vm.ProdE.label_1`, `i` values multiplied. -/
structure Inv (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 32 prodEStack slots 0 0 st
  lt : i < len m0
  rbx : reg st .rbx = BitVec.ofNat 64 (16 * len m0)
  r15 : reg st .r15 = BitVec.ofNat 64 (16 * i)
  r14 : reg st .r14 = reg m0 .rdi
  acc : ewArg (reg st .rax) (reg st .rdx) = acc m0 i

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.ProdE.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.ProdE.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.ProdE.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.ProdE.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.ProdE.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.ProdE.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.ProdE.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.ProdE.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.ProdE.b1Offset) :=
  hp.label NativeRustcVmX64.Vm.ProdE.label_1_at

/-- `prod_e`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ ProdEPost m0 st.data

/-- **The epilogue** `b3`: from a body, the product returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : ProdEPre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ProdE.b3Offset)) (hb : Body m0 32 prodEStack slots 0 0 st.data)
    (hacc : ewArg (reg st.data .rax) (reg st.data .rdx) = acc m0 (len m0)) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hS := hpre.1
  have h32 : 32 ≤ prodEStack := by decide
  refine exec_at (hb3 hp) run_b3 (hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h32)
    (by intro l h; cases h) hpc hb.mid_match fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hpc'', hrsp, hdm, hsaved⟩ := hb.done hS h32 hm' hpc'
    (after_eq run_b3 ▸ b3_restores).1 (after_eq run_b3 ▸ b3_restores).2
    (fun _ _ ↦ not_inRange_zero _)
  have h0 : reg st'.data .rax = reg st.data .rax := hm'.regs .rax _ rfl
  have h1 : reg st'.data .rdx = reg st.data .rdx := hm'.regs .rdx _ rfl
  refine ⟨hpc'', hrsp, ?_, fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  rw [prodE_eq_acc, ← hacc]
  show ewArg (reg st'.data .rax) (reg st'.data .rdx) = _
  rw [h0, h1]

omit [Host] in
theorem sixteen_add (i : Nat) :
    BitVec.ofNat 64 16 + BitVec.ofNat 64 (16 * i) = BitVec.ofNat 64 (16 * (i + 1)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

/-- **A turn of the loop**: the product multiplied by `values[i]`, back at the head or out of the
loop and returned. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : ProdEPre m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ProdE.b1Offset)) (hI : Inv m0 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ProdE.b1Offset) ∧ Inv m0 (i + 1) st'.data)) st := by
  have hS := hpre.1
  have hV := SliceIn.of_ok hpre.2.2.2
  have h32 : 32 ≤ prodEStack := by decide
  have hlt := hI.lt
  have hlen := lt_of_offStack hpre.2.2.2.1.2 hpre.2.2.2.2
  have hL : len m0 = (reg m0 .rsi).toNat := rfl
  -- `b1`: `values[i]`, the call
  obtain ⟨hwf1, hm1, hel1⟩ := hI.body.elem (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.ProdE.b2Offset)).toBitVec) hS h32
    hV hlt (x := .bin .add .W64 (.reg .r14) (.reg .r15)) (o := 0)
    (by rw [eval_add, eval_reg, eval_reg]; simp [hI.r14, hI.r15])
  refine exec_at (hb1 hp) run_b1 hwf1 (fun _ _ ↦ rfl) hpc hm1 fun st1 hm1' hpc1 ↦ ?_
  obtain ⟨hk1, hsp1, hw1⟩ := after_eq run_b1 ▸ b1_call
  have hdi : reg st1.data .rdi = reg st.data .rax := hm1'.regs .rdi (.reg .rax) rfl
  have hsi : reg st1.data .rsi = reg st.data .rdx := hm1'.regs .rsi (.reg .rdx) rfl
  have hx : ewArg (reg st1.data .rdx) (reg st1.data .rcx) = (xs m0)[i]'(lt_len hlt) := by
    rw [← hel1]
    show ewArg (st1.data.regs.get64 .rdx) (st1.data.regs.get64 .rcx) = _
    rw [hm1'.regs .rdx _ rfl, hm1'.regs .rcx _ rfl]
    rfl
  refine Body.call_mul hmul hI.body hS (by decide) (by decide) slots_ok hwf1 hm1 hm1' hpc1 hk1
    hsp1 hw1 fun st2 hpc2 hb2' hprod hsv _ _ ↦ ?_
  rw [hdi, hsi, hI.acc, hx] at hprod
  replace hprod : ewRet st2.data = acc m0 (i + 1) := by rw [acc_succ m0 hI.lt]; exact hprod
  have e2 : ∀ r ∈ [Reg64.rbx, .r14, .r15], reg st2.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hsv _ rfl).trans (Match.reg_eq hm1 hm1' rfl rfl)
  -- `b2`: advance, compare
  refine exec_at (hb2 hp) run_b2 (Env.wf_nil _) (by intro l h; cases h) hpc2 (match_nil _)
    fun st3 hm3 hpc3 ↦ ?_
  have hb3' := hb2'.of_block (match_nil _) hm3 (Env.wf_nil _) rfl (after_eq run_b2 ▸ b2_keeps)
  have h2 : ∀ r ∈ [Reg64.rbx, .r14, .r15],
      (Env.ofMachine st2.data []).regs r = reg st.data r := e2
  have hacc : ewArg (reg st3.data .rax) (reg st3.data .rdx) = acc m0 (i + 1) := by
    rw [← hprod]
    rw [show reg st3.data .rax = reg st2.data .rax from Match.reg_eq (match_nil _) hm3 rfl rfl,
      show reg st3.data .rdx = reg st2.data .rdx from Match.reg_eq (match_nil _) hm3 rfl rfl]
    rfl
  have hr15 : reg st3.data .r15 = BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [show reg st3.data .r15 = (Sym.bin .add .W64 (.lit 16) (.reg .r15)).eval
      (Env.ofMachine st2.data []) from hm3.regs .r15 _ rfl, eval_add, eval_lit, eval_reg,
      h2 .r15 (by simp), hI.r15]
    exact sixteen_add i
  have hrbx : reg st3.data .rbx = BitVec.ofNat 64 (16 * len m0) :=
    (hm3.regs .rbx (.reg .rbx) rfl).trans ((h2 .rbx (by simp)).trans hI.rbx)
  have hr14 : reg st3.data .r14 = reg m0 .rdi :=
    (hm3.regs .r14 (.reg .r14) rfl).trans ((h2 .r14 (by simp)).trans hI.r14)
  simp only [PcOk] at hpc3
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg, h2 .rbx (by simp),
    h2 .r15 (by simp), hI.rbx, hI.r15, sixteen_add, ofNat_beq (by omega) (by omega)] at hpc3
  obtain ⟨hT, hF⟩ := pc_cond hpc3
  by_cases hlast : 16 * len m0 = 16 * (i + 1)
  · have hpc3' := hF (by simp [hlast])
    simp only [NativeRustcVmX64.Vm.ProdE.b2_length] at hpc3'
    refine Eventually.mono (finish hp hpre hpc3' hb3' ?_) fun _ h ↦ Or.inl h
    rw [hacc, show i + 1 = len m0 by omega]
  · exact .done _ (Or.inr ⟨(hT (by simp [hlast])).trans (lbl_1 hp),
      ⟨hb3', by omega, hrbx, hr15, hr14, hacc⟩⟩)

/-- **`prod_e` meets its contract.** -/
theorem prodE_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.ProdE.entryLabel) ProdEPre ProdEPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hS := hpre.1
  have h32 : 32 ≤ prodEStack := by decide
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h32)
    fun _ h ↦ h
  have hlen := lt_of_offStack hpre.2.2.2.1.2 hpre.2.2.2.2
  have hL : len m0 = (reg m0 .rsi).toNat := rfl
  have h2 := hpre.2.1
  have hm : Match (frameEnv m0 m0 32) entryS m0 := match_frame
  refine exec_then (hb0 hp) run_b0 hwf (by intro l h; cases h) hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.ProdE.b0_length] at hpc1
  obtain ⟨hw, hregs, hmem, hsp⟩ := after_eq run_b0 ▸ b0_entry
  have hI : Inv m0 0 st1.data := by
    have hbx := hm1.regs .rbx _ rfl
    rw [eval_shl_lit (hj := by decide)] at hbx
    refine ⟨Body.of_entry hS h32 hm1 hsp hw hregs hmem, by omega, ?_, hm1.regs .r15 _ rfl,
      hm1.regs .r14 _ rfl, ?_⟩
    · show st1.data.regs.get64 .rbx = _
      rw [hbx]
      apply BitVec.eq_of_toNat_eq
      show ((reg m0 .rsi) <<< 4).toNat = (BitVec.ofNat 64 (16 * len m0)).toNat
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    · show ewArg (st1.data.regs.get64 .rax) (st1.data.regs.get64 .rdx) = _
      rw [hm1.regs .rax _ rfl, hm1.regs .rdx _ rfl]
      rfl
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ProdE.b1Offset) ∧ ∃ i, len m0 - i = n ∧
    Inv m0 i st.data) (fun n st ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc1.trans rfl, 0, rfl, hI⟩
  refine Eventually.mono (step hp hmul hpre hpc hI) fun st' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨len m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Arrays.ProdE
