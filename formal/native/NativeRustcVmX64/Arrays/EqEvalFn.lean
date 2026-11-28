module

public import NativeRustcVmX64.Arrays.EqEvalFn.Exec
public import NativeRustcVm.Arrays.Folds
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names

/-!
# `eq_eval_fn` with `eq_above`'s closure on x86-64

**`eqEvalFn_spec`**: rustc's `eq_eval_fn(n, |k| bit_e(selector, k), right)`, placed anywhere in
the program, meets `EqEvalFnOfEqAbovePre`/`EqEvalFnOfEqAbovePost` given `EW::mul`'s contract: the
value is `eqEval (selectorPoint selector n) right`. The prologue (`b0`) pushes R15, R14, R12, RBX,
RAX and takes `min n |right|`; at `0` it returns `1` (`b5`, `b6`); else (`b1`) the loop (`b2` in
three parts, `EW::mul`, `b3`) multiplies the accumulator (RAX, RDX) by
`1 + bit_e(selector, i) + right[i]` (`Inv`: RSI is `i`, RBX `right[i]`'s address plus 8). The
bit is the carry of raw `bt %rsi, %r14` (`p2`), read by `setb`. The epilogue
(`b4`, `b6`) returns the product.
-/

namespace NativeRustcVmX64.Arrays.EqEvalFn

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.EqEvalFnOfEqAbove NativeVm.Model
  NativeRustcVmX64.Field
open NativeRustcVm (ewsOf ewOf)

public section

/-- The left side: the selector's bits. -/
abbrev lft (m : MachineData) : List EW := (selectorPoint (reg m .rsi).toNat (reg m .rdi).toNat).toList
/-- The right slice at the entry. -/
abbrev rgt (m : MachineData) : List EW := ewsOf m.dmem (reg m .rdx) (reg m .rcx).toNat
/-- The common length. -/
abbrev cnt (m : MachineData) : Nat := min (reg m .rdi).toNat (reg m .rcx).toNat

theorem length_lft (m : MachineData) : (lft m).length = (reg m .rdi).toNat := by
  simp [lft, selectorPoint]

theorem lt_l {m : MachineData} {i : Nat} (h : i < cnt m) : i < (lft m).length := by
  rw [length_lft]; exact Nat.lt_of_lt_of_le h (Nat.min_le_left _ _)

theorem lt_r {m : MachineData} {i : Nat} (h : i < cnt m) : i < (rgt m).length := by
  simp only [rgt, NativeRustcVm.length_ewsOf]; exact Nat.lt_of_lt_of_le h (Nat.min_le_right _ _)

theorem getElem_lft (m : MachineData) {i : Nat} (h : i < (lft m).length) :
    (lft m)[i] = EW.ofNat (((reg m .rsi).toNat >>> i) % 2) := by
  simp [lft, selectorPoint]

/-- The product of the first `i` factors. -/
def acc (m : MachineData) (i : Nat) : EW :=
  (List.zipWith (fun x z ↦ 1 + x + z) ((lft m).take i) ((rgt m).take i)).foldl (· * ·) 1

theorem eqEval_eq_acc (m : MachineData) :
    eqEval (selectorPoint (reg m .rsi).toNat (reg m .rdi).toNat) (slice m (reg m .rdx) (reg m .rcx)) =
      acc m (cnt m) := by
  unfold slice acc
  rw [← @Array.toArray_toList _ (selectorPoint _ _), NativeRustcVm.eqEval_eq,
    NativeRustcVm.zipWith_take_min, length_lft]
  simp

theorem acc_succ (m : MachineData) {i : Nat} (h : i < cnt m) :
    acc m (i + 1) = acc m i * (1 + (lft m)[i]'(lt_l h) + (rgt m)[i]'(lt_r h)) :=
  NativeRustcVm.zipFold_take_succ _ _ _ _ _ _ _

/-- The factor the loop forms from the bit `b` and `right[i]`'s limbs: `1 + b + r`. -/
theorem factor (b l0 l1 : BitVec 64) :
    ewArg ((b ^^^ l0) ^^^ BitVec.ofNat 64 1) l1 = 1 + ewArg b 0#64 + ewArg l0 l1 := by
  show (⟨_, _⟩ : EW) = ⟨(1 ^^^ _) ^^^ _, (0 ^^^ _) ^^^ _⟩
  congr 1
  · apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_xor]
    show _ = (1#64 ^^^ b) ^^^ l0
    ac_rfl
  · apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_xor, UInt64.toBitVec_zero, BitVec.zero_xor]
    show l1 = 0#64 ^^^ l1
    rw [BitVec.zero_xor]

/-- **The loop head** `NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.label_3`, `i` factors multiplied. -/
structure Inv (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 48 eqEvalFnStack slots 0 0 st
  lt : i < cnt m0
  r15 : reg st .r15 = BitVec.ofNat 64 (cnt m0)
  rsi : reg st .rsi = BitVec.ofNat 64 i
  r14 : reg st .r14 = reg m0 .rsi
  rbx : reg st .rbx = reg m0 .rdx + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8
  acc : ewArg (reg st .rax) (reg st .rdx) = acc m0 i

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : p1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b2Offset) ∧
    p2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b2Offset + p1.length) ∧ p3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b2Offset + p1.length + p2.length) := by
  have h := b2_in_code.trans hp.1 (by simp [b2])
  rw [← List.take_append_drop 4 b2, ← List.take_append_drop 1 (b2.drop 4)] at h
  have h1 := h.append
  have h2 := h1.2.append
  exact ⟨h1.1, h2.1, by simpa [p1, p2, p3, List.drop_drop, NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b2_length] using h2.2⟩
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])

theorem lbl_entry (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b5Offset) :=
  hp.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.label_1_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b2Offset) :=
  hp.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.label_3_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.label_4 = Host.addrOf (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b6Offset) :=
  hp.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.label_4_at

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ EqEvalFnOfEqAbovePost m0 st.data

/-- **The epilogue** `b6`: from a body, the accumulator returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : EqEvalFnOfEqAbovePre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b6Offset))
    (hb : Body m0 48 eqEvalFnStack slots 0 0 st.data)
    (hacc : ewArg (reg st.data .rax) (reg st.data .rdx) = acc m0 (cnt m0)) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hS := hpre.1
  have h48 : 48 ≤ eqEvalFnStack := by decide
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
theorem sixteen_add (a : BitVec 64) (i : Nat) :
    BitVec.ofNat 64 16 + (a + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8) =
      a + BitVec.ofNat 64 (16 * (i + 1)) + BitVec.ofNat 64 8 := by
  rw [← BitVec.add_assoc, add16]

/-- **A turn of the loop**: the accumulator multiplied by `1 + bit_e(selector, i) + right[i]`, back
at the head or out of the loop and returned. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : EqEvalFnOfEqAbovePre m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b2Offset)) (hI : Inv m0 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b2Offset) ∧ Inv m0 (i + 1) st'.data)) st := by
  have hS := hpre.1
  have hR := SliceIn.of_ok hpre.2.2
  have h48 : 48 ≤ eqEvalFnStack := by decide
  have hlt := hI.lt
  have hc64 : cnt m0 ≤ 64 := hpre.2.1
  have hiR : i < (reg m0 .rcx).toNat := Nat.lt_of_lt_of_le hI.lt (Nat.min_le_right _ _)
  have hi64 : i < 64 := by omega
  -- `p1`: `right[i]`'s limb 1, `i + 1`
  obtain ⟨hwf1, hm1, hel1⟩ := hI.body.elem (ret := 0) hS h48 hR hiR (x := .reg .rbx) (o := 8)
    (by rw [eval_reg, Env.ofMachine_regs]; exact hI.rbx)
  refine exec_at (hb2 hp).1 run_p1 hwf1 (by intro l h; cases h) hpc hm1 fun st1 hm1' hpc1 ↦ ?_
  simp only [PcOk, show p1.length = 4 from rfl] at hpc1
  have hb1 := hI.body.of_block hm1 hm1' hwf1 rfl (after_eq run_p1 ▸ p1_keeps)
  have h8 : reg st1.data .r8 = BitVec.ofNat 64 0 := hm1'.regs .r8 _ rfl
  have hcx1 : reg st1.data .rcx = (elemEnv m0 st.data 48 (reg m0 .rdx) i).load 1 8 8 :=
    hm1'.regs .rcx _ rfl
  have h12 : reg st1.data .r12 = BitVec.ofNat 64 (i + 1) := by
    rw [show reg st1.data .r12 = (Sym.bin .add .W64 (.reg .rsi) (.lit 1)).eval
      (elemEnv m0 st.data 48 (reg m0 .rdx) i) from hm1'.regs .r12 _ rfl, eval_add, eval_reg,
      eval_lit, Env.ofMachine_regs]
    show reg st.data .rsi + _ = _
    rw [hI.rsi, BitVec.ofNat_add]
  have e1 : ∀ r ∈ [Reg64.rax, .rdx, .rbx, .rsi, .r14, .r15], reg st1.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm1 hm1' rfl rfl
  -- `p2`: raw `bt`, its carry bit `i` of the selector
  refine exec_at (hb2 hp).2.1 run_p2 (Env.wf_nil _) (by intro l h; cases h)
    hpc1 (match_nil _) fun st2 hm2' hpc2 ↦ ?_
  simp only [PcOk, show p2.length = 1 from rfl] at hpc2
  obtain ⟨hk2, hr2, hcf2⟩ := after_eq run_p2 ▸ p2_keeps
  have hb2' := hb1.of_block (match_nil _) hm2' (Env.wf_nil _) rfl hk2
  have e2 : ∀ r ∈ [Reg64.rax, .rcx, .rdx, .rbx, .rsi, .r8, .r12, .r14, .r15],
      reg st2.data r = reg st1.data r := fun r hr ↦ hm2'.regs r _ (hr2 r hr)
  have hcf : st2.data.status.cf = decide (((reg m0 .rsi).toNat >>> i) % 2 = 1) := by
    rw [hm2'.flags.1 _ hcf2]
    show CmpOp.apply .bit .W64 (reg st1.data .r14) (reg st1.data .rsi) = _
    have hsi : reg st1.data .rsi = BitVec.ofNat 64 i := (e1 .rsi (by simp)).trans hI.rsi
    have hit : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [bt_cf _ _ (by rw [hsi, hit]; exact hi64), e1 .r14 (by simp), hI.r14, hsi, hit]
  -- `p3`: the bit, `right[i]`'s limb 0, the call
  obtain ⟨hwf3, hm3, hel3⟩ := hb2'.elem (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b3Offset)).toBitVec) hS
    h48 hR hiR (x := .reg .rbx) (o := 8) (by
      rw [eval_reg, Env.ofMachine_regs]
      show reg st2.data .rbx = _
      rw [e2 .rbx (by simp), e1 .rbx (by simp), hI.rbx])
  refine exec_at (hb2 hp).2.2 run_p3 hwf3 (fun _ _ ↦ rfl) hpc2 hm3 fun st3 hm3' hpc3 ↦ ?_
  obtain ⟨hk3, hsp3, hw3⟩ := after_eq run_p3 ▸ p3_call
  have hdi : reg st3.data .rdi = reg st.data .rax :=
    (hm3'.regs .rdi (.reg .rax) rfl).trans ((e2 .rax (by simp)).trans (e1 .rax (by simp)))
  have hsi : reg st3.data .rsi = reg st.data .rdx :=
    (hm3'.regs .rsi (.reg .rdx) rfl).trans ((e2 .rdx (by simp)).trans (e1 .rdx (by simp)))
  have hdx : reg st3.data .rdx = (Sym.bin .xor .W64 (.bin .xor .W64 (.bin .merge .W8 (.reg .r8)
      (.ite .flagCF (.lit 1) (.lit 0))) (.load 1 0 8)) (.lit 1)).eval
      (elemEnv m0 st2.data 48 (reg m0 .rdx) i (Host.addrOf (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b3Offset)).toBitVec) :=
    hm3'.regs .rdx _ rfl
  have hcx3 : reg st3.data .rcx = reg st2.data .rcx := hm3'.regs .rcx (.reg .rcx) rfl
  have hfac : ewArg (reg st3.data .rdx) (reg st3.data .rcx) =
      1 + (lft m0)[i]'(lt_l hlt) + (rgt m0)[i]'(lt_r hlt) := by
    have hl1 : (elemEnv m0 st.data 48 (reg m0 .rdx) i).load 1 8 8 =
        (elemEnv m0 st2.data 48 (reg m0 .rdx) i (Host.addrOf (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b3Offset)).toBitVec).load
          1 8 8 := by
      have h := hel1.trans hel3.symm
      exact congrArg UInt64.toBitVec (congrArg EW.c1 h)
    rw [getElem_lft, ← hel3, hdx, hcx3, e2 .rcx (by simp), hcx1, hl1]
    have hcfE : (elemEnv m0 st2.data 48 (reg m0 .rdx) i
        (Host.addrOf (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b3Offset)).toBitVec).flags.cf =
        decide (((reg m0 .rsi).toNat >>> i) % 2 = 1) := hcf
    have hr8E : (elemEnv m0 st2.data 48 (reg m0 .rdx) i
        (Host.addrOf (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b3Offset)).toBitVec).regs .r8 = BitVec.ofNat 64 0 :=
      (e2 .r8 (by simp)).trans h8
    simp only [Sym.eval, SBool.eval, xor_eval, hcfE, hr8E, setb_eval]
    rw [← ewArg_bit]
    exact factor _ _ _
  refine Body.call_mul hmul hb2' hS (by decide) (by decide) slots_ok hwf3 hm3 hm3' hpc3 hk3 hsp3
    hw3 fun st4 hpc4 hb4' hprod hsv _ _ ↦ ?_
  rw [hdi, hsi, hI.acc, hfac] at hprod
  replace hprod : ewRet st4.data = acc m0 (i + 1) := by rw [acc_succ m0 hI.lt]; exact hprod
  have e4 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg st4.data r = reg st2.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (hsv _ rfl).trans (Match.reg_eq hm3 hm3' rfl rfl)
  -- `b3`: advance, compare
  refine exec_at (hb3 hp) run_b3 (Env.wf_nil _) (by intro l h; cases h) hpc4 (match_nil _)
    fun st5 hm5 hpc5 ↦ ?_
  have hb5' := hb4'.of_block (match_nil _) hm5 (Env.wf_nil _) rfl (after_eq run_b3 ▸ b3_keeps)
  have h4 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15],
      (Env.ofMachine st4.data []).regs r = reg st2.data r := e4
  have hacc : ewArg (reg st5.data .rax) (reg st5.data .rdx) = acc m0 (i + 1) := by
    rw [← hprod]
    rw [show reg st5.data .rax = reg st4.data .rax from Match.reg_eq (match_nil _) hm5 rfl rfl,
      show reg st5.data .rdx = reg st4.data .rdx from Match.reg_eq (match_nil _) hm5 rfl rfl]
    rfl
  have h12' : reg st2.data .r12 = BitVec.ofNat 64 (i + 1) := (e2 .r12 (by simp)).trans h12
  have h15 : reg st2.data .r15 = BitVec.ofNat 64 (cnt m0) :=
    (e2 .r15 (by simp)).trans ((e1 .r15 (by simp)).trans hI.r15)
  have hrsi : reg st5.data .rsi = BitVec.ofNat 64 (i + 1) :=
    (hm5.regs .rsi (.reg .r12) rfl).trans ((h4 .r12 (by simp)).trans h12')
  have hrbx : reg st5.data .rbx = reg m0 .rdx + BitVec.ofNat 64 (16 * (i + 1)) +
      BitVec.ofNat 64 8 := by
    rw [show reg st5.data .rbx = (Sym.bin .add .W64 (.lit 16) (.reg .rbx)).eval
      (Env.ofMachine st4.data []) from hm5.regs .rbx _ rfl, eval_add, eval_lit, eval_reg,
      h4 .rbx (by simp), e2 .rbx (by simp), e1 .rbx (by simp), hI.rbx]
    exact sixteen_add _ i
  have hr14 : reg st5.data .r14 = reg m0 .rsi :=
    (hm5.regs .r14 (.reg .r14) rfl).trans ((h4 .r14 (by simp)).trans
      ((e2 .r14 (by simp)).trans ((e1 .r14 (by simp)).trans hI.r14)))
  have hr15 : reg st5.data .r15 = BitVec.ofNat 64 (cnt m0) :=
    (hm5.regs .r15 (.reg .r15) rfl).trans ((h4 .r15 (by simp)).trans h15)
  simp only [PcOk] at hpc5
  rw [eval_not, eval_cmp_eq, eval_reg, eval_reg, h4 .r15 (by simp), h4 .r12 (by simp), h15, h12',
    ofNat_beq (by omega) (by omega)] at hpc5
  obtain ⟨hT, hF⟩ := pc_cond hpc5
  by_cases hlast : cnt m0 = i + 1
  · have hpc5' := hF (by simp [hlast])
    simp only [NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b3_length] at hpc5'
    refine exec_at (hb4 hp) run_b4 (Env.wf_nil _) (by intro l h; cases h) hpc5' (match_nil _)
      fun st6 hm6 hpc6 ↦ ?_
    have hb6' := hb5'.of_block (match_nil _) hm6 (Env.wf_nil _) rfl (after_eq run_b4 ▸ b4_keeps)
    simp only [PcOk] at hpc6
    refine Eventually.mono (finish hp hpre (hpc6.trans (lbl_4 hp)) hb6' ?_) fun _ h ↦ Or.inl h
    rw [show reg st6.data .rax = reg st5.data .rax from Match.reg_eq (match_nil _) hm6 rfl rfl,
      show reg st6.data .rdx = reg st5.data .rdx from Match.reg_eq (match_nil _) hm6 rfl rfl,
      hacc, hlast]
  · exact .done _ (Or.inr ⟨(hT (by simp [hlast])).trans (lbl_3 hp),
      ⟨hb5', by omega, hr15, hrsi, hr14, hrbx, hacc⟩⟩)

/-- **`eq_eval_fn` (`eq_above`'s closure) meets its contract.** -/
theorem eqEvalFn_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hS := hpre.1
  have h48 : 48 ≤ eqEvalFnStack := by decide
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h48)
    fun _ h ↦ h
  have hlen := (reg m0 .rdi).isLt
  have hc1 : cnt m0 ≤ (reg m0 .rdi).toNat := Nat.min_le_left _ _
  have hm : Match (frameEnv m0 m0 48) entryS m0 := match_frame
  refine exec_then (hb0 hp) run_b0 hwf (by intro l h; cases h) hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b0_length] at hpc1
  rw [eval_test, eval_min, ofNat_beq (by omega) (by decide)] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hz : cnt m0 = 0
  · -- `n = 0`: return `1`.
    have hpc1 := hT (by simp only [Env.ofMachine_regs]; exact decide_eq_true hz)
    refine exec_at (hb5 hp) (exec_after run_b0 run_b5) hwf (by intro l h; cases h)
      (hpc1.trans (lbl_1 hp)) hm1 fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b5_length] at hpc2
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
    simp only [PcOk, NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b1_length] at hpc2
    obtain ⟨hw, hregs, hmem, hsp⟩ := after_eq run_b1 ▸ b1_entry
    have hI : Inv m0 0 st2.data := by
      have h15 := hm2.regs .r15 _ rfl
      have hbx := hm2.regs .rbx _ rfl
      rw [eval_min] at h15
      rw [eval_add, eval_lit, eval_reg] at hbx
      refine ⟨Body.of_entry hS h48 hm2 hsp hw hregs hmem, Nat.pos_of_ne_zero hz, h15,
        hm2.regs .rsi _ rfl, hm2.regs .r14 _ rfl, ?_, ?_⟩
      · show st2.data.regs.get64 .rbx = _
        rw [hbx, Nat.mul_zero, add_ofNat_zero, BitVec.add_comm]
        rfl
      · show ewArg (st2.data.regs.get64 .rax) (st2.data.regs.get64 .rdx) = _
        rw [hm2.regs .rax _ rfl, hm2.regs .rdx _ rfl]
        rfl
    refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.b2Offset) ∧ ∃ i, cnt m0 - i = n ∧
      Inv m0 i st.data) (fun n st ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, hI⟩
    refine Eventually.mono (step hp hmul hpre hpc hI) fun st' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨cnt m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Arrays.EqEvalFn
