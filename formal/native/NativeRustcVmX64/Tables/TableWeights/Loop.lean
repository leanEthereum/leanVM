module

public import NativeRustcVmX64.Tables.TableWeights.Mul
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `table_weights`: a turn of the loop (x86-64)

`NativeRustcVmX64.Vm.TableWeights.label_3` (`b10`, `b11`) computes coordinate `c`'s factor parts (`head_step`); `b3`
multiplies weight `0` (`pre3_step`), `b4` to `b7` the next four (`mid_step`), `b8` weight `5`
(`last_step`); `b9` moves to the next coordinate or out of the loop (`turn_step`). `turn`: the
whole turn, from `It c` to `It (c + 1)` or the exit.
-/

namespace NativeRustcVmX64.Tables.TableWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Arrays
open NativeRustcVmX64.Vm.TableWeights NativeRustcVmX64.Field
open NativeRustcVm (wordOf ewsOf)

public section

/-- `16 + (a + 16 c)`. -/
theorem sixteen_add (i : Nat) :
    BitVec.ofNat 64 16 + BitVec.ofNat 64 (16 * i) = BitVec.ofNat 64 (16 * (i + 1)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

/-- `b9`'s test: the point's next element is its end exactly after the last coordinate. -/
theorem turn_cond {a r9 : BitVec 64} {c : Nat} (hc : c < r9.toNat) (hnw : a.toNat + 16 * r9.toNat ≤ 2 ^ 64)
    (h16 : 16 * r9.toNat < 2 ^ 64) :
    (BitVec.ofNat 64 16 + (a + BitVec.ofNat 64 (16 * c)) == a + r9 <<< 4) =
      decide (c + 1 = r9.toNat) := by
  have hsh : (r9 <<< 4).toNat = 16 * r9.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  by_cases h : c + 1 = r9.toNat
  · simp only [h, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hsh]
    omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hsh] at this
    have := a.isLt
    omega

variable [Host] {k : Nat}

/-- `b3` and its call: weight `0` multiplied. -/
theorem pre3_step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : TableWeightsPre m0) {c : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b3Offset)) (hI : Pre3 m0 c st.data) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b4Offset) ∧ Mid m0 c 1 st'.data) st := by
  obtain ⟨hS, -, -, -, -, hP⟩ := hpre
  have hco := hI.co
  have hc64 : c < 2 ^ 64 := by have := hI.lt; unfold n at this; have := (reg m0 .r9).isLt; omega
  obtain ⟨hwf, hm0, hval⟩ := hI.body.elem (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b4Offset)).toBitVec) hS h256
    (SliceIn.of_ok hP) (i := c) hI.lt (x := .bin .add .W64 (.reg .r8) (.reg .rbp)) (o := 0) (by
      rw [eval_add, eval_reg, eval_reg, Env.ofMachine_regs, Env.ofMachine_regs]
      show reg st.data .r8 + reg st.data .rbp = _
      rw [hI.r8, hco.rbp, add_ofNat_zero])
  replace hval := hval.trans (ch_eq hI.lt).symm
  obtain ⟨hregs, hw, hwr, hkw⟩ := after_eq run_b3 ▸ b3_ok
  refine exec_at (hb3 hp) run_b3 hwf (fun _ _ ↦ rfl) hpc hm0 fun st1 hm1 hpc1 ↦ ?_
  have hk' : ∀ o ∈ kfo ++ [200, 192] ++ wAll, firstOverlap 0 o 8 _ = none := hkw
  have gr : ∀ r v, _ → reg st1.data r = Sym.eval _ v := hm1.regs
  refine Body.call_mul hmul hI.body hS hle_mul (by omega : 208 ≤ 256) slots_ok' hwf hm0 hm1 hpc1
    (keepsRegs_nil _ _) (hregs (.rsp, .ptr 0 0) (by simp)) hw
    fun st2 hpc2 hb2 hprod hsv _ hfr ↦ .done _ ⟨hpc2, ?_⟩
  have hkept : ∀ o, o ∈ kfo ++ [200, 192] ++ wAll → o + 8 ≤ 264 →
      fw m0 st2.data o = fw m0 st.data o := fun o ho hle ↦ by
    rw [fw_call hle hfr, fw_keep hm1 rfl rfl hle (hk' o ho)]
  have h12 : reg st1.data .r12 = (ch m0 c).c0.toBitVec := by
    rw [gr _ _ (hregs (.r12, .load 1 0 8) (by simp)), ← hval]; rfl
  refine ⟨hb2, hI.lt, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun i hi ↦ absurd hi (by omega), ?_,
    fun i hi1 hi2 ↦ ?_⟩
  · rw [hsv .rbx rfl, gr _ _ (hregs (.rbx, .reg .rbx) (by simp))]; exact hco.rbx
  · rw [hsv .rbp rfl, gr _ _ (hregs (.rbp, .reg .rbp) (by simp))]; exact hco.rbp
  · rw [hsv .r14 rfl, gr _ _ (hregs (.r14, .reg .r14) (by simp))]; exact hco.r14
  · rw [hsv .r15 rfl, gr _ _ (hregs (.r15, .reg .r15) (by simp)), hsv .r13 rfl, gr _ _ (hregs (.r13, .reg .r13) (by simp))]; exact hco.tall
  · rw [hsv .r12 rfl]; exact h12
  · exact (hI.fixed.keep hm1 rfl rfl fun o ho ↦ hk' o (by simp [ho])).call hfr
  · rw [fw_call (by omega) hfr, fw_write (o := 184) (v := .bin .add .W64 (.reg .r8) (.reg .rbp))
      hm1 rfl (by omega) (hwr (184, _) (by simp)), eval_add, eval_reg, eval_reg,
      Env.ofMachine_regs, Env.ofMachine_regs]
    show reg st.data .r8 + reg st.data .rbp = _
    rw [hI.r8, hco.rbp]
  · rw [hkept 200 (by simp) (by omega), hkept 192 (by simp) (by omega)]; exact hI.w5
  · -- the product
    rw [hprod, show 1 - 1 = 0 from rfl, W_succ' hI.lt (by omega)]
    refine congrArg₂ EW.mul ?_ ?_
    · rw [gr _ _ (hregs (.rdi, .load 0 16 8) (by simp)),
        gr _ _ (hregs (.rsi, .load 0 24 8) (by simp))]
      simp only [Sym.eval]
      rw [load_fw rfl rfl, load_fw rfl rfl]
      exact hI.w 0 (by omega)
    · rw [gr _ _ (hregs (.rdx, facLo 152 (.load 1 0 8)) (by simp)),
        gr _ _ (hregs (.rcx, facHi 152) (by simp)), eval_facLo, eval_facHi]
      refine factor_block (j := 0) hco hc64 (by omega) (funext fun _ ↦ rfl) ?_ ?_
      · rw [load_fw rfl rfl]; exact hI.fixed.hoff (by omega)
      · simp only [Sym.eval]; rw [← hval]; rfl
  · -- the weights to do
    have hm := mem_wAll (show i < 5 by omega)
    rw [wE_call hfr, wE_keep hm1 rfl rfl (hk' _ (by simp [hm.1])) (hk' _ (by simp [hm.2]))]
    exact hI.w i hi2

/-- `b8` and its call: weight `4`'s product stored, weight `5` multiplied. -/
theorem last_step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hS : StackOk m0 tableWeightsStack) {c : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b8Offset)) (hI : Mid m0 c 5 st.data) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b9Offset) ∧ Done m0 c st'.data) st := by
  have hco := hI.co
  have hc64 : c < 2 ^ 64 := by have := hI.lt; unfold n at this; have := (reg m0 .r9).isLt; omega
  have hwf := hI.body.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b9Offset)).toBitVec) hS h256
  have hm0 := hI.body.mid_match (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b9Offset)).toBitVec)
  obtain ⟨hregs, hw, hwr, hkw⟩ := after_eq run_b8 ▸ b8_ok
  refine exec_at (hb8 hp) run_b8 hwf (fun _ _ ↦ rfl) hpc hm0 fun st1 hm1 hpc1 ↦ ?_
  have hk' : ∀ o ∈ kfo ++ [184] ++ wOthers 4, firstOverlap 0 o 8 _ = none := hkw
  have gr : ∀ r v, _ → reg st1.data r = Sym.eval _ v := hm1.regs
  refine Body.call_mul hmul hI.body hS hle_mul (by omega : 208 ≤ 256) slots_ok' hwf hm0 hm1 hpc1
    (keepsRegs_nil _ _) (hregs (.rsp, .ptr 0 0) (by simp)) hw
    fun st2 hpc2 hb2 hprod hsv _ hfr ↦ .done _ ⟨hpc2, ?_⟩
  have hkept : ∀ o, o ∈ kfo ++ [184] ++ wOthers 4 → o + 8 ≤ 264 →
      fw m0 st2.data o = fw m0 st.data o := fun o ho hle ↦ by
    rw [fw_call hle hfr, fw_keep hm1 rfl rfl hle (hk' o ho)]
  refine ⟨hb2, hI.lt, ?_, ?_, ?_, ?_, fun i hi ↦ ?_, ?_⟩
  · rw [hsv .rbx rfl, gr _ _ (hregs (.rbx, .reg .rbx) (by simp))]; exact hco.rbx
  · rw [hsv .rbp rfl, gr _ _ (hregs (.rbp, .reg .rbp) (by simp))]; exact hco.rbp
  · exact (hI.fixed.keep hm1 rfl rfl fun o ho ↦ hk' o (by simp [ho])).call hfr
  · rw [hkept 184 (by simp) (by omega)]; exact hI.cur
  · rw [wE_call hfr]
    by_cases hi4 : i = 4
    · subst hi4
      unfold wE
      rw [fw_write (o := wlo 4) (v := .reg .rax) hm1 rfl (by decide) (hwr (88, .reg .rax) (by simp)),
        fw_write (o := whi 4) (v := .reg .rdx) hm1 rfl (by decide) (hwr (80, .reg .rdx) (by simp))]
      exact hI.prod
    · have hm := mem_wOthers (show i < 5 by omega) hi4
      rw [wE_keep hm1 rfl rfl (hk' _ (by simp [hm.1])) (hk' _ (by simp [hm.2]))]
      exact hI.done i (by omega)
  · rw [hprod, W_succ' hI.lt (by omega)]
    refine congrArg₂ EW.mul ?_ ?_
    · rw [gr _ _ (hregs (.rdi, .load 0 200 8) (by simp)), gr _ _ (hregs (.rsi, .load 0 192 8) (by simp))]
      simp only [Sym.eval]
      rw [load_fw rfl rfl, load_fw rfl rfl]
      exact hI.w5
    · rw [gr _ _ (hregs (.rdx, .bin .xor .W64 (.ite (.not (ltH 112)) (.lit 0) (.reg .r15)) (.reg .r12))
        (by simp)), gr _ _ (hregs (.rcx, facHi 112) (by simp)),
        eval_facLo8, eval_facHi]
      refine factor_block (j := 5) hco hc64 (by omega) (funext fun _ ↦ rfl) ?_ ?_
      · rw [load_fw rfl rfl]; exact hI.fixed.hoff (by omega)
      · exact hI.r12

/-- **The loop head** `NativeRustcVmX64.Vm.TableWeights.label_3` (`b10`, and `b11` for a coordinate of the equality
point): coordinate `c`'s factor parts. -/
theorem head_step (hp : Placed code k) {m0 : MachineData} (hpre : TableWeightsPre m0) {c : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b10Offset)) (hI : It m0 c st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b3Offset) ∧ Pre3 m0 c st'.data)
      st := by
  obtain ⟨hS, -, -, -, hE, hP⟩ := hpre
  have hc64 : c < 2 ^ 64 := by have := hI.lt; unfold n at this; have := (reg m0 .r9).isLt; omega
  obtain ⟨hwf, hm0, hval⟩ := hI.body.elem (ret := 0) hS h256
    (SliceIn.of_ok hP) (i := c) hI.lt (x := .bin .add .W64 (.reg .r8) (.reg .rbp)) (o := 0) (by
      rw [eval_add, eval_reg, eval_reg, Env.ofMachine_regs, Env.ofMachine_regs]
      show reg st.data .r8 + reg st.data .rbp = _
      rw [hI.r8, hI.rbp, add_ofNat_zero])
  replace hval := hval.trans (ch_eq hI.lt).symm
  obtain ⟨hregs, hw, hwr, hkw, hkr⟩ := after_eq run_b10 ▸ b10_ok
  refine exec_at (hb10 hp) run_b10 hwf (fun _ h ↦ by cases h) hpc hm0 fun st1 hm1 hpc1 ↦ ?_
  have hk' : ∀ o ∈ kfo ++ wAll, firstOverlap 0 o 8 _ = none := hkw
  have gr : ∀ r v, _ → reg st1.data r = Sym.eval _ v := hm1.regs
  have hb1 := Body.of_frame hI.body hS h256 hwf hm0 hm1 hkr hw (by omega : 208 ≤ 256) slots_ok'
  have hfx : Fixed m0 st1.data := hI.fixed.keep hm1 rfl rfl fun o ho ↦ hk' o (by simp [ho])
  have hw1 : ∀ i < 5, wE m0 st1.data i = (W m0 c).getD i 0 := fun i hi ↦ by
    have hm := mem_wAll hi
    rw [wE_keep hm1 rfl rfl (hk' _ (by simp [hm.1])) (hk' _ (by simp [hm.2]))]
    exact hI.w i hi
  have hw5 : ewArg (fw m0 st1.data 200) (fw m0 st1.data 192) = (W m0 c).getD 5 0 := by
    rw [fw_write (o := 200) (v := .reg .rax) hm1 rfl (by omega) (hwr (200, .reg .rax) (by simp)),
      fw_write (o := 192) (v := .reg .rdx) hm1 rfl (by omega) (hwr (192, .reg .rdx) (by simp))]
    exact hI.w5
  have hx1 : reg st1.data .rbx = BitVec.ofNat 64 c := by
    rw [gr _ _ (hregs (.rbx, .reg .rbx) (by simp))]; exact hI.rbx
  have hp1 : reg st1.data .rbp = BitVec.ofNat 64 (16 * c) := by
    rw [gr _ _ (hregs (.rbp, .reg .rbp) (by simp))]; exact hI.rbp
  have h81 : reg st1.data .r8 = reg m0 .r8 := by
    rw [gr _ _ (hregs (.r8, .reg .r8) (by simp))]; exact hI.r8
  have h14 : reg st1.data .r14 = (ch m0 c).c1.toBitVec := by
    rw [gr _ _ (hregs (.r14, .load 1 8 8) (by simp)), ← hval]; rfl
  simp only [PcOk] at hpc1
  have hcond : ∀ env' : Env, env'.regs .rbx = BitVec.ofNat 64 c → env'.load 0 176 8 = reg m0 .rcx →
      (SBool.not (.cmp .ult .W64 (.reg .rbx) (.load 0 176 8))).eval env' =
        !decide (c < (reg m0 .rcx).toNat) := fun env' h1 h2 ↦ by
    simp only [SBool.eval, CmpOp.apply, low_W64, BitVec.ult, Sym.eval, h1, h2, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hc64]
  rw [hcond _ hI.rbx (by rw [load_fw rfl rfl]; exact hI.fixed.get (by simp [kf]))] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hlt : c < (reg m0 .rcx).toNat
  · -- `b11`: the equality point's coordinate
    have hpc1' := hF (by simp [hlt])
    simp only [NativeRustcVmX64.Vm.TableWeights.b10_length] at hpc1'
    obtain ⟨hwf2, hm2, hvalE⟩ := hb1.elem (ret := 0) hS h256 (SliceIn.of_ok hE) (i := c) hlt
      (x := .bin .add .W64 (.load 0 104 8) (.reg .rbp)) (o := 0) (by
        rw [eval_add, eval_load, eval_reg, Env.ofMachine_regs, load_fw rfl rfl,
          hfx.get (o := 104) (v := reg m0 .rdx) (by simp [kf])]
        show _ + reg st1.data .rbp = _
        rw [hp1, add_ofNat_zero])
    replace hvalE := hvalE.trans (E_getD hlt).symm
    obtain ⟨hregs2, hmem2, hka2⟩ := after_eq run_b11 ▸ b11_ok
    refine exec_at (hb11 hp) run_b11 hwf2 (fun _ h ↦ by cases h) hpc1' hm2 fun st2 hm3 hpc2 ↦ ?_
    have gr2 : ∀ r v, _ → reg st2.data r = Sym.eval _ v := hm3.regs
    have hd : st2.data.dmem = st1.data.dmem := hm3.dmem_eq hwf2 hmem2
    simp only [PcOk] at hpc2
    refine .done _ ⟨hpc2.trans (lbl_5 hp), hb1.of_block hm2 hm3 hwf2 rfl hka2, hI.lt, ⟨?_, ?_, ?_, ?_⟩,
      ?_, fun p hp' ↦ by rw [fw_of_dmem hd]; exact hfx p hp', fun i hi ↦ ?_, ?_⟩
    · rw [gr2 _ _ (hregs2 (.rbx, .reg .rbx) (by simp))]; exact hx1
    · rw [gr2 _ _ (hregs2 (.rbp, .reg .rbp) (by simp))]; exact hp1
    · rw [gr2 _ _ (hregs2 (.r14, .reg .r14) (by simp))]; exact h14
    · rw [gr2 _ _ (hregs2 (.r15, .bin .xor .W64 (.load 1 0 8) (.lit 1)) (by simp)),
        gr2 _ _ (hregs2 (.r13, .bin .xor .W64 (.load 1 8 8) (.reg .r14)) (by simp))]
      simp only [Sym.eval, xor_eval, Env.ofMachine_regs]
      show ewArg (_ ^^^ _ ^^^ _) (_ ^^^ reg st1.data .r14) = _
      rw [h14]
      unfold fac
      rw [← fac_lt, ← hvalE]
      rfl
    · rw [gr2 _ _ (hregs2 (.r8, .reg .r8) (by simp))]; exact h81
    · unfold wE; rw [fw_of_dmem hd, fw_of_dmem hd]; exact hw1 i hi
    · rw [fw_of_dmem hd, fw_of_dmem hd]; exact hw5
  · -- straight to `NativeRustcVmX64.Vm.TableWeights.label_5`
    have hpc1' := hT (by simp [hlt])
    refine .done _ ⟨hpc1'.trans (lbl_5 hp), hb1, hI.lt, ⟨hx1, hp1, h14, ?_⟩, h81, hfx, hw1, hw5⟩
    rw [gr _ _ (hregs (.r15, .lit 1) (by simp)), gr _ _ (hregs (.r13, .load 1 8 8) (by simp))]
    unfold fac
    rw [E_getD_ge (by omega), ← fac_ge, ← hval]
    rfl

/-- **`b9`**: the next coordinate, or out of the loop after the last. -/
theorem turn_step (hp : Placed code k) {m0 : MachineData} (hpre : TableWeightsPre m0) {c : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b9Offset)) (hI : Done m0 c st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b10Offset) ∧ It m0 (c + 1) st'.data) ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b13Offset) ∧ Fin m0 st'.data)) st := by
  obtain ⟨hS, -, -, -, -, hP⟩ := hpre
  have hwf := hI.body.wf (vars := fun _ ↦ 0) (ret := 0) hS h256
  have hm0 := hI.body.mid_match (vars := fun _ ↦ 0) (ret := 0)
  obtain ⟨hregs, hmem, hka⟩ := after_eq run_b9 ▸ b9_ok
  refine exec_at (hb9 hp) run_b9 hwf (fun _ h ↦ by cases h) hpc hm0 fun st1 hm1 hpc1 ↦ ?_
  have gr : ∀ r v, _ → reg st1.data r = Sym.eval _ v := hm1.regs
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem
  have hb1 := hI.body.of_block hm0 hm1 hwf rfl hka
  have hfx : Fixed m0 st1.data := fun p hp' ↦ by rw [fw_of_dmem hd]; exact hI.fixed p hp'
  have hw : ∀ i < 5, wE m0 st1.data i = (W m0 (c + 1)).getD i 0 := fun i hi ↦ by
    unfold wE; rw [fw_of_dmem hd, fw_of_dmem hd]; exact hI.w i hi
  have hw5 : ewRet st1.data = (W m0 (c + 1)).getD 5 0 := by
    unfold ewRet
    rw [gr _ _ (hregs (.rax, .reg .rax) (by simp)), gr _ _ (hregs (.rdx, .reg .rdx) (by simp))]
    exact hI.w5
  have hlen := lt_of_offStack hP.1.2 hP.2
  have hnw := hP.1.2
  unfold NoWrap at hnw
  simp only [PcOk] at hpc1
  have hcond : (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.load 0 184 8)) (.load 0 168 8)).eval
      (frameEnv m0 st.data 256 (fun _ ↦ 0) 0) = decide (c + 1 = n m0) := by
    rw [eval_cmp_eq, eval_add, eval_lit, eval_load, eval_load, load_fw rfl rfl, load_fw rfl rfl,
      hI.cur, hI.fixed.get (o := 168) (v := endp m0) (by simp [kf]), endp]
    exact turn_cond hI.lt (by omega) (by omega)
  rw [hcond] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hlast : c + 1 = n m0
  · refine .done _ (Or.inr ⟨(hT (by simp [hlast])).trans (lbl_6 hp), hb1,
      hfx.get (by simp [kf]), ?_, ?_⟩)
    · rw [← hlast]; exact hw
    · rw [← hlast]; exact hw5
  · have hpc1' := hF (by simp [hlast])
    simp only [NativeRustcVmX64.Vm.TableWeights.b9_length] at hpc1'
    refine .done _ (Or.inl ⟨hpc1', hb1, by have := hI.lt; omega, ?_, ?_, ?_, hfx, hw, hw5⟩)
    · rw [gr _ _ (hregs (.rbx, .bin .add .W64 (.reg .rbx) (.lit 1)) (by simp)), eval_add, eval_reg,
        eval_lit, Env.ofMachine_regs]
      show reg st.data .rbx + _ = _
      rw [hI.rbx, ← BitVec.ofNat_add]
    · rw [gr _ _ (hregs (.rbp, .bin .add .W64 (.lit 16) (.reg .rbp)) (by simp)), eval_add, eval_reg,
        eval_lit, Env.ofMachine_regs]
      show _ + reg st.data .rbp = _
      rw [hI.rbp, sixteen_add]
    · rw [gr _ _ (hregs (.r8, .load 0 160 8) (by simp)), eval_load, load_fw rfl rfl]
      exact hI.fixed.get (by simp [kf])

end

end NativeRustcVmX64.Tables.TableWeights
