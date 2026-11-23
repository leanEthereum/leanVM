module

public import NativeRustcVmX64.Tables.TableWeights.Defs
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.TableWeights.Names

/-!
# `table_weights`: a coordinate's six multiplications (x86-64)

Where the blocks are (`hb3` …, the labels), then the blocks of one coordinate: `NativeRustcVmX64.Vm.TableWeights.label_5`
(`b3`) multiplies weight `0` (`pre3_step`), each of `b4` to `b7` stores the previous product and
multiplies the next weight (`mid_step`), `b8` stores weight `4`'s product and multiplies weight `5`
(`last_step`).
-/

namespace NativeRustcVmX64.Tables.TableWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Arrays
open NativeRustcVmX64.Vm.TableWeights NativeRustcVmX64.Field
open NativeRustcVm (wordOf ewsOf)

public section

theorem h256 : 256 ≤ tableWeightsStack := by decide
theorem hle_mul : 256 + ewMulStack ≤ tableWeightsStack := by decide

theorem keepsRegs_nil (S₀ S₁ : SState) : keepsRegs S₀ S₁ (freeRegs slots) = true := by
  rw [freeRegs_slots]; rfl

theorem slots_ok' : ∀ p ∈ slots, 208 ≤ p.1 ∧ p.1 + 8 ≤ 256 := slots_ok

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b9Offset) :=
  b9_in_code.trans hp.1 (by simp [b9])
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b10Offset) :=
  b10_in_code.trans hp.1 (by simp [b10])
theorem hb11 (hp : Placed code k) : b11.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b11Offset) :=
  b11_in_code.trans hp.1 (by simp [b11])
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b12Offset) :=
  b12_in_code.trans hp.1 (by simp [b12])
theorem hb13 (hp : Placed code k) : b13a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b13Offset) ∧
    b13b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.TableWeights.b13Offset + b13a.length) := by
  have h := b13_in_code.trans hp.1 (by simp [b13])
  rw [← List.take_append_drop 24 b13] at h
  exact h.append

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableWeights.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.TableWeights.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableWeights.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b12Offset) :=
  hp.label NativeRustcVmX64.Vm.TableWeights.label_1_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableWeights.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b10Offset) :=
  hp.label NativeRustcVmX64.Vm.TableWeights.label_3_at
theorem lbl_5 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableWeights.label_5 = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b3Offset) :=
  hp.label NativeRustcVmX64.Vm.TableWeights.label_5_at
theorem lbl_6 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableWeights.label_6 = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b13Offset) :=
  hp.label NativeRustcVmX64.Vm.TableWeights.label_6_at

omit [Host] in
theorem reg_atom [Labels] {env : Env} {S : SState} {st : MachineData} (hm : Match env S st)
    {r : Reg64} (h : S.reg r = some (.reg r)) : reg st r = env.regs r := hm.regs r _ h

/-- **A multiplying block `b<3 + j>`** (`1 ≤ j ≤ 4`) and its call: weight `j - 1`'s product
stored, weight `j` multiplied. -/
theorem mid_step (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {m0 : MachineData}
    (hS : StackOk m0 tableWeightsStack) {c j : Nat} (hj1 : 1 ≤ j) (hj4 : j ≤ 4)
    {ds : List Directive} {kk : Nat} {S₁ : SState}
    (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds mS = some (S₁, .call NativeRustcVmX64.Vm.EWMul.entryLabel))
    (hok : MidOk j S₁) {st : MachineState} (hpc : st.pc = Host.addrOf kk)
    (hI : Mid m0 c j st.data) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = Host.addrOf (kk + ds.length) ∧ Mid m0 c (j + 1) st'.data) st := by
  obtain ⟨hregs, hw, hwr, hkw⟩ := hok
  have hwf := hI.body.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (kk + ds.length)).toBitVec)
    hS h256
  have hm0 := hI.body.mid_match (vars := fun _ ↦ 0) (ret := (Host.addrOf (kk + ds.length)).toBitVec)
  refine exec_at hk hx hwf (fun _ _ ↦ rfl) hpc hm0 fun st1 hm1 hpc1 ↦ ?_
  have g : ∀ {r v}, (r, v) ∈ ([(.rdi, .load 0 (wlo j) 8), (.rsi, .load 0 (whi j) 8),
      (.rdx, facLo (hoff j) (.reg .r12)), (.rcx, facHi (hoff j)), (.rsp, .ptr 0 0)] ++ atoms :
        List (Reg64 × Sym)) → reg st1.data r = v.eval (frameEnv m0 st.data 256 (fun _ ↦ 0)
          (Host.addrOf (kk + ds.length)).toBitVec) :=
    fun h ↦ hm1.regs _ _ (hregs _ h)
  have hk' : ∀ o ∈ kfo ++ [184, 200, 192] ++ wOthers (j - 1), firstOverlap 0 o 8 S₁.mem = none :=
    hkw
  refine Body.call_mul hmul hI.body hS hle_mul (by omega : 208 ≤ 256) slots_ok' hwf hm0 hm1 hpc1
    (keepsRegs_nil _ _) (hregs (.rsp, .ptr 0 0) (by simp)) hw
    fun st2 hpc2 hb2 hprod hsv _ hfr ↦ .done _ ⟨hpc2, ?_⟩
  have hreg : ∀ r, calleeSaved r = true → (r, Sym.reg r) ∈ atoms →
      reg st2.data r = reg st.data r := fun r hc ha ↦
    (hsv r hc).trans (g (List.mem_append_right _ ha))
  have hco := hI.co
  have hc64 : c < 2 ^ 64 := by have := hI.lt; unfold n at this; have := (reg m0 .r9).isLt; omega
  have hkept : ∀ o, o ∈ kfo ++ [184, 200, 192] ++ wOthers (j - 1) → o + 8 ≤ 264 →
      fw m0 st2.data o = fw m0 st.data o := fun o ho hle ↦ by
    rw [fw_call hle hfr, fw_keep hm1 rfl rfl hle (hk' o ho)]
  refine ⟨hb2, hI.lt, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun i hi ↦ ?_, ?_, fun i hi1 hi2 ↦ ?_⟩
  · rw [hreg .rbx rfl (by simp [atoms])]; exact hco.rbx
  · rw [hreg .rbp rfl (by simp [atoms])]; exact hco.rbp
  · rw [hreg .r14 rfl (by simp [atoms])]; exact hco.r14
  · rw [hreg .r15 rfl (by simp [atoms]), hreg .r13 rfl (by simp [atoms])]; exact hco.tall
  · rw [hreg .r12 rfl (by simp [atoms])]; exact hI.r12
  · exact (hI.fixed.keep hm1 rfl rfl fun o ho ↦ hk' o (by simp [ho])).call hfr
  · rw [hkept 184 (by simp) (by omega)]; exact hI.cur
  · rw [hkept 200 (by simp) (by omega), hkept 192 (by simp) (by omega)]; exact hI.w5
  · -- the weights done
    rw [wE_call hfr]
    by_cases hij : i = j - 1
    · subst hij
      unfold wE
      rw [fw_write (o := wlo (j - 1)) (v := .reg .rax) hm1 rfl
          (by have := wlo_le (j - 1); omega) (hwr (wlo (j - 1), .reg .rax) (by simp)),
        fw_write (o := whi (j - 1)) (v := .reg .rdx) hm1 rfl
          (by have := whi_le (j - 1); omega) (hwr (whi (j - 1), .reg .rdx) (by simp))]
      exact hI.prod
    · have hm := mem_wOthers (show i < 5 by omega) hij
      rw [wE_keep hm1 rfl rfl (hk' _ (by simp [hm.1])) (hk' _ (by simp [hm.2]))]
      exact hI.done i (by omega)
  · -- the product
    rw [show j + 1 - 1 = j by omega, hprod, W_succ' hI.lt (by omega)]
    refine congrArg₂ EW.mul ?_ ?_
    · rw [g (r := .rdi) (v := .load 0 (wlo j) 8) (by simp), g (r := .rsi) (v := .load 0 (whi j) 8) (by simp)]
      simp only [Sym.eval]
      rw [load_fw rfl rfl, load_fw rfl rfl]
      exact hI.todo j le_rfl (by omega)
    · rw [g (r := .rdx) (v := facLo (hoff j) (.reg .r12)) (by simp),
        g (r := .rcx) (v := facHi (hoff j)) (by simp), eval_facLo, eval_facHi]
      refine factor_block (j := j) hco hc64 (by omega) (funext fun _ ↦ rfl) ?_ ?_
      · rw [load_fw rfl rfl]; exact hI.fixed.hoff (by omega)
      · simp only [Sym.eval, Env.ofMachine_regs]; exact hI.r12
  · -- the weights to do
    have hm := mem_wOthers (show i < 5 by omega) (show i ≠ j - 1 by omega)
    rw [wE_call hfr,
      wE_keep hm1 rfl rfl (hk' _ (by simp [hm.1])) (hk' _ (by simp [hm.2]))]
    exact hI.todo i (by omega) hi2

end

end NativeRustcVmX64.Tables.TableWeights
