module

public import NativeRustcVmX64.Tables.TableWeights.Turn
public import NativeRustcVmX64.Tables.Common

/-!
# `table_weights`: the entry and the exit (x86-64)

`entry_step`: the prologue (`b0`) into the loop (`b1`, `It 0`) or, for an empty point, to the
exit with the weights `1` (`b12`, `Fin`). `exit_step`: the weights stored at `out` (`b13a`), the
epilogue (`b13b`).
-/

namespace NativeRustcVmX64.Tables.TableWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Arrays
open NativeRustcVmX64.Vm.TableWeights NativeRustcVmX64.Field
open NativeRustcVm (wordOf wordsOf ewsOf)

public section

theorem ewArg_one_zero : ewArg (BitVec.ofNat 64 1) (BitVec.ofNat 64 0) = 1 := rfl

variable [Host] {k : Nat}

/-- **The entry**: into the loop, or straight to the exit for an empty point. -/
theorem entry_step (hp : Placed code k) {m0 : MachineData} (hpre : TableWeightsPre m0) :
    Eventually (step1 Host.exe) (fun st' ↦ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b10Offset) ∧ It m0 0 st'.data) ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b13Offset) ∧ Fin m0 st'.data)) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b0Offset)⟩ := by
  obtain ⟨hS, -, -, ⟨hHr, hHo, -⟩, -, -⟩ := hpre
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h256)
    fun _ h ↦ h
  have hm : Match (frameEnv m0 m0 256) entryS m0 := match_frame
  obtain ⟨hsl, hfree, hw0, hsp0, hwr0, hreg0⟩ := after_eq run_b0 ▸ b0_ok
  refine exec_then (hb0 hp) run_b0 hwf (fun _ h ↦ by cases h) hm fun st1 hm1 hpc1 ↦ ?_
  have gr : ∀ r v, _ → reg st1.data r = Sym.eval _ v := hm1.regs
  have hb1 : Bd m0 st1.data := Body.of_entry hS h256 hm1 hsp0 hsl hfree hw0
  have hk1 : st1.data.dmem = st1.data.dmem := rfl
  have h96 : fw m0 st1.data 96 = reg m0 .rdi :=
    fw_write (o := 96) (v := .reg .rdi) hm1 rfl (by omega) (hwr0 (96, .reg .rdi) (by simp))
  have h104 : fw m0 st1.data 104 = reg m0 .rdx :=
    fw_write (o := 104) (v := .reg .rdx) hm1 rfl (by omega) (hwr0 (104, .reg .rdx) (by simp))
  have h176 : fw m0 st1.data 176 = reg m0 .rcx :=
    fw_write (o := 176) (v := .reg .rcx) hm1 rfl (by omega) (hwr0 (176, .reg .rcx) (by simp))
  have hr8 : reg st1.data .r8 = reg m0 .r8 := gr _ _ (hreg0 (.r8, .reg .r8) (by simp))
  have hr9 : reg st1.data .r9 = reg m0 .r9 := gr _ _ (hreg0 (.r9, .reg .r9) (by simp))
  have hrsi : reg st1.data .rsi = reg m0 .rsi := gr _ _ (hreg0 (.rsi, .reg .rsi) (by simp))
  simp only [PcOk, NativeRustcVmX64.Vm.TableWeights.b0_length] at hpc1
  rw [eval_test, eval_reg, Env.ofMachine_regs] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hz : reg m0 .r9 = BitVec.ofNat 64 0
  · -- an empty point: the weights `1`
    have hpc2 := (hT (by simp [hz])).trans (lbl_1 hp)
    have hwf2 := hb1.wf (vars := fun _ ↦ 0) (ret := 0) hS h256
    have hm2 := hb1.mid_match (vars := fun _ ↦ 0) (ret := 0)
    obtain ⟨hregs, hw, hwr, hkw, hkr⟩ := after_eq run_b12 ▸ b12_ok
    refine exec_at (hb12 hp) run_b12 hwf2 (fun _ h ↦ by cases h) hpc2 hm2 fun st2 hm3 hpc3 ↦ ?_
    simp only [PcOk, NativeRustcVmX64.Vm.TableWeights.b12_length] at hpc3
    have hn0 : n m0 = 0 := by unfold n; rw [hz]; rfl
    refine .done _ (Or.inr ⟨hpc3, Body.of_frame hb1 hS h256 hwf2 hm2 hm3 hkr hw (by omega)
      slots_ok', ?_, fun i hi ↦ ?_, ?_⟩)
    · rw [fw_keep hm3 rfl rfl (by omega) (hkw 96 (by simp))]; exact h96
    · rw [hn0, W_zero (by omega)]
      unfold wE
      have hlo := hwr (wlo i, .lit 1)
      have hhi := hwr (whi i, .lit 0)
      rw [fw_write hm3 rfl (by have := wlo_le i; omega) (hlo (by
          match i, hi with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [wlo])),
        fw_write hm3 rfl (by have := whi_le i; omega) (hhi (by
          match i, hi with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [whi]))]
      rfl
    · rw [hn0, W_zero (by omega)]
      unfold ewRet
      show ewArg (st2.data.regs.get64 .rax) (st2.data.regs.get64 .rdx) = 1
      rw [hm3.regs _ _ (hregs (.rax, .lit 1) (by simp)), hm3.regs _ _ (hregs (.rdx, .lit 0) (by simp))]
      rfl
  · -- the loop
    have hpc2 := hF (by simp [hz])
    have hlen : (reg m0 .r9).toNat ≠ 0 := fun h ↦ hz (BitVec.eq_of_toNat_eq (by simpa using h))
    have hHo' : Apart (stackBelow m0 256) (256 + 8) (reg m0 .rsi) 48 := by
      have h1 := h256
      have hS1 := hS.1
      have hr := (rspOf m0).isLt
      have hh := hHo
      unfold OffStack Apart at hh
      unfold Apart
      rw [stackBelow_toNat (by omega)]
      rw [stackBelow_toNat hS1] at hh
      omega
    have hwf2 := wf_two (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h256) hb1.kept
      (show Readable st1.data (reg m0 .rsi) 48 from ⟨fun i hi ↦ hb1.kept _ (hHr.1 i hi), hHr.2⟩)
      hHo'
    have hm2 : Match (Env.ofMachine st1.data [(stackBelow m0 256, 256 + 8), (reg m0 .rsi, 48)])
        htS st1.data :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb1.rsp, trivial⟩ trivial trivial
        ⟨by show reg st1.data .rsi = _; rw [hrsi]; simp, trivial⟩
    obtain ⟨hregs, hw, hwr, hkw, hkr⟩ := after_eq run_b1 ▸ b1_ok
    refine exec_at (TableWeights.hb1 hp) run_b1 hwf2 (fun _ h ↦ by cases h) hpc2 hm2
      fun st2 hm3 hpc3 ↦ ?_
    simp only [PcOk] at hpc3
    have gr3 : ∀ r v, _ → reg st2.data r = Sym.eval _ v := hm3.regs
    have hht : ∀ j < 6, (Env.ofMachine st1.data [(stackBelow m0 256, 256 + 8),
        (reg m0 .rsi, 48)]).load 1 (8 * j) 8 = hword m0 j := fun j hj ↦ by
      rw [load8_eq, Env.base_eq (b := reg m0 .rsi) (n := 48) rfl, Env.ofMachine_mem0, hword]
      exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun i hi ↦ by
        rw [addr_add]
        exact same_of_apart hb1.same hS hHr.2 hHo (apart_zero _ _) noWrap_zero _ (by omega))
    have hW : ∀ o (v : Sym), (o, v) ∈ [(152, Sym.load 1 0 8), (144, .load 1 8 8),
        (136, .load 1 16 8), (128, .load 1 24 8), (120, .load 1 32 8), (112, .load 1 40 8),
        (16, .lit 1), (24, .lit 0), (32, .lit 1), (40, .lit 0), (48, .lit 1), (56, .lit 0),
        (64, .lit 1), (72, .lit 0), (88, .lit 1), (80, .lit 0),
        (168, .bin .add .W64 (.reg .r8) (.bin .shl .W64 (.reg .r9) (.lit 4))), (160, .reg .r8)] →
        o + 8 ≤ 264 → fw m0 st2.data o = v.eval (Env.ofMachine st1.data
          [(stackBelow m0 256, 256 + 8), (reg m0 .rsi, 48)]) :=
      fun o v h hle ↦ fw_write hm3 rfl hle (hwr (o, v) h)
    have hK : ∀ o ∈ [96, 104, 176], fw m0 st2.data o = fw m0 st1.data o := fun o ho ↦
      fw_keep hm3 rfl rfl (by simp at ho; omega) (hkw o ho)
    refine .done _ (Or.inl ⟨hpc3.trans (lbl_3 hp), Body.of_frame hb1 hS h256 hwf2 hm2 hm3 hkr hw
      (by omega) slots_ok', Nat.pos_of_ne_zero hlen, ?_, ?_, ?_, ?_, fun i hi ↦ ?_, ?_⟩)
    · rw [gr3 _ _ (hregs (.rbx, .lit 0) (by simp))]; rfl
    · rw [gr3 _ _ (hregs (.rbp, .lit 0) (by simp))]; rfl
    · rw [gr3 _ _ (hregs (.r8, .reg .r8) (by simp))]; exact hr8
    · intro p hp'
      simp only [kf, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hK 96 (by simp)]; exact h96
      · rw [hK 104 (by simp)]; exact h104
      · rw [hK 176 (by simp)]; exact h176
      · rw [hW _ (.load 1 0 8) (by simp) (by omega), eval_load]; exact hht 0 (by omega)
      · rw [hW _ (.load 1 8 8) (by simp) (by omega), eval_load]; exact hht 1 (by omega)
      · rw [hW _ (.load 1 16 8) (by simp) (by omega), eval_load]; exact hht 2 (by omega)
      · rw [hW _ (.load 1 24 8) (by simp) (by omega), eval_load]; exact hht 3 (by omega)
      · rw [hW _ (.load 1 32 8) (by simp) (by omega), eval_load]; exact hht 4 (by omega)
      · rw [hW _ (.load 1 40 8) (by simp) (by omega), eval_load]; exact hht 5 (by omega)
      · rw [hW _ (.bin .add .W64 (.reg .r8) (.bin .shl .W64 (.reg .r9) (.lit 4))) (by simp)
          (by omega), eval_add, eval_shl_lit (j := 4) _ (by omega), eval_reg, eval_reg,
          Env.ofMachine_regs, Env.ofMachine_regs]
        show reg st1.data .r8 + reg st1.data .r9 <<< 4 = _
        rw [hr8, hr9]; rfl
      · rw [hW _ (.reg .r8) (by simp) (by omega), eval_reg, Env.ofMachine_regs]; exact hr8
    · rw [W_zero (by omega)]
      unfold wE
      match i, hi with
      | 0, _ => rw [show wlo 0 = 16 from rfl, show whi 0 = 24 from rfl,
          hW 16 (.lit 1) (by simp) (by omega), hW 24 (.lit 0) (by simp) (by omega)]; rfl
      | 1, _ => rw [show wlo 1 = 32 from rfl, show whi 1 = 40 from rfl,
          hW 32 (.lit 1) (by simp) (by omega), hW 40 (.lit 0) (by simp) (by omega)]; rfl
      | 2, _ => rw [show wlo 2 = 48 from rfl, show whi 2 = 56 from rfl,
          hW 48 (.lit 1) (by simp) (by omega), hW 56 (.lit 0) (by simp) (by omega)]; rfl
      | 3, _ => rw [show wlo 3 = 64 from rfl, show whi 3 = 72 from rfl,
          hW 64 (.lit 1) (by simp) (by omega), hW 72 (.lit 0) (by simp) (by omega)]; rfl
      | 4, _ => rw [show wlo 4 = 88 from rfl, show whi 4 = 80 from rfl,
          hW 88 (.lit 1) (by simp) (by omega), hW 80 (.lit 0) (by simp) (by omega)]; rfl
    · rw [W_zero (by omega)]
      unfold ewRet
      rw [gr3 _ _ (hregs (.rax, .lit 1) (by simp)), gr3 _ _ (hregs (.rdx, .lit 0) (by simp))]
      rfl

end

end NativeRustcVmX64.Tables.TableWeights
