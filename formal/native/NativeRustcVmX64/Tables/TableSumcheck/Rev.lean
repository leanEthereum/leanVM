module

public import NativeRustcVmX64.Tables.TableSumcheck.Swap
public import NativeRustcVmX64.Bus.BytecodeShare.Model

/-!
# `table_sumcheck`: the challenges reversed (x86-64)

`b3` saves the commitments' and the bus's pointers at `56` to `72` and halves `n`: none to swap
(`n < 2`) goes on to `table_weights`; `b4` points RAX past the challenges, one pair (`b5`) goes to
the last swap, more (`b6`) to the loop of two pairs each (`Swap.loop`); `b8` ends it, with one more
swap where the pairs are odd (`Swap.one`). `rev`: the challenges reversed, as the model's
`Array.reverse`.
-/

namespace NativeRustcVmX64.Tables.TableSumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableSumcheck
open NativeRustcVmX64.Tables.TableTerms (at_pc addr_eq)

public section

variable [Host] {k : Nat} {a : DecArea} {s s1 : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData} {c : EW}

omit [Host] in
/-- The challenges reversed: the swaps' end. -/
theorem ch_rev {L : List EW} {d : MachineData} (hc : Ch m0 L (L.length / 2) d) :
    NativeRustcVm.EWsAt d.dmem (off (fb m0) 112) L.reverse := by
  rw [NativeRustcVm.ewsAt_iff]
  intro i hi
  rw [List.length_reverse] at hi
  have := hc i hi
  rw [rv_half hi] at this
  rw [off_add]
  exact this

/-- **The reverse** (`b3` to `b9`). -/
theorem rev (hp : Placed code k) (h : TableSumcheckPre a s heights bus m0) {xs : Array EW}
    {d : MachineData} (H : Sc a s heights m0 xs c s1 d)
    (cont : ∀ d', Kp a s1 heights m0 c d' →
      NativeRustcVm.EWsAt d'.dmem (off (fb m0) 112) xs.toList.reverse →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b10Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b3Offset)⟩ := by
  have hH := Pre.hts h
  have hn30 : nR heights ≤ 30 := foldl_max_le heights hH.1 hH.2.1
  have hsz : xs.size = nR heights :=
    NativeRustcVmX64.Bus.BytecodeShare.sumcheckPlain_size H.run
  have hL : xs.toList.length = nR heights := by rw [Array.length_toList]; exact hsz
  have fin : ∀ d', Kp a s1 heights m0 c d' → Ch m0 xs.toList (nR heights / 2) d' →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b10Offset)⟩ :=
    fun d' K hc ↦ cont d' K (ch_rev (by rw [hL]; exact hc))
  -- `b3`: the pointers saved, `n / 2`.
  have hwf : (E m0 d [] 0).WF := wf_nil h H.bd.fr.kept
  have hm : Match (E m0 d [] 0) sF d := match_body H.bd ⟨rfl, trivial⟩ trivial
  refine exec_then (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf nofun hm
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨mid3, W3, wr3, w56, w64, w72, rdx3, k3⟩ := ok_b3
  obtain ⟨hb3, hso3⟩ := blockB h H.bd hwf hm3 mid3 W3
  have hin3 := writesIn_of_mid mid3
  have K3 : Kp a s1 heights m0 c st3.data :=
    ⟨hb3, wroteW hm3 (by omega) w56 H.rbp, wroteW hm3 (by omega) w64 H.r12,
      wroteW hm3 (by omega) w72 H.r14,
      keepW hwf hm3 hin3 (o := 80) (by omega) (fun w hw _ ↦ by have := wr3 w hw; omega) H.t80,
      keep_frame hwf hm3 hin3 (o := 600) (bs := NativeRustcVm.ewBytes c)
        (by rw [NativeRustcVm.length_ewBytes]; omega)
        (fun w hw _ ↦ by have := wr3 w hw; rw [NativeRustcVm.length_ewBytes]; omega) H.cl,
      H.ts.frame (hm3.kept hwf) (fun q hq ↦ (ctx h).stack_not_t (fr_stack h hq)) hso3,
      (keeps_reg hm3 k3 (by simp)).trans H.r13, (keeps_reg hm3 k3 (by simp)).trans H.rbx⟩
  have hch : NativeRustcVm.EWsAt st3.data.dmem (off (fb m0) 112) xs.toList :=
    keep_frame hwf hm3 hin3 (o := 112) (bs := xs.toList.flatMap NativeRustcVm.ewBytes)
      (by rw [NativeRustcVm.length_ewsBytes]; omega)
      (fun w hw _ ↦ by have := wr3 w hw; omega) H.ch
  have C0 : Ch m0 xs.toList 0 st3.data := fun i hi ↦ by
    rw [rv_zero hi]
    have := NativeRustcVm.ewsAt_iff.mp hch i hi
    rwa [off_add] at this
  have r15_3 : reg st3.data .r15 = off (fb m0) 112 := (keeps_reg hm3 k3 (by simp)).trans H.r15
  have rdx_3 : reg st3.data .rdx = BitVec.ofNat 64 (nR heights / 2) := by
    refine (hm3.regs _ _ rdx3).trans ?_
    show BinOp.apply .shr .W64 (reg d .r13) (BitVec.ofNat 64 1) = _
    rw [H.r13, f_shr _ (by omega)]
  have hc3 : (SBool.cmp .eq .W64 (.bin .shr .W64 (.reg .r13) (.lit 1)) (.lit 0)).eval
      (E m0 d [] 0) = decide (nR heights / 2 = 0) := by
    show CmpOp.apply .eq .W64 (BinOp.apply .shr .W64 (reg d .r13) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 0) = _
    rw [H.r13, f_shr _ (by omega), eq_apply (by omega) (by omega)]
  simp only [PcOk] at hpc3
  rw [hc3] at hpc3
  by_cases hz : nR heights / 2 = 0
  · simp only [hz, decide_true, ↓reduceIte] at hpc3
    exact at_pc (hpc3.trans (lbl_9 hp)) (fin _ K3 (by rw [hz]; exact C0))
  simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc3
  refine at_pc (pc := Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b4Offset))
    (hpc3.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableSumcheck.b3_next))) ?_
  -- `b4`: RAX past the challenges; one pair or more.
  have hwf4 : (E m0 st3.data [] 0).WF := wf_nil h K3.bd.fr.kept
  have hm4 : Match (E m0 st3.data [] 0) sF st3.data := match_body K3.bd ⟨rfl, trivial⟩ trivial
  refine exec_then (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf4 nofun hm4
    fun st4 hm4' hpc4 ↦ ?_
  obtain ⟨mid4, mem4, rcx4, rax4, rdx4, k4⟩ := ok_b4
  obtain ⟨K4, hd4⟩ := Kp.nil h K3 hwf4 hm4' mid4 mem4 k4
  have C4 := Ch.nil C0 hd4
  have e40 : (Sym.ptr 0 40).eval (E m0 st3.data [] 0) = off (fb m0) 40 := eval_ptr0 40
  have rcx_4 : reg st4.data .rcx = BitVec.ofNat 64 (16 * nR heights) := by
    refine (hm4'.regs _ _ rcx4).trans ?_
    show BinOp.apply .shl .W64 (reg st3.data .r13) (BitVec.ofNat 64 4) = _
    rw [K3.r13, shl4]
  have rax_4 : reg st4.data .rax = off (fb m0) (112 + 16 * nR heights) := by
    refine (hm4'.regs _ _ rax4).trans ?_
    show BinOp.apply .add .W64 (BitVec.ofNat 64 72) (BinOp.apply .add .W64
      ((Sym.ptr 0 40).eval (E m0 st3.data [] 0))
      (BinOp.apply .shl .W64 (reg st3.data .r13) (BitVec.ofNat 64 4))) = _
    rw [e40, K3.r13, shl4, add_apply, add_apply, off_add, BitVec.add_comm, off_add]
    exact off_congr (by omega)
  have rdx_4 : reg st4.data .rdx = BitVec.ofNat 64 (nR heights / 2) :=
    (hm4'.regs _ _ rdx4).trans rdx_3
  have r15_4 : reg st4.data .r15 = off (fb m0) 112 := (keeps_reg hm4' k4 (by simp)).trans r15_3
  have hc4 : (SBool.not (.cmp .eq .W64 (.reg .rdx) (.lit 1))).eval (E m0 st3.data [] 0) =
      !decide (nR heights / 2 = 1) := by
    show (!CmpOp.apply .eq .W64 (reg st3.data .rdx) (BitVec.ofNat 64 1)) = _
    rw [rdx_3, eq_apply (by omega) (by omega)]
  simp only [PcOk] at hpc4
  rw [hc4] at hpc4
  by_cases h1 : nR heights / 2 = 1
  · -- `b5`: one pair.
    simp only [h1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc4
    refine at_pc (pc := Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b5Offset))
      (hpc4.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableSumcheck.b4_next))) ?_
    have hwf5 : (E m0 st4.data [] 0).WF := wf_nil h K4.bd.fr.kept
    have hm5 : Match (E m0 st4.data [] 0) sF st4.data := match_body K4.bd ⟨rfl, trivial⟩ trivial
    refine exec_then (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf5 nofun hm5
      fun st5 hm5' hpc5 ↦ ?_
    obtain ⟨mid5, mem5, rcx5, rax5, k5⟩ := ok_b5
    obtain ⟨K5, hd5⟩ := Kp.nil h K4 hwf5 hm5' mid5 mem5 k5
    simp only [PcOk] at hpc5
    exact at_pc (hpc5.trans (lbl_8 hp)) (one hp h hL (j := 0) (by omega) K5 (Ch.nil C4 hd5)
      (hm5'.regs _ _ rcx5) ((hm5'.regs _ _ rax5).trans rax_4)
      fun d' K' hc' ↦ fin d' K' (by rw [h1]; exact hc'))
  -- `b6`: the loop's start.
  simp only [h1, decide_false, Bool.not_false, ↓reduceIte] at hpc4
  refine at_pc (pc := Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b6Offset)) (hpc4.trans (lbl_5 hp)) ?_
  have hwf6 : (E m0 st4.data [] 0).WF := wf_nil h K4.bd.fr.kept
  have hm6 : Match (E m0 st4.data [] 0) sF st4.data := match_body K4.bd ⟨rfl, trivial⟩ trivial
  refine exec_then (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf6 nofun hm6
    fun st6 hm6' hpc6 ↦ ?_
  obtain ⟨mid6, mem6, rcx6, rdx6, rsi6, rdi6, rax6, k6⟩ := ok_b6
  obtain ⟨K6, hd6⟩ := Kp.nil h K4 hwf6 hm6' mid6 mem6 k6
  have hT : 4 * (nR heights / 2 / 2) ≤ nR heights := by omega
  have LR6 : LR m0 (nR heights) 0 (nR heights / 2 / 2) st6.data := by
    refine ⟨(hm6'.regs _ _ rcx6).trans rfl, ?_, ?_, (hm6'.regs _ _ rax6).trans rax_4,
      (hm6'.regs _ _ rdi6).trans rfl, ?_⟩
    · exact (keeps_reg hm6' k6 (r := .r15) (by simp)).trans r15_4
    · rw [show reg st6.data .rsi = _ from hm6'.regs _ _ rsi6]
      show BinOp.apply .add .W64 (BitVec.ofNat 64 18446744073709551600)
        (BinOp.apply .add .W64 (reg st4.data .rcx) (reg st4.data .r15)) + _ = _
      rw [rcx_4, r15_4, add_apply, add_apply]
      unfold off
      bv_omega
    · refine (hm6'.regs _ _ rdx6).trans ?_
      show BinOp.apply .and .W32 (reg st4.data .rdx) (BitVec.ofNat 64 14) = _
      rw [rdx_4, f_and _ (by omega)]
  simp only [PcOk] at hpc6
  refine at_pc (hpc6.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableSumcheck.b6_next)))
    (loop hp h hL hT (fun d8 K8 C8 R8 ↦ ?_) (nR heights / 2 / 2 - 1) 0 (by omega) st6.data K6
      (by rw [Nat.mul_zero]; exact Ch.nil C4 hd6) LR6)
  -- `b8`: one more pair where they are odd.
  have hwf8 : (E m0 d8 [] 0).WF := wf_nil h K8.bd.fr.kept
  have hm8 : Match (E m0 d8 [] 0) sF d8 := match_body K8.bd ⟨rfl, trivial⟩ trivial
  refine exec_then (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf8 nofun hm8
    fun st8 hm8' hpc8 ↦ ?_
  obtain ⟨mid8, mem8, rcx8, rax8, k8⟩ := ok_b8
  obtain ⟨K8', hd8⟩ := Kp.nil h K8 hwf8 hm8' mid8 mem8 k8
  have hc8 : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .r13) (.lit 2)) (.lit 0)).eval
      (E m0 d8 [] 0) = decide (nR heights / 2 % 2 = 0) := by
    show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg d8 .r13) (BitVec.ofNat 64 2))
      (BitVec.ofNat 64 0) = _
    rw [K8.r13, f_test _ (by omega)]
  simp only [PcOk] at hpc8
  rw [hc8] at hpc8
  by_cases he : nR heights / 2 % 2 = 0
  · simp only [he, decide_true, ↓reduceIte] at hpc8
    exact at_pc (hpc8.trans (lbl_9 hp))
      (fin _ K8' (by
        rw [show nR heights / 2 = 2 * (nR heights / 2 / 2) by omega]; exact Ch.nil C8 hd8))
  simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc8
  refine at_pc (hpc8.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableSumcheck.b8_next)))
    (one hp h hL (j := 2 * (nR heights / 2 / 2)) (by omega) K8' (Ch.nil C8 hd8)
      ((hm8'.regs _ _ rcx8).trans R8.rcx) ((hm8'.regs _ _ rax8).trans R8.rax)
      fun d' K' hc' ↦ fin d' K' (by
        rw [show nR heights / 2 = 2 * (nR heights / 2 / 2) + 1 by omega]; exact hc'))

end

end NativeRustcVmX64.Tables.TableSumcheck
