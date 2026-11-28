module

public import NativeRustcVmX64.Whir.NovelEval.Sum
public import NativeRustcVmX64.Code.Vm.Kmul.Names

/-!
# `novel_eval`: from the complete basis to the sum (x86-64)

`sum`: from `Mid` at `b9`, the products' count `min size count`; none (`b15`: the sum `0`) or
`b10` spills its bytes and starts the sum's loop (`sumTurn`, by `Sym.loop`), to `Done` at `b16`.
-/

namespace NativeRustcVmX64.Whir.NovelEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.NovelEval NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv)
open NativeRustcVmX64.Arrays (load8_eq wordAt_of_write eval_reg eval_lit eval_load eval_add
  eval_cmp_eq eval_not eval_test eval_min eval_shl_lit)

public section

variable [Host] {k : Nat}

theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b9Offset) :=
  b9_in_code.trans hp.1 (by simp [b9])
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b10Offset) :=
  b10_in_code.trans hp.1 (by simp [b10])
theorem hb15 (hp : Placed code k) : b15.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b15Offset) :=
  b15_in_code.trans hp.1 (by simp [b15])

/-- **From the complete basis to the sum.** -/
theorem sum (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hpre : NovelEvalPre m0) (hc : cnt m0 ≤ 64) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b9Offset)) (hM : Mid m0 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b16Offset) ∧ Done m0 s.data) st := by
  have hS := hpre.1
  have hF : 1104 ≤ novelEvalStack := by decide
  have hS1 := hS.1
  have hS2 := hS.2.1
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfr := hM.fr
  have hsl := slots_ok
  have hlw : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  have hblen : (basisOf m0 (wn m0)).size ≤ 64 := novelPre_size_le _ hc _
  have hpos := basis_pos m0 (wn m0)
  have hlb : ((basisOf m0 (wn m0)).toList.flatMap NativeRustcVm.wordBytes).length =
      8 * (basisOf m0 (wn m0)).size := by
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList]
  have hlen : lenOf m0 = min (basisOf m0 (wn m0)).size (cnt m0) := rfl
  -- `b9`: the count
  refine exec_at (hb9 hp) run_b9 (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hfr.of_block (match_nil _) hm1 (Env.wf_nil _) rfl (after_eq run_b9 ▸ b9_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have hmin : (Sym.ite (.cmp .ult .W64 (.reg .rbp) (.reg .r14)) (.reg .rbp) (.reg .r14)).eval
      (Env.ofMachine st.data []) = BitVec.ofNat 64 (lenOf m0) := by
    rw [eval_min, Env.ofMachine_regs, Env.ofMachine_regs]
    show BitVec.ofNat 64 (min (reg st.data .r14).toNat (reg st.data .rbp).toNat) = _
    rw [hM.r14, hM.rbp, hlen, Nat.min_comm]
    rfl
  have hr141 : reg st1.data .r14 = BitVec.ofNat 64 (lenOf m0) := (hm1.regs .r14 _ rfl).trans hmin
  have e1 : ∀ r ∈ [Reg64.rbx, .r15], reg st1.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Match.reg_eq (match_nil _) hm1 rfl rfl
  simp only [PcOk] at hpc1
  rw [eval_test, hmin, ofNat_beq (by omega) (by omega)] at hpc1
  obtain ⟨hT, hF1⟩ := Arrays.pc_cond hpc1
  by_cases h0 : lenOf m0 = 0
  · -- `b15`: no product
    have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b15Offset) :=
      (hT (by rw [decide_eq_true_eq]; exact h0)).trans (hp.label NativeRustcVmX64.Vm.NovelEval.label_8_at)
    refine exec_at (hb15 hp) run_b15 (Env.wf_nil _) (by intro l h; cases h) hpc1' (match_nil _)
      fun st2 hm2 hpc2 ↦ .done _ ⟨hpc2, ?_⟩
    have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq (Env.wf_nil _) rfl
    refine ⟨hfr1.of_block (match_nil _) hm2 (Env.wf_nil _) rfl (after_eq run_b15 ▸ b15_keeps),
      ⟨by rw [hd2, hd1]; exact hM.sp.out, by rw [hd2, hd1]; exact hM.sp.cs⟩, ?_, ?_⟩
    · rw [h0, acc_zero]; exact (hm2.regs .r14 _ rfl).trans rfl
    · rw [h0, acc_zero]; exact (hm2.regs .rbx _ rfl).trans rfl
  · -- `b10`: the sum's count, its loop
    have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b10Offset) := hF1 (by rw [decide_eq_true_eq]; exact h0)
    have hwf2 := hfr1.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
    refine exec_at (hb10 hp) run_b10 hwf2 (by intro l h; cases h) hpc1' hfr1.mid_match
      fun st2 hm2 hpc2 ↦ ?_
    obtain ⟨hk2, hw2, hv2⟩ := after_eq run_b10 ▸ b10_write
    have hfr2 : NFrame m0 st2.data := hfr1.of_write hfr1.mid_match hm2 hwf2 rfl hk2 (r := 0) rfl
      (len := 16) (by omega) (fun w hw ↦ ⟨(hw2 w hw).1, (hw2 w hw).2.2⟩)
      (fun p h ↦ .inr (inRange_frame hS hF (by omega) h))
      (fun q hq i hi ↦ by
        rw [addr_add]
        exact Arrays.not_inRange_above (by have := hsl q hq; omega)
          (by rw [hfe]; have := hsl q hq; omega))
    have k2 : ∀ {o : Nat} {bs : List UInt8}, 16 ≤ o → o + bs.length ≤ 1112 →
        NativeRustcVm.BytesAt st1.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
        NativeRustcVm.BytesAt st2.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
      fun h16 hl h ↦ bytesAt_block hm2 hwf2 rfl hl
        (fun w hw ↦ ⟨(hw2 w hw).1, .inl (by have := (hw2 w hw).2.2; omega)⟩) h
    have hlen2 : WordAt st2.data.dmem (fbOf m0 + BitVec.ofNat 64 8) (.ofNat (8 * lenOf m0)) := by
      have := wordAt_of_write hm2 (r := 0) (o := 8) rfl (by decide)
        (v := .bin .shl .W64 (.reg .r14) (.lit 3)) hv2
      rwa [eval_shl_lit _ (by decide), eval_reg, Env.ofMachine_regs,
        show st1.data.regs.get64 .r14 = _ from hr141, shl3 (by omega)] at this
    have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b11Offset) := hpc2
    have hI0 : SInv m0 0 st2.data := by
      refine ⟨hfr2, ⟨k2 (by omega) (by rw [hlw]; omega) (hd1 ▸ hM.sp.out),
        k2 (by omega) (by rw [hlw]; omega) (hd1 ▸ hM.sp.cs)⟩, hlen2, by omega, ?_, ?_, ?_,
        k2 (by omega) (by rw [hlb]; omega) (hd1 ▸ hM.basis)⟩
      · exact (hm2.regs .r15 _ rfl).trans rfl
      · rw [acc_zero]; exact (hm2.regs .r14 _ rfl).trans rfl
      · rw [acc_zero]; exact (hm2.regs .rbx _ rfl).trans rfl
    refine Sym.loop (fun n s ↦ ∃ t, n = lenOf m0 - t ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b11Offset) ∧
      SInv m0 t s.data) (fun n s ⟨t, hn, hpc, hI⟩ ↦ ?_) ⟨0, rfl, hpc2', hI0⟩
    have ht := hI.ht
    refine (sumTurn hp hkmul hpre hc hpc hI).mono fun s' h ↦ ?_
    rcases h with ⟨hpc', hI'⟩ | h
    · exact .inr ⟨lenOf m0 - (t + 1), by omega, t + 1, rfl, hpc', hI'⟩
    · exact .inl h

end

end NativeRustcVmX64.Whir.NovelEval
