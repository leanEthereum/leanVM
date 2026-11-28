module

public import NativeRustcVmX64.Whir.SampleQueries.Fin
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names

/-!
# `sample_queries` on x86-64: the outer loop's end, the squeezes' loop

`b9_step`: after a challenge's positions (`AtB9`, `b9`), back at the outer loop's head (`Outer`)
or, after the last challenge, the return (`fin`). `big_step`: a depth above `128` asks for no
position, each challenge a squeeze (`b4`, `b5`, `Big`), then the return.
-/

namespace NativeRustcVmX64.Whir.SampleQueries

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.SampleQueries
open NativeRustcVmX64.Transcript (Frame frameEnv)
open NativeRustcVmX64.Arrays (pc_cond)
open NativeRustcVm (BufWordsAt WordsAt WordAt)

public section

theorem toNat_add1 {x : BitVec 64} {n : Nat} (h : x.toNat = n) (hn : n + 1 < 2 ^ 64) :
    (x + BitVec.ofNat 64 1).toNat = n + 1 := by
  rw [BitVec.toNat_add, h, BitVec.toNat_ofNat]
  omega

theorem toNat_sub1 {x : BitVec 64} {n : Nat} (h : x.toNat = n) (hn : 1 ≤ n) :
    (x - BitVec.ofNat 64 1).toNat = n - 1 := by
  rw [BitVec.toNat_sub, h, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem toNat_subx {x y : BitVec 64} {r n : Nat} (hx : x.toNat = r) (hy : y.toNat = n) (h : n ≤ r) :
    (x - y).toNat = r - n := by
  rw [BitVec.toNat_sub, hx, hy]
  have := x.isLt
  omega

theorem beq_of_toNat {x y : BitVec 64} : (x == y) = decide (x.toNat = y.toNat) := by
  by_cases h : x = y
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr h]
    exact (decide_eq_false fun h' ↦ h (BitVec.eq_of_toNat_eq h')).symm

theorem bufWords_nil {d : DataMem} {p : BitVec 64} (h : WordAt d p 0) : BufWordsAt d p queryCap [] :=
  ⟨by decide, h, NativeRustcVm.wordsAt_nil _ _⟩

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- **`b9`**: the challenge counted; the outer loop goes on, or returns after the last. -/
theorem b9_step (hp : Placed code k) (h : SampleQueriesPre a s0 m0) {j r n : Nat} {s : TState}
    {qs : List UInt64} {st : MachineData} (hA : AtB9 a s0 m0 j r n s qs st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post a s0 m0 st' ∨ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b10Offset) ∧
      Outer a s0 m0 (j + 1) (r - n) s qs st'.data)) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b9Offset)⟩ := by
  have hwf := mid_wf (vars := fun _ ↦ 0) (ret := 0) h hA.ctx.fr.kept
  have hcnt := pre_cnt h
  have hj := hA.jlt
  refine exec_then (inf hp b9_in_code (by simp [b9])) run_b9 hwf (by intro l h; cases h)
    (mid_match hA.ctx.fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hmem, h15, hax, hk⟩ := after_eq run_b9 ▸ ok_b9
  have hc1 := hA.ctx.block h hm1 (L := 0) (by omega) hmid (wr0_nil hmem 0) (kept_spec hk (by simp))
  have hd1 : st1.data.dmem = st.dmem := hm1.dmem_eq hwf hmem
  have hr15 : (reg st1.data .r15).toNat = j + 1 := by
    rw [show reg st1.data .r15 = _ from hm1.regs .r15 _ h15]
    exact toNat_add1 hA.r15 (by omega)
  simp only [PcOk] at hpc1
  have hc : (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .r15) (.lit 1)) (.reg .r14)).eval
      (frameEnv m0 st 128 []) = decide (j + 1 = cnt m0) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
    rw [beq_of_toNat]
    show decide ((reg st .r15 + BitVec.ofNat 64 1).toNat = (reg st .r14).toNat) = _
    rw [toNat_add1 hA.r15 (by omega), hA.r14]
  rw [hc] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  have hc1' := hc1
  have hts1 : TStateAt st1.data.dmem (tA m0) a s := hd1 ▸ hA.ts
  have hbuf1 : BufWordsAt st1.data.dmem (oA m0) queryCap qs := hd1 ▸ hA.buf
  by_cases hlast : j + 1 = cnt m0
  · have hpc := (hT (decide_eq_true hlast)).trans (hp.label NativeRustcVmX64.Vm.SampleQueries.label_12_at)
    refine Eventually.mono (at_pc (fin hp h (qs := qs) (s' := s) ⟨hc1, hts1, hbuf1, ?_⟩) rfl hpc)
      fun _ h ↦ .inl h
    rw [hA.model, show cnt m0 - (j + 1) = 0 by omega, auxP_zero_left]
    simp
  · have hpc := hF fun h ↦ hlast (of_decide_eq_true h)
    refine .done _ (.inr ⟨hpc, ⟨hc1', ?_, ?_, ?_, hr15, ?_, ?_, ?_, by omega, hA.len,
      hA.dlt, hts1, hbuf1, hA.model⟩⟩)
    · rw [hd1]; exact hA.tw
    · rw [show reg st1.data .rax = _ from hm1.regs .rax _ hax]
      exact toNat_subx hA.rax hA.rcx hA.nle
    · exact (reg_kept hm1 (kept_spec hk (by simp))).trans hA.rbx
    · exact (congrArg BitVec.toNat (reg_kept hm1 (kept_spec hk (by simp)))).trans hA.r14
    · exact (reg_kept hm1 (kept_spec hk (by simp))).trans hA.r12
    · exact (congrArg BitVec.toNat (reg_kept hm1 (kept_spec hk (by simp)))).trans
        (by rw [hA.rbp])

/-- **The squeezes' loop** (`b4`, `b5`, a depth above `128`): a challenge squeezed; the loop goes
on, or returns after the last. -/
theorem big_step (hp : Placed code k) (h : SampleQueriesPre a s0 m0)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp)) {j : Nat}
    {s : TState} {st : MachineData} (hB : Big a s0 m0 j s st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post a s0 m0 st' ∨ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b4Offset) ∧
      Big a s0 m0 (j + 1) (sq s).2 st'.data)) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b4Offset)⟩ := by
  have hj := hB.jlt
  have hcnt := pre_cnt h
  have hwf := mid_wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b4Offset + b4.length)).toBitVec) h
    hB.ctx.fr.kept
  refine exec_then (inf hp b4_in_code (by simp [b4])) run_b4 hwf (fun _ _ ↦ rfl)
    (mid_match hB.ctx.fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw, hdi, hk⟩ := after_eq run_b4 ▸ ok_b4
  have hs1 := block_same hwf hm1 (by omega) hw
  have hbuf1 : WordAt st1.data.dmem (oA m0) 0 :=
    wordAt0_keep h hB.buf hs1 fun q hq ↦ frame_not_o h (Transcript.inRange_mono hq (by omega))
  refine squeeze_call h hsq hB.ctx hB.ts hm1 hmid (by omega) hw (kept_spec hk (by simp))
    ((hm1.regs .rdi _ hdi).trans hB.rbx) hpc1 fun st2 hpc2 hc2 hts2 _ _ hcs2 _ hso2 ↦ ?_
  have hbuf2 : WordAt st2.data.dmem (oA m0) 0 :=
    wordAt0_keep h hbuf1 hso2 fun q hq ↦ by
      rcases hq with hq | hq
      · exact fun ho ↦ (o_not_t h ho).1 hq
      · exact stack_not_o h hq
  have hr14 : (reg st2.data .r14).toNat = cnt m0 - j :=
    (congrArg BitVec.toNat ((hcs2 .r14 rfl).trans (reg_kept hm1 (kept_spec hk (by simp))))).trans
      hB.r14
  have hrbx : reg st2.data .rbx = tA m0 :=
    (hcs2 .rbx rfl).trans ((reg_kept hm1 (kept_spec hk (by simp))).trans hB.rbx)
  have hwf2 := mid_wf (vars := fun _ ↦ 0) (ret := 0) h hc2.fr.kept
  refine exec_at (inf hp b5_in_code (by simp [b5])) run_b5 hwf2 (by intro l h; cases h)
    (hpc2.trans rfl) (mid_match hc2.fr) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, h14, hk3⟩ := after_eq run_b5 ▸ ok_b5
  have hc3 := hc2.block h hm3 (L := 0) (by omega) hmid3 (wr0_nil hmem3 0) (kept_spec hk3 (by simp))
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hdg : 128 / dep m0 = 0 := Nat.div_eq_of_lt (by have := hB.dge; omega)
  have hstep : auxP (dep m0) (cnt m0 - j) (cnt m0) s =
      auxP (dep m0) (cnt m0 - (j + 1)) (cnt m0) (sq s).2 := by
    rw [show cnt m0 - j = cnt m0 - (j + 1) + 1 by omega, auxP_big hdg _ _ _ (by omega)]
  simp only [PcOk] at hpc3
  have hc : (SBool.not (.cmp .eq .W64 (.bin .sub .W64 (.reg .r14) (.lit 1)) (.lit 0))).eval
      (frameEnv m0 st2.data 128 []) = decide (j + 1 ≠ cnt m0) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
    rw [beq_of_toNat]
    show (!decide ((reg st2.data .r14 - BitVec.ofNat 64 1).toNat = (BitVec.ofNat 64 0).toNat)) = _
    rw [toNat_sub1 hr14 (by omega)]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    by_cases hh : j + 1 = cnt m0 <;> simp [hh] <;> omega
  rw [hc] at hpc3
  obtain ⟨hT, hF⟩ := pc_cond hpc3
  by_cases hlast : j + 1 = cnt m0
  · have hpc := hF (by simp [hlast])
    refine Eventually.mono (at_pc (fin hp h (qs := []) (s' := (sq s).2)
      ⟨hc3, hd3 ▸ hts2, bufWords_nil (hd3 ▸ hbuf2), ?_⟩) rfl hpc) fun _ h ↦ .inl h
    rw [hB.model, hstep, show cnt m0 - (j + 1) = 0 by omega, auxP_zero_left]
  · have hpc := (hT (by simp [hlast])).trans (hp.label NativeRustcVmX64.Vm.SampleQueries.label_11_at)
    refine .done _ (.inr ⟨hpc, ⟨hc3, ?_, ?_, by omega, hB.dge, hd3 ▸ hts2, hd3 ▸ hbuf2,
      hB.model.trans hstep⟩⟩)
    · exact (reg_kept hm3 (kept_spec hk3 (by simp))).trans hrbx
    · rw [show reg st3.data .r14 = _ from hm3.regs .r14 _ h14]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
      show (reg st2.data .r14 - BitVec.ofNat 64 1).toNat = _
      rw [toNat_sub1 hr14 (by omega)]
      omega

end

end NativeRustcVmX64.Whir.SampleQueries
