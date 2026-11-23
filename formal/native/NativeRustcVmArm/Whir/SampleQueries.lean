module

public import NativeRustcVmArm.Code.Vm.QueryBits.Names
public import NativeRustcVmArm.Code.Vm.SampleQueries.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Whir.SampleQueries.Loops

/-!
# `sample_queries`'s contract

`b0` clears the output's count word; no position (`b6`) returns at once; else the prologue (`b1`)
and, for a depth above `128`, the squeezes' loop (`big_run`), else `b2` and the outer loop
(`outer_run`).
-/

namespace NativeRustcVmArm.Whir.SampleQueries

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.SampleQueries
open NativeRustcVm (BufWordsAt WordsAt WordAt)

public section

variable [Host] {a : DecArea} {s0 : TState} {m0 : MachineData} {k : Nat}

theorem entry_match (h : SampleQueriesPre a s0 m0) : Match (entryEnv m0) entryS m0 := by
  have hN := pre_N h
  refine match_ofMachine ⟨rfl, fun _ ↦ frame_aligned (pre_stack h) (by decide) rfl, rfl,
    fun h ↦ absurd h (by decide), trivial⟩ ?_ ⟨?_, trivial⟩ trivial trivial trivial
  · simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some]
    rw [show BitVec.ofInt 64 112 = BitVec.ofNat 64 112 from rfl, base_add_eq]
  · simp [Sym.eval, oA]; rfl

/-- The entry's writes: the frame and the count word. -/
theorem entry_written (h : SampleQueriesPre a s0 m0) {S : SState}
    (hS : ∀ w ∈ S.mem, (w.r = 0 ∧ w.off + w.n ≤ 112) ∨ (w.r = 1 ∧ w.off + w.n ≤ 8))
    {q : BitVec 64} (hq : Written (entryEnv m0) S q) :
    InRange (base m0 112) 112 q ∨ InRange (oA m0) 8 q := by
  obtain ⟨w, hw, b, sz, hb, hin⟩ := written_inRange (entry_wf h) (fun w hw b sz hb ↦ by
    rcases hS w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩ <;> rw [hr] at hb <;> simp at hb <;> omega) hq
  rcases hS w hw with ⟨hr, -⟩ | ⟨hr, -⟩ <;> rw [hr] at hb <;> simp at hb <;>
    obtain ⟨rfl, rfl⟩ := hb
  · exact Or.inl hin
  · exact Or.inr hin

theorem entry_out (h : SampleQueriesPre a s0 m0) {q : BitVec 64}
    (hq : InRange (base m0 112) 112 q ∨ InRange (oA m0) 8 q) :
    (¬InRange (tA m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q) ∧
      (InRange (stackBelow m0 sampleQueriesStack) sampleQueriesStack q ∨ outs m0 q) := by
  obtain ⟨⟨hmo, hno, hot, hod, hos, hor⟩, -⟩ := h.2.2.2
  have hfp := h.2.1.footprint
  have hnt : NativeRustcVm.NoWrap (tA m0) tstateBytes := hfp.1.2
  have hnd : NativeRustcVm.NoWrap a.words (8 * a.len) := hfp.2.1.2
  have hno' : NativeRustcVm.NoWrap (oA m0) queryBufBytes := hno
  rcases hq with hq | hq
  · exact ⟨frame_not_t h hq, Or.inl (in_stack h hq)⟩
  · have ho : InRange (oA m0) queryBufBytes q :=
      NativeRustcVm.InRange.mono hq (hno'.mono (by decide)) hno' (Nat.le_refl _)
        (Nat.add_le_add_left (by decide) _)
    exact ⟨⟨fun ht ↦ NativeRustcVm.Apart.not_inRange hot hno' hnt ho ht,
      fun hd ↦ NativeRustcVm.Apart.not_inRange hod hno' hnd ho hd⟩, Or.inr (Or.inl ho)⟩

/-- **`sample_queries`'s contract.** -/
theorem sampleQueries_spec (hp : Placed code k)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hqb : Spec (Labels.label NativeRustcVmArm.Vm.QueryBits.entryLabel) QueryBitsPre QueryBitsPost) (a : DecArea)
    (s0 : TState) :
    Spec (Labels.label NativeRustcVmArm.Vm.SampleQueries.entryLabel) (SampleQueriesPre a s0) (SampleQueriesPost a s0) := by
  intro m0 h
  rw [show Labels.label NativeRustcVmArm.Vm.SampleQueries.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.SampleQueries.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.SampleQueries.entryOffset) NativeRustcVmArm.Vm.SampleQueries.entry_at]
  have hwf := entry_wf h
  have hm := entry_match h
  have hc := cnt_le h
  refine exec_then (inf hp b0_in_code (by simp [b0])) run_b0 hwf hm fun st0 hm0 hpc0 ↦ ?_
  simp only [PcOk] at hpc0
  have hcond0 : (SBool.cmp CmpOp.eq RegWidth.W64 (Sym.reg XReg.X2) (Sym.lit 0)).eval
      (entryEnv m0) = decide (cnt m0 = 0) := by
    sym_simp
    simp only [Env.ofMachine_regs]
    exact bv_beq _ (by decide)
  rw [hcond0] at hpc0
  by_cases hc0 : cnt m0 = 0
  · -- no position: `b6`
    simp only [hc0, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.SampleQueries.b6Offset) NativeRustcVmArm.Vm.SampleQueries.label_5_at] at hpc0
    refine exec_at (inf hp b6_in_code (by simp [b6])) (exec_after run_b0 run_b6) hwf hpc0 hm0
      fun st hm' hpc' ↦ ?_
    simp only [PcOk] at hpc'
    have hS : ∀ w ∈ (after b6 (after b0 entryS)).mem,
        (w.r = 0 ∧ w.off + w.n ≤ 112) ∨ (w.r = 1 ∧ w.off + w.n ≤ 8) := by
      rw [after_eq run_b6]; decide
    rw [after_eq run_b6] at hS
    have hs : SameOutside m0.dmem st.data.dmem
        (fun q ↦ InRange (base m0 112) 112 q ∨ InRange (oA m0) 8 q) :=
      NativeRustcVm.SameOutside.mono (hm'.sameOutside hwf) fun q hq ↦ entry_written h hS hq
    have h30 : st.data.regs.X30 = m0.regs.X30 := Match.reg_eq (r := .X30) hm hm' rfl rfl
    refine .done _ ⟨by rw [hpc']; simp only [retOf, h30], ?_, ⟨#[], s0, ?_, ?_, ?_⟩, ?_,
      Match.saved hm hm' hwf rfl (by decide)⟩
    · exact reg_of hm' (r := .X0) rfl rfl
    · rw [sampleQueries_run, show m0.regs.X2.toNat = 0 from hc0, auxP_zero_left]
    · have hw := hm'.bytesAt_write (r := 1) (o := 0) (n := 8) (b := oA m0) (sz := 8) rfl
        (by decide) (v := .lit 0) (by decide)
      rw [wordBytes_reg, NativeRustcVm.addr_add_zero] at hw
      exact ⟨Nat.zero_le _, hw, NativeRustcVm.wordsAt_nil _ _⟩
    · exact h.2.1.frame (hm'.kept hwf) (fun q hq ↦ (entry_out h hq).1) hs
    · exact NativeRustcVm.SameOutside.mono hs fun q hq ↦ by
        rcases (entry_out h hq).2 with hq | hq | hq
        · exact Or.inr hq
        · exact Or.inl ⟨_, List.mem_cons_self, hq⟩
        · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩
  · -- the prologue: `b1`
    simp only [hc0, decide_false, Bool.false_eq_true, ↓reduceIte,
      show k + NativeRustcVmArm.Vm.SampleQueries.b0Offset + b0.length = k + NativeRustcVmArm.Vm.SampleQueries.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SampleQueries.b0_next]] at hpc0
    refine exec_at (inf hp b1_in_code (by simp [b1])) (exec_after run_b0 run_b1) hwf hpc0 hm0
      fun st1 hm1 hpc1 ↦ ?_
    simp only [PcOk] at hpc1
    have hS : ∀ w ∈ (after b1 (after b0 entryS)).mem,
        (w.r = 0 ∧ w.off + w.n ≤ 112) ∨ (w.r = 1 ∧ w.off + w.n ≤ 8) := by
      rw [after_eq run_b1]; decide
    rw [after_eq run_b1] at hS
    have hf1 : SFr m0 st1.data := fr_entry h hm1 rfl (by decide) hS
    have hs : SameOutside m0.dmem st1.data.dmem
        (fun q ↦ InRange (base m0 112) 112 q ∨ InRange (oA m0) 8 q) :=
      NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf) fun q hq ↦ entry_written h hS hq
    have hts1 : TStateAt st1.data.dmem (tA m0) a s0 :=
      h.2.1.frame (hm1.kept hwf) (fun q hq ↦ (entry_out h hq).1) hs
    have hw := hm1.bytesAt_write (r := 1) (o := 0) (n := 8) (b := oA m0) (sz := 8) rfl
      (by decide) (v := .lit 0) (by decide)
    rw [wordBytes_reg, NativeRustcVm.addr_add_zero] at hw
    have hw0 : WordAt st1.data.dmem (oA m0) 0 := hw
    have h19 : st1.data.regs.X19 = m0.regs.X2 := reg_of hm1 (r := .X19) (v := .reg .X2) rfl rfl
    have h20 : st1.data.regs.X20 = m0.regs.X0 := reg_of hm1 (r := .X20) (v := .reg .X0) rfl rfl
    have h22 : st1.data.regs.X22 = m0.regs.X1 := reg_of hm1 (r := .X22) (v := .reg .X1) rfl rfl
    have h3 : st1.data.regs.X3 = m0.regs.X3 := reg_of hm1 (r := .X3) (v := .ptr 1 0) rfl
      (by simp [Sym.eval, oA])
    have hcond1 : (SBool.cmp CmpOp.ult RegWidth.W64 (Sym.reg XReg.X1) (Sym.lit 129)).not.eval
        (entryEnv m0) = decide (128 < dep m0) := by
      sym_simp
      simp only [Env.ofMachine_regs]
      rw [bv_ult _ (by decide), show (m0.regs.getXReg .X1).toNat = dep m0 from rfl]
      by_cases hd : 128 < dep m0
      · simp only [hd, decide_true]; simp; omega
      · simp only [hd, decide_false]; simp; omega
    rw [hcond1] at hpc1
    by_cases hd : 128 < dep m0
    · -- the squeezes' loop
      simp only [hd, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.SampleQueries.b3Offset) NativeRustcVmArm.Vm.SampleQueries.label_3_at] at hpc1
      refine big_run hp h hsq hd (j := 0) (s := s0) rfl hpc1 {
        fr := hf1
        x19 := by rw [h19]; rfl
        x20 := h20
        jlt := by omega
        ts := hts1
        buf := hw0
        model := rfl }
    · -- the outer loop
      simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte,
        show k + NativeRustcVmArm.Vm.SampleQueries.b1Offset + b1.length = k + NativeRustcVmArm.Vm.SampleQueries.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SampleQueries.b1_next]] at hpc1
      refine hf1.regsBlock (inf hp b2_in_code (by simp [b2])) run_b2 hpc1 rfl rfl (by rfl)
        fun st2 hf2 hd2 hm2 hpc2 ↦ ?_
      simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.SampleQueries.b9Offset) NativeRustcVmArm.Vm.SampleQueries.label_8_at] at hpc2
      refine outer_run hp h hsq hqb ⟨0, cnt m0, s0, [], rfl, hpc2, {
        fr := hf2
        x19 := (reg_of hm2 (r := .X19) (v := .reg .X19) rfl rfl).trans h19
        x20 := (reg_of hm2 (r := .X20) (v := .reg .X20) rfl rfl).trans h20
        x21 := (reg_of hm2 (r := .X21) (v := .reg .X3) rfl rfl).trans h3
        x22 := (reg_of hm2 (r := .X22) (v := .reg .X22) rfl rfl).trans h22
        x25 := by
          show (st2.data.regs.getXReg .X25).toNat = 0
          rw [reg_of hm2 (r := .X25) (v := .lit 0) rfl rfl]; rfl
        x26 := reg_of hm2 (r := .X26) (v := .lit 230) rfl rfl
        x27 := reg_val hm2 (r := .X27) rfl
        x28 := by
          show (st2.data.regs.getXReg .X28).toNat = 0
          rw [reg_of hm2 (r := .X28) (v := .lit 0) rfl rfl]; rfl
        x29 := by
          show (st2.data.regs.getXReg .X29).toNat = m0.regs.X2.toNat
          rw [reg_of hm2 (r := .X29) (v := .reg .X19) rfl rfl]
          exact congrArg UInt64.toNat h19
        jlt := by omega
        len := by simp
        dlt := by omega
        ts := by rw [hd2]; exact hts1
        buf := by rw [hd2]; exact ⟨Nat.zero_le _, hw0, NativeRustcVm.wordsAt_nil _ _⟩
        model := by simp }⟩

end

end NativeRustcVmArm.Whir.SampleQueries
