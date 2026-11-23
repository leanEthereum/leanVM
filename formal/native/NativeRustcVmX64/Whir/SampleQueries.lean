module

public import NativeRustcVmX64.Whir.SampleQueries.Entry
public import NativeRustcVmX64.Code.Vm.QueryBits.Names
public import NativeRustcVmX64.Code.Vm.SampleQueries.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names

/-!
# `sample_queries` on x86-64

**`sampleQueries_spec`**: rustc's `sample_queries`, placed anywhere in the program, meets
`SampleQueriesPre`/`SampleQueriesPost` given `squeeze`'s and `query_bits`' contracts. The entry
(`Entry`) clears the buffer's count; an empty count returns at once; a depth above `128` squeezes
`count` challenges (`Big`, `big_step`); else the outer loop (`Outer`, `outer_step`, `b12_step`)
squeezes a challenge and pushes its `n = min(r, 128 / depth)` positions (`b13_step`, the inner
loop `inner_call`, `b16_step`; `exit_step`, `b9_step`) until the count or the challenges are
done. The positions and the transcript's state are `auxP`'s (`NativeRustcVm.Whir.Sample`), the
model's `sampleQueries`.
-/

namespace NativeRustcVmX64.Whir.SampleQueries

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.SampleQueries
open NativeRustcVmX64.Transcript (Frame frameEnv)
open NativeRustcVmX64.Arrays (pc_cond)

public section

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- **The inner loop**, from its head after `i` positions, to `b17`. -/
theorem inner_run (hp : Placed code k) (h : SampleQueriesPre a s0 m0)
    (hqb : Spec (Labels.label NativeRustcVmX64.Vm.QueryBits.entryLabel) QueryBitsPre QueryBitsPost) {j r : Nat} {s : TState}
    {qs : List UInt64} {i : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b14Offset))
    (hI : Inner a s0 m0 j r s qs i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b17Offset) ∧
      AtB17 a s0 m0 j r s qs st'.data) st := by
  refine Sym.loop (I := fun n st ↦ ∃ i, n = nOf m0 r - i ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b14Offset) ∧
      Inner a s0 m0 j r s qs i st.data) (fun n st ⟨i, hn, hpc, hI⟩ ↦ ?_) ⟨i, rfl, hpc, hI⟩
  have hilt := hI.ilt
  refine Eventually.bind (at_pc (inner_call hp h hqb hI) rfl hpc) fun st1 ⟨hpc1, hB⟩ ↦ ?_
  refine Eventually.mono (at_pc (b16_step hp h hB) rfl hpc1) fun st2 h2 ↦ ?_
  rcases h2 with ⟨hpc2, hI2⟩ | h2
  · exact .inr ⟨nOf m0 r - (i + 1), by omega, i + 1, rfl, hpc2, hI2⟩
  · exact .inl h2

/-- **A turn of the outer loop**: from its head, the return or the head after one more
challenge. -/
theorem outer_turn (hp : Placed code k) (h : SampleQueriesPre a s0 m0)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hqb : Spec (Labels.label NativeRustcVmX64.Vm.QueryBits.entryLabel) QueryBitsPre QueryBitsPost) {j r : Nat} {s : TState}
    {qs : List UInt64} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b10Offset))
    (hO : Outer a s0 m0 j r s qs st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post a s0 m0 st' ∨ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b10Offset) ∧
      ∃ r' s' qs', Outer a s0 m0 (j + 1) r' s' qs' st'.data)) st := by
  have hb9 : ∀ {n : Nat} {qs' : List UInt64} {st' : MachineState},
      st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b9Offset) → AtB9 a s0 m0 j r n (sq s).2 qs' st'.data →
      Eventually (step1 Host.exe) (fun st' ↦ Post a s0 m0 st' ∨ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b10Offset) ∧
        ∃ r' s' qs', Outer a s0 m0 (j + 1) r' s' qs' st'.data)) st' := fun hpc' hA ↦
    Eventually.mono (at_pc (b9_step hp h hA) rfl hpc') fun _ h ↦ h.elim .inl
      fun ⟨hp', hO'⟩ ↦ .inr ⟨hp', _, _, _, hO'⟩
  refine Eventually.bind (at_pc (outer_step hp h hsq hO) rfl hpc) fun st1 h1 ↦ ?_
  rcases h1 with h1 | ⟨hpc1, hB⟩
  · exact .done _ (.inl h1)
  refine Eventually.bind (at_pc (b12_step hp h hB) rfl hpc1) fun st2 h2 ↦ ?_
  rcases h2 with ⟨hpc2, hA⟩ | ⟨hpc2, hB13⟩
  · exact hb9 hpc2 hA
  refine Eventually.bind (at_pc (b13_step hp h hB13) rfl hpc2) fun st3 ⟨hpc3, hI⟩ ↦ ?_
  refine Eventually.bind (inner_run hp h hqb hpc3 hI) fun st4 ⟨hpc4, hB17⟩ ↦ ?_
  refine Eventually.bind (at_pc (exit_step hp h hB17) rfl hpc4) fun st5 ⟨hpc5, hA⟩ ↦ ?_
  exact hb9 hpc5 hA

/-- **`sample_queries` meets its contract.** -/
theorem sampleQueries_spec (hp : Placed code k)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hqb : Spec (Labels.label NativeRustcVmX64.Vm.QueryBits.entryLabel) QueryBitsPre QueryBitsPost) (a : DecArea)
    (s : TState) :
    Spec (Labels.label NativeRustcVmX64.Vm.SampleQueries.entryLabel) (SampleQueriesPre a s) (SampleQueriesPost a s) := by
  intro m0 h
  rw [show Labels.label NativeRustcVmX64.Vm.SampleQueries.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b0Offset) from hp.label NativeRustcVmX64.Vm.SampleQueries.entry_at]
  have hwf := entry_wf h
  have hx : ∀ r, (entryEnv m0).regs r = reg m0 r := fun _ ↦ rfl
  refine exec_then (inf hp b0_in_code (by simp [b0])) run_b0 hwf (by intro l h; cases h)
    entry_match fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hc : (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rdx) (.reg .rdx)) (.lit 0)).eval
      (entryEnv m0) = decide (cnt m0 = 0) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.and_self]
    rw [beq_of_toNat, hx]
    simp
  rw [hc] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases h0 : cnt m0 = 0
  · have hpc := (hT (decide_eq_true h0)).trans (hp.label NativeRustcVmX64.Vm.SampleQueries.label_13_at)
    refine exec_at (inf hp b19_in_code (by simp [b19])) (exec_after run_b0 run_b19z) hwf
      (by intro l h; cases h) hpc hm1 fun st2 hm2 hpc2 ↦ .done _ ?_
    rw [← after_eq run_b19z] at hm2
    exact ret0 h h0 hm2 hpc2
  have hpc := hF fun h ↦ h0 (of_decide_eq_true h)
  refine exec_at (inf hp b1_in_code (by simp [b1])) (exec_after run_b0 run_b1) hwf
    (by intro l h; cases h) (hpc.trans rfl) hm1 fun st2 hm2 hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  have hc2 : (SBool.not (.cmp .ult .W64 (.reg .rsi) (.lit 129))).eval (entryEnv m0) =
      decide (129 ≤ dep m0) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hx, BitVec.ult, BitVec.toNat_ofNat]
    have hd' : dep m0 = (reg m0 .rsi).toNat := rfl
    by_cases hh : 129 ≤ dep m0
    · simp [hh]
    · simp [hh]; omega
  rw [hc2] at hpc2
  obtain ⟨hT2, hF2⟩ := pc_cond hpc2
  by_cases hd : 129 ≤ dep m0
  · -- the squeezes' loop
    have hpc := (hT2 (decide_eq_true hd)).trans (hp.label NativeRustcVmX64.Vm.SampleQueries.label_11_at)
    have hB : Big a s m0 0 s st2.data := by
      refine big0 h h0 hd ?_
      show Match _ (after b1 S0) _
      rw [after_eq run_b1]
      exact hm2
    refine Sym.loop (I := fun n st ↦ ∃ j s', n = cnt m0 - j ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b4Offset) ∧
        Big a s m0 j s' st.data) (fun n st ⟨j, s', hn, hpc, hB⟩ ↦ ?_) ⟨0, s, rfl, hpc, hB⟩
    have hj := hB.jlt
    refine Eventually.mono (at_pc (big_step hp h hsq hB) rfl hpc) fun st' h' ↦ ?_
    rcases h' with h' | ⟨hpc', hB'⟩
    · exact .inl h'
    · exact .inr ⟨cnt m0 - (j + 1), by omega, j + 1, _, rfl, hpc', hB'⟩
  · -- the outer loop
    have hpc := hF2 fun h ↦ hd (of_decide_eq_true h)
    refine exec_at (inf hp b2_in_code (by simp [b2])) (exec_after run_b1 run_b2) hwf
      (by intro l h; cases h) (hpc.trans rfl) hm2 fun st3 hm3 hpc3 ↦ ?_
    simp only [PcOk] at hpc3
    have hO : Outer a s m0 0 (cnt m0) s [] st3.data := by
      refine outer0 h h0 (by omega) ?_
      rw [← after_eq run_b2] at hm3
      exact hm3
    refine Sym.loop (I := fun n st ↦ ∃ j r s' qs, n = cnt m0 - j ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b10Offset) ∧
        Outer a s m0 j r s' qs st.data) (fun n st ⟨j, r, s', qs, hn, hpc, hO⟩ ↦ ?_)
      ⟨0, _, _, _, rfl, hpc3.trans (hp.label NativeRustcVmX64.Vm.SampleQueries.label_3_at), hO⟩
    have hj := hO.jlt
    refine Eventually.mono (outer_turn hp h hsq hqb hpc hO) fun st' h' ↦ ?_
    rcases h' with h' | ⟨hpc', r', s'', qs', hO'⟩
    · exact .inl h'
    · exact .inr ⟨cnt m0 - (j + 1), by omega, j + 1, r', s'', qs', rfl, hpc', hO'⟩

end

end NativeRustcVmX64.Whir.SampleQueries
