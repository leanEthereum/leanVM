module

public import NativeRustcVmArm.Code.Vm.QueryBits.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Whir.SampleQueries.Inner

/-!
# `sample_queries`: the loops

The inner loop runs to `b8` (`inner_run`); the outer loop to the epilogue (`outer_run`); with a
depth above `128`, the squeezes' loop (`b3`, `b4`) to the epilogue (`big_run`).
-/

namespace NativeRustcVmArm.Whir.SampleQueries

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.SampleQueries
open NativeRustcVm (BufWordsAt WordsAt WordAt)

public section

variable [Host] {a : DecArea} {s0 : TState} {m1 : MachineData} {k : Nat}

/-- **The inner loop**, from its head after `i` positions, to `b8`. -/
theorem inner_run (hp : Placed code k) (h : SampleQueriesPre a s0 m1)
    (hqb : Spec (Labels.label NativeRustcVmArm.Vm.QueryBits.entryLabel) QueryBitsPre QueryBitsPost)
    {j r : Nat} {s : TState} {qs : List UInt64} {n : Nat} :
    ∀ {d i : Nat} {st : MachineState}, d = n - i → st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SampleQueries.b13Offset) →
      Inner a s0 m1 j r s qs n i st.data →
      Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SampleQueries.b8Offset) ∧
        AtB8 a s0 m1 j r n (sq s).2 (qs ++ (chunk (dep m1) (sq s).1 n).toList) st'.data) st := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro i st hd hpc hi
    refine Eventually.bind (inner_step hp h hqb hpc hi) fun st' hst' ↦ ?_
    rcases hst' with ⟨hpc', hi'⟩ | hb
    · have := hi.ilt
      exact ih (n - (i + 1)) (by omega) rfl hpc' hi'
    · exact .done _ hb

/-- **The outer loop**, from its head after `j` challenges, to the epilogue. -/
theorem outer_run (hp : Placed code k) (h : SampleQueriesPre a s0 m1)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hqb : Spec (Labels.label NativeRustcVmArm.Vm.QueryBits.entryLabel) QueryBitsPre QueryBitsPost) :
    ∀ {d : Nat} {st : MachineState}, OuterAt a s0 m1 k d st →
      Eventually (step1 Host.exe) (Goal a s0 m1) st := by
  refine Sym.loop (OuterAt a s0 m1 k) fun d st hO ↦ ?_
  unfold OuterAt at hO
  obtain ⟨j, r, s, qs, hd, hpc, ho⟩ := hO
  refine Eventually.bind (outer_step hp h hsq hpc ho) fun st1 h1 ↦ ?_
  rcases h1 with hg | ⟨hpc1, hb⟩ | ⟨hpc1, nn, hi⟩
  · exact .done _ (Or.inl hg)
  · refine Eventually.mono (tail_b8 hp h hpc1 hb) fun st2 h2 ↦ ?_
    rcases h2 with hg | ⟨n', hn', ho'⟩
    · exact Or.inl hg
    · exact Or.inr ⟨n', by omega, ho'⟩
  · refine Eventually.bind (inner_run hp h hqb rfl hpc1 hi) fun st2 ⟨hpc2, hb⟩ ↦ ?_
    refine Eventually.mono (tail_b8 hp h hpc2 hb) fun st3 h3 ↦ ?_
    rcases h3 with hg | ⟨n', hn', ho'⟩
    · exact Or.inl hg
    · exact Or.inr ⟨n', by omega, ho'⟩

/-- **The squeezes' loop** (depth above `128`), from its head after `j` squeezes, to the
epilogue. -/
theorem big_run (hp : Placed code k) (h : SampleQueriesPre a s0 m1)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hd : 128 < dep m1) :
    ∀ {d j : Nat} {s : TState} {st : MachineState}, d = cnt m1 - j →
      st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SampleQueries.b3Offset) → Big a s0 m1 j s st.data →
      Eventually (step1 Host.exe) (Goal a s0 m1) st := by
  have h128 : 128 / dep m1 = 0 := Nat.div_eq_of_lt hd
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro j s st hdj hpc hb
    have hjc := hb.jlt
    refine hb.fr.regsBlock (inf hp b3_in_code (by simp [b3])) run_b3 hpc rfl rfl (by rfl)
      fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
    simp only [PcOk] at hpc1
    have hk1 : ∀ r' : XReg, r' ≠ .X0 → r' ≠ .X30 →
        st1.data.regs.getXReg r' = st.data.regs.getXReg r' := fun r' h0 h30 ↦
      reg_of hm1 (v := .reg r') (by cases r' <;> first | rfl | contradiction) rfl
    have hx0 : st1.data.regs.X0 = m1.regs.X0 :=
      (reg_of hm1 (r := .X0) (v := .reg .X20) rfl rfl).trans hb.x20
    have hbuf1 : BufWordsAt st1.data.dmem (oA m1) queryCap [] :=
      ⟨Nat.zero_le _, by rw [hd1]; simpa using hb.buf, NativeRustcVm.wordsAt_nil _ _⟩
    refine squeeze_call h hsq hf1 hpc1 hx0 (by rw [hd1]; exact hb.ts)
      fun m2 hf2 hts2 _ _ hcs2 hs2 ↦ ?_
    have hbuf2 := buf_sq h hf1 hs2 hbuf1
    have hk2 : ∀ r' : XReg, calleeSaved r' = true →
        m2.regs.getXReg r' = st.data.regs.getXReg r' := fun r' hr' ↦
      (hcs2 r' hr').trans (hk1 r' (by rintro rfl; simp [calleeSaved] at hr')
        (by rintro rfl; simp [calleeSaved] at hr'))
    refine hf2.regsBlock (st := ⟨m2, _⟩) (k := k + NativeRustcVmArm.Vm.SampleQueries.b4Offset) (inf hp b4_in_code (by simp [b4])) run_b4
      rfl rfl rfl (by rfl) fun st3 hf3 hd3 hm3 hpc3 ↦ ?_
    simp only [PcOk] at hpc3
    have hx19 : (m2.regs.getXReg .X19).toNat = cnt m1 - j := by
      rw [hk2 .X19 rfl]; exact hb.x19
    have hcond : (SBool.cmp CmpOp.eq RegWidth.W64 (Sym.reg XReg.X19) (Sym.lit 1)).not.eval
        (Env.ofMachine m2 []) = decide (j + 1 < cnt m1) := by
      sym_simp
      simp only [Env.ofMachine_regs]
      rw [bv_beq _ (by decide), hx19]
      by_cases hc : j + 1 < cnt m1
      · simp only [hc, decide_true]; simp; omega
      · simp only [hc, decide_false]; simp; omega
    rw [hcond] at hpc3
    have hmodel : auxP (dep m1) (cnt m1) (cnt m1) s0 =
        auxP (dep m1) (cnt m1 - (j + 1)) (cnt m1) (sq s).2 := by
      rw [hb.model, show cnt m1 - j = cnt m1 - (j + 1) + 1 by omega, auxP_big h128 _ _ _ (by omega)]
    by_cases hc : j + 1 < cnt m1
    · simp only [hc, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.SampleQueries.b3Offset) NativeRustcVmArm.Vm.SampleQueries.label_3_at] at hpc3
      refine ih (cnt m1 - (j + 1)) (by omega) (s := (sq s).2) rfl hpc3 ?_
      exact {
        fr := hf3
        x19 := by
          have := reg_val hm3 (r := .X19) rfl
          sym_simp at this
          simp only [Env.ofMachine_regs] at this
          have e := toNat_sub_of (z := 1) this (by
            rw [hx19, show (1 : UInt64).toNat = 1 from rfl]; omega)
          show (st3.data.regs.getXReg .X19).toNat = _
          rw [e, hx19]
          simp
          omega
        x20 := (reg_of hm3 (r := .X20) (v := .reg .X20) rfl rfl).trans ((hk2 .X20 rfl).trans hb.x20)
        jlt := hc
        ts := by rw [hd3]; exact hts2
        buf := by rw [hd3]; simpa using hbuf2.2.1
        model := hmodel }
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc3
      rw [show k + NativeRustcVmArm.Vm.SampleQueries.b4Offset + b4.length = k + NativeRustcVmArm.Vm.SampleQueries.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SampleQueries.b4_next]] at hpc3
      refine hf3.regsBlock (inf hp b5_in_code (by simp [b5])) run_b5 hpc3 rfl rfl (by rfl)
        fun st4 hf4 hd4 hm4 hpc4 ↦ ?_
      simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.SampleQueries.b18Offset) NativeRustcVmArm.Vm.SampleQueries.label_14_at] at hpc4
      have h0 : st4.data.regs.X0 = 1 := reg_of hm4 (r := .X0) rfl rfl
      refine finish hp h hpc4 hf4 h0 (qs := []) (s := (sq s).2) ?_ (by rw [hd4, hd3]; exact hbuf2)
        (by rw [hd4, hd3]; exact hts2)
      rw [hmodel, show cnt m1 - (j + 1) = 0 by omega, auxP_zero_left]

end

end NativeRustcVmArm.Whir.SampleQueries
