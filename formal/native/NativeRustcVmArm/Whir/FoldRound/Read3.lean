module

public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Whir.FoldRound.Read2

/-!
# `fold_round`: the four scalars and the grind

`reads`: from the entry, the four scalars (`u0`, `v`, `c0`, `c1` into X29/X24, X27/X28, X25/X26,
X21/X22) and the grind, to `b10` (`AtB10`), or `None` returned.
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

public section

section
variable [Labels]

/-- **At `b10`**: the scalars in registers, the `TState` after the grind, the model's result. -/
structure AtB10 (a : DecArea) (s0 : TState) (w : WhirStateW) (m0 : MachineData) (s5 : TState)
    (u0 v c0 c1 : EW) (st : MachineData) : Prop where
  base : Base w m0 st
  x29 : st.regs.X29 = u0.c0
  x24 : st.regs.X24 = u0.c1
  x27 : st.regs.X27 = v.c0
  x28 : st.regs.X28 = v.c1
  x25 : st.regs.X25 = c0.c0
  x26 : st.regs.X26 = c0.c1
  x21 : st.regs.X21 = c1.c0
  x22 : st.regs.X22 = c1.c1
  ts : TStateAt st.dmem (tA m0) a s5
  model : (foldRound w).run s0 = some ((foldW w u0 v c0 c1 (sq s5).1 (sq (sq s5).2).1,
    ⟨(sq s5).1, (sq (sq s5).2).1⟩), (sq (sq s5).2).2)

end

variable [Host] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData} {k : Nat}

/-- **The grind** (`b8`: `c1` into X21, X22, `grind(t, 7)`; `b9`: `None` to the epilogue). -/
theorem grind_step (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b8Offset)) (hb : Base w m0 st.data) {x : EW}
    {s : TState} (hopt : OptEWAt st.data.dmem (loc m0 88) (some x))
    (hts : TStateAt st.data.dmem (tA m0) a s)
    (hnone : (grind 7).run s = none → (foldRound w).run s0 = none)
    (cont : ∀ s5 st', (grind 7).run s = some ((), s5) → st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b10Offset) →
      Base w m0 st'.data → TStateAt st'.data.dmem (tA m0) a s5 →
      st'.data.regs.X21 = x.c0 → st'.data.regs.X22 = x.c1 →
      (∀ r, calleeSaved r = true → r ≠ .X21 → r ≠ .X22 →
        st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have c := ctx h
  have hle : 208 + grindStack ≤ foldRoundStack := by decide
  refine frame_block h b8_in_code (by simp [b8]) run_b8 rfl rfl hpc hp hb
    fun st1 hm1 hpc1 hf1 hd1 ↦ ?_
  simp only [PcOk] at hpc1
  have hb1 : Base w m0 st1.data :=
    ⟨hf1, (reg_of hm1 (r := .X19) (v := .reg .X19) rfl rfl).trans hb.x19,
      (reg_of hm1 (r := .X20) (v := .reg .X20) rfl rfl).trans hb.x20,
      (reg_of hm1 (r := .X23) (v := .reg .X23) rfl rfl).trans hb.x23, by rw [hd1]; exact hb.ws⟩
  have h21 : st1.data.regs.X21 = x.c0 := reg_of hm1 (r := .X21) rfl (elem0 rfl hopt)
  have h22 : st1.data.regs.X22 = x.c1 := reg_of hm1 (r := .X22) rfl (elem1 rfl hopt)
  have hx0 : st1.data.regs.X0.toBitVec = tA m0 := by
    rw [show st1.data.regs.X0 = st.data.regs.X23 from
      reg_of hm1 (r := .X0) (v := .reg .X23) rfl rfl, hb.x23]
  have hx1 : grindBits st1.data = 7 := by
    rw [grindBits, show st1.data.regs.X1 = 7 from reg_of hm1 (r := .X1) (v := .lit 7) rfl rfl]
    rfl
  have hpre : GrindPre a s st1.data := by
    refine ⟨c.stackOk hf1 hle, c.rcAt hf1 hle, ?_, ?_, by rw [hx1]; decide⟩
    · show TStateAt st1.data.dmem st1.data.regs.X0.toBitVec a s
      rw [hx0, hd1]; exact hts
    · show TStateOk st1.data st1.data.regs.X0.toBitVec a grindStack
      rw [hx0]; exact c.tstateOk hf1 hle
  rw [show k + NativeRustcVmArm.Vm.FoldRound.b8Offset + b8.length = k + NativeRustcVmArm.Vm.FoldRound.b9Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FoldRound.b8_next]] at hpc1
  refine Fr.callW hf1 (pre_hN h) hle (fun _ h ↦ by cases h) slots_le c.frame_outs (o := 0)
    (n := 0) (by decide) (by decide)
    (spec_with (hgr s) fun m ↦ m.regs.X0.toBitVec = tA m0 ∧ grindBits m = 7)
    (fun m m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.1.2.2.1 fun q hq' ↦ by
      obtain ⟨-, h0, -⟩ := hq
      rcases hq' with hq' | hq'
      · rw [h0] at hq'; exact .inr (.inr (.inr (.inr hq')))
      · exact .inl hq', hq.1.2.2.2⟩) hpc1 ⟨hpre, hx0, hx1⟩ fun m2 hf2 hq hcs ↦ ?_
  obtain ⟨⟨hok, hnext, hs, -⟩, -, -⟩ := hq
  simp only [hx0, hx1] at hok hnext hs
  have hb2 : Base w m0 m2 :=
    ⟨hf2, (hcs .X19 rfl).trans hb1.x19, (hcs .X20 rfl).trans hb1.x20,
      (hcs .X23 rfl).trans hb1.x23, ws_keep h hb1.ws hs fun q hq ↦ by
        rcases hq with hq | hq
        · exact Or.inr (Or.inr hq)
        · exact Or.inl (stack_sub h hf1 hle hq)⟩
  -- `b9`
  refine frame_block (st := ⟨m2, _⟩) h b9_in_code (by simp [b9]) run_b9 rfl rfl rfl hp hb2
    fun st3 hm3 hpc3 hf3 hd3 ↦ ?_
  simp only [PcOk] at hpc3
  have hcond : (SBool.not (.bit .W32 (.reg .X0) 0)).eval (frameEnv m0 m2) =
      !((grind 7).run s).isSome := by
    sym_simp
    simp only [Env.ofMachine_regs]
    rw [show m2.regs.getXReg .X0 = _ from hok]
    cases (grind 7).run s <;> simp only [Option.isSome_none, Option.isSome_some, okWord,
      Bool.false_eq_true, ↓reduceIte] <;> decide
  rw [hcond] at hpc3
  have hk3 : ∀ r, st3.data.regs.getXReg r = m2.regs.getXReg r := fun r ↦
    reg_of hm3 (v := .reg r) (by cases r <;> rfl) rfl
  have hb3 : Base w m0 st3.data :=
    ⟨hf3, (hk3 .X19).trans hb2.x19, (hk3 .X20).trans hb2.x20, (hk3 .X23).trans hb2.x23,
      by rw [hd3]; exact hb2.ws⟩
  cases hr : (grind 7).run s with
  | none =>
    simp only [hr, Option.isSome_none, Bool.not_false, ↓reduceIte,
      hp.label (j := NativeRustcVmArm.Vm.FoldRound.b20Offset) NativeRustcVmArm.Vm.FoldRound.label_7_at] at hpc3
    exact none_exit hp h (hnone hr) hpc3 hb3
  | some p =>
    simp only [hr, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    refine cont p.2 st3 (by rw [hr]) hpc3 hb3 (by rw [hd3]; exact hnext _ _ hr)
      ((hk3 .X21).trans ((hcs .X21 rfl).trans h21)) ((hk3 .X22).trans ((hcs .X22 rfl).trans h22))
      fun r hr' h1 h2 ↦ (hk3 r).trans ((hcs r hr').trans (reg_of hm1 (v := .reg r) (by
        cases r <;> first | rfl | contradiction) rfl))

end

end NativeRustcVmArm.Whir.FoldRound
