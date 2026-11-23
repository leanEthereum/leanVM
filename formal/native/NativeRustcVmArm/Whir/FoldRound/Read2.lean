module

public import NativeRustcVmArm.Code.Vm.FoldRound.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Whir.FoldRound.Read1

/-!
# `fold_round`: a scalar's tag, the scalar into registers, the next `read_scalar`

`load_rs` (`b2`, `b4`, `b6`): the scalar `x` the frame holds into two registers, `read_scalar`
again. `check4` (`b3`, `b5`, `b7`): a scalar's tag; `None` to `.LFoldRound_7`.
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

public section

variable [Host] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData} {k : Nat}

/-- **A scalar into registers, `read_scalar` again.** -/
theorem load_rs (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {lb : List Directive} {jl : Nat} (hkl : lb.IsInfixAt code jl) (hne : lb ≠ []) {Sl : SState}
    (hxl : exec lb midS = some (Sl, .call NativeRustcVmArm.Vm.TStateReadScalar.entryLabel)) (hlm : Sl.mem = [])
    (hlsp : Sl.sp = .ptr 0 0) {rA rB : XReg} (hA : Sl.reg rA = some (.load 0 96 8))
    (hB : Sl.reg rB = some (.load 0 104 8)) (hcA : calleeSaved rA = true)
    (hcB : calleeSaved rB = true) (h0 : Sl.reg .X0 = some (.ptr 0 88))
    (h1 : Sl.reg .X1 = some (.reg .X23)) (h19 : Sl.reg .X19 = some (.reg .X19))
    (h20 : Sl.reg .X20 = some (.reg .X20)) (h23 : Sl.reg .X23 = some (.reg .X23))
    (hlk : ∀ r, calleeSaved r = true → r ≠ rA → r ≠ rB → Sl.reg r = some (.reg r))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + jl)) (hb : Base w m0 st.data) {x : EW}
    {s : TState} (hopt : OptEWAt st.data.dmem (loc m0 88) (some x))
    (hts : TStateAt st.data.dmem (tA m0) a s) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + jl + lb.length) → Base w m0 st'.data →
      AfterRs (a := a) s m0 st'.data → st'.data.regs.getXReg rA = x.c0 →
      st'.data.regs.getXReg rB = x.c1 →
      (∀ r, calleeSaved r = true → r ≠ rA → r ≠ rB →
        st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  refine frame_block h hkl hne hxl hlm hlsp hpc hp hb fun st1 hm1 hpc1 hf1 hd1 ↦ ?_
  simp only [PcOk] at hpc1
  have hb1 : Base w m0 st1.data :=
    ⟨hf1, (reg_of hm1 h19 rfl).trans hb.x19, (reg_of hm1 h20 rfl).trans hb.x20,
      (reg_of hm1 h23 rfl).trans hb.x23, by rw [hd1]; exact hb.ws⟩
  have hvA : st1.data.regs.getXReg rA = x.c0 := reg_of hm1 hA (elem0 rfl hopt)
  have hvB : st1.data.regs.getXReg rB = x.c1 := reg_of hm1 hB (elem1 rfl hopt)
  refine rs_call h hrs hb1 hpc1 ?_ ((reg_of hm1 h1 rfl).trans hb.x23) (by rw [hd1]; exact hts)
    fun m2 hb2 hopt2 hnext2 hcs _ ↦ cont ⟨m2, _⟩ rfl hb2 ⟨hopt2, hnext2⟩
      ((hcs rA hcA).trans hvA) ((hcs rB hcB).trans hvB)
      fun r hr hra hrb ↦ (hcs r hr).trans (reg_of hm1 (hlk r hr hra hrb) rfl)
  have := reg_val hm1 h0
  simp only [Sym.eval] at this
  exact this

/-- **A scalar's tag** (`ldr w8, [sp, #88]; tbz w8, #0, .LFoldRound_7`): `None` to the epilogue. -/
theorem check4 (hp : Placed code k) (h : FoldRoundPre a s0 w m0) {cb : List Directive}
    {jc : Nat} (hkc : cb.IsInfixAt code jc) (hne : cb ≠ []) {Sc : SState}
    (hxc : exec cb midS = some (Sc, .cond (.not (.bit .W32 (.load 0 88 4) 0)) NativeRustcVmArm.Vm.FoldRound.label_7))
    (hcm : Sc.mem = []) (hcsp : Sc.sp = .ptr 0 0)
    (hck : ∀ r, r ≠ .X8 → Sc.reg r = some (.reg r))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + jc)) (hb : Base w m0 st.data)
    {s : TState} (haft : AfterRs (a := a) s m0 st.data)
    (hnone : readScalar.run s = none → (foldRound w).run s0 = none)
    (cont : ∀ x s' st', readScalar.run s = some (x, s') →
      st'.pc = Host.addrOf (k + jc + cb.length) → Base w m0 st'.data →
      OptEWAt st'.data.dmem (loc m0 88) (some x) → TStateAt st'.data.dmem (tA m0) a s' →
      (∀ r, r ≠ .X8 → st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  refine frame_block h hkc hne hxc hcm hcsp hpc hp hb fun st1 hm1 hpc1 hf1 hd1 ↦ ?_
  simp only [PcOk] at hpc1
  have hk1 : ∀ r, r ≠ .X8 → st1.data.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦
    reg_of hm1 (hck r hr) rfl
  have hb1 : Base w m0 st1.data :=
    ⟨hf1, (hk1 .X19 (by decide)).trans hb.x19, (hk1 .X20 (by decide)).trans hb.x20,
      (hk1 .X23 (by decide)).trans hb.x23, by rw [hd1]; exact hb.ws⟩
  have hcond : (SBool.not (.bit .W32 (.load 0 88 4) 0)).eval (frameEnv m0 st.data) =
      !(readScalar.run s).isSome := by
    sym_simp
    rw [tag4 (env := frameEnv m0 st.data) rfl (by simpa using haft.opt)]
    cases readScalar.run s <;> simp only [Option.map_none, Option.map_some, Option.isSome_none,
      Option.isSome_some, Bool.false_eq_true, ↓reduceIte] <;> decide
  rw [hcond] at hpc1
  cases hr : readScalar.run s with
  | none =>
    simp only [hr, Option.isSome_none, Bool.not_false, ↓reduceIte,
      hp.label (j := NativeRustcVmArm.Vm.FoldRound.b20Offset) NativeRustcVmArm.Vm.FoldRound.label_7_at] at hpc1
    exact none_exit hp h (hnone hr) hpc1 hb1
  | some p =>
    simp only [hr, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hopt := haft.opt
    rw [hr] at hopt
    refine cont p.1 p.2 st1 hr hpc1 hb1 (by rw [hd1]; exact hopt) ?_ hk1
    rw [hd1]; exact haft.next p.1 p.2 hr

end

end NativeRustcVmArm.Whir.FoldRound
