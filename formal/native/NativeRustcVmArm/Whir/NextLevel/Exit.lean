module

public import NativeRustcVmArm.Whir.NextLevel.Step

/-!
# `next_level`: `None` returned, a callee's `Option<()>` tested

`none14`: at `.LNextLevel_14` (`b27`) with X0 `0`, `None` returned; `none13`: at
`.LNextLevel_13` (`b26`, X0 set to `0`). `chk14`: `cbz w0, .LNextLevel_14` (`b1`, `b4`, `b6`,
`b14`) after a callee's `Option<()>` in X0; `chk13`: `tbz w0, #0, .LNextLevel_13` (`b12`, `b23`).
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel

public section

theorem b4_eq : b4 = b1 := rfl
theorem b6_eq : b6 = b1 := rfl
theorem b14_eq : b14 = b1 := rfl
theorem b23_eq : b23 = b12 := rfl

theorem b4_in : b1.IsInfixAt code b4Offset := b4_eq ▸ b4_in_code
theorem b6_in : b1.IsInfixAt code b6Offset := b6_eq ▸ b6_in_code
theorem b14_in : b1.IsInfixAt code b14Offset := b14_eq ▸ b14_in_code
theorem b23_in : b12.IsInfixAt code b23Offset := b23_eq ▸ b23_in_code

theorem okWord_toBitVec (b : Bool) :
    (okWord b).toBitVec = BitVec.ofNat 64 (if b then 1 else 0) := by
  cases b <;> rfl

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

/-- The outputs are among the contract's. -/
theorem outs_changes (h : NextLevelPre a s level w rounds m0) {q : BitVec 64} (hq : outs m0 q) :
    NativeRustcVm.InAny [⟨pA m0, whirBytes⟩, ⟨tA m0, tstateBytes⟩] q := by
  rcases hq with hq | hq
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩
  · refine ⟨_, List.mem_cons_self, ?_⟩
    have g := geo h
    have hq' := qA_toNat (m0 := m0) g.pW
    have hqw : (qA m0).toNat + 1848 ≤ 2 ^ 64 := by rw [hq']; have := g.pW; omega
    have r := inr hqw (show InRange (qA m0) 1848 q from hq)
    show InRange (pA m0) 63200 q
    rw [Sym.inRange_iff g.pW]; omega

/-- **`None`'s postcondition** from a state of the frame, memory and X0 `0`. -/
theorem none_post (h : NextLevelPre a s level w rounds m0)
    (hnone : runN level w rounds m0 s = none) {st m' : MachineData} (hf : NFr m0 st)
    (hx0 : m'.regs.X0 = 0) (hd : m'.dmem = st.dmem) (hsv : Saved m0 m') :
    NextLevelPost a s level w rounds m0 m' := by
  refine ⟨?_, fun _ _ he ↦ ?_, fun _ _ he ↦ ?_, fun q hq ↦ ?_, hsv⟩
  · show m'.regs.X0 = okWord (runN level w rounds m0 s).isSome
    rw [hnone, hx0]; rfl
  · rw [show (nextLevelM m0.regs.X1.toNat level ⟨m0.regs.X3.toNat, m0.regs.X4.toNat, 0⟩
      m0.regs.X5.toNat w rounds).run s = none from hnone] at he; cases he
  · rw [show (nextLevelM m0.regs.X1.toNat level ⟨m0.regs.X3.toNat, m0.regs.X4.toNat, 0⟩
      m0.regs.X5.toNat w rounds).run s = none from hnone] at he; cases he
  · rw [hd]
    exact hf.same q fun hq' ↦ hq (hq'.elim (fun h' ↦ .inr h') fun h' ↦ .inl (outs_changes h h'))

end

section
variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **`None` at `.LNextLevel_14`.** -/
theorem none14 (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    (hnone : runN level w rounds m0 s = none) {st : MachineState} (hf : NFr m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b27Offset)) (hx0 : st.data.regs.X0 = 0) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st :=
  Eventually.mono (epi hp h hf hpc) fun _ ⟨h1, h2, h3, h4⟩ ↦
    ⟨h1, none_post h hnone hf (h2.trans hx0) h3 h4⟩

/-- **`None` at `.LNextLevel_13`.** -/
theorem none13 (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    (hnone : runN level w rounds m0 s = none) {st : MachineState} (hf : NFr m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b26Offset)) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st := by
  refine exec_at (inf hp b26_in_code (by simp [b26])) run_b26 (wfF h hf) hpc (mF h hf)
    fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq (wfF h hf) rfl
  have hf1 : NFr m0 st1.data := Fr.ofBlock hf (mF h hf) hm1 (wfF h hf) rfl rfl rfl
    (fun _ h ↦ by cases h)
  exact none14 hp h hnone hf1 (hpc1.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b26_next]))
    (reg_of hm1 (r := .X0) (v := .lit 0) rfl rfl)

/-- **`cbz w0, .LNextLevel_14`** after a callee's `Option<()>` `ok` in X0: `None` returned, or
on. -/
theorem chk14 (hp : Placed code k) (h : NextLevelPre a s level w rounds m0) {j : Nat}
    (hj : b1.IsInfixAt code j) {st : MachineState} (hf : NFr m0 st.data)
    (hpc : st.pc = Host.addrOf (k + j)) {ok : Bool} (hx0 : st.data.regs.X0 = okWord ok)
    (hnone : ok = false → runN level w rounds m0 s = none) {R : MachineState → Prop}
    (hR : ∀ st', Goal a s level w rounds m0 st' → R st')
    (cont : ok = true → ∀ st', st'.pc = Host.addrOf (k + j + 1) → NFr m0 st'.data →
      st'.data.dmem = st.data.dmem →
      (∀ r : XReg, st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  refine exec_at (inf hp hj (by simp [b1])) run_b1 (wfF h hf) hpc (mF h hf)
    fun st1 hm1 hpc1 ↦ ?_
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq (wfF h hf) rfl
  have hf1 : NFr m0 st1.data := Fr.ofBlock hf (mF h hf) hm1 (wfF h hf) rfl rfl rfl
    (fun _ h ↦ by cases h)
  have hr : ∀ r : XReg, st1.data.regs.getXReg r = st.data.regs.getXReg r := fun r ↦
    reg_of hm1 (r := r) (v := .reg r) (by cases r <;> rfl) rfl
  have hc : (SBool.cmp .eq .W32 (.reg .X0) (.lit 0)).eval (envF m0 st.data) = !ok := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, Env.ofMachine_regs]
    show (low .W32 st.data.regs.X0.toBitVec == low .W32 (BitVec.ofNat 64 0)) = !ok
    rw [hx0, okWord_toBitVec]
    cases ok <;> decide
  simp only [PcOk, hc] at hpc1
  cases ok with
  | false =>
    simp only [Bool.not_false, ↓reduceIte] at hpc1
    exact Eventually.mono (none14 hp h (hnone rfl) hf1 (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.NextLevel.b27Offset) NativeRustcVmArm.Vm.NextLevel.label_14_at))
      ((hr .X0).trans (hx0.trans rfl))) hR
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact cont rfl st1 hpc1 hf1 hd hr

/-- **`tbz w0, #0, .LNextLevel_13`** after a callee's `Option<()>` `ok` in X0. -/
theorem chk13 (hp : Placed code k) (h : NextLevelPre a s level w rounds m0) {j : Nat}
    (hj : b12.IsInfixAt code j) {st : MachineState} (hf : NFr m0 st.data)
    (hpc : st.pc = Host.addrOf (k + j)) {ok : Bool} (hx0 : st.data.regs.X0 = okWord ok)
    (hnone : ok = false → runN level w rounds m0 s = none) {R : MachineState → Prop}
    (hR : ∀ st', Goal a s level w rounds m0 st' → R st')
    (cont : ok = true → ∀ st', st'.pc = Host.addrOf (k + j + 1) → NFr m0 st'.data →
      st'.data.dmem = st.data.dmem →
      (∀ r : XReg, st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  refine exec_at (inf hp hj (by simp [b12])) run_b12 (wfF h hf) hpc (mF h hf)
    fun st1 hm1 hpc1 ↦ ?_
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq (wfF h hf) rfl
  have hf1 : NFr m0 st1.data := Fr.ofBlock hf (mF h hf) hm1 (wfF h hf) rfl rfl rfl
    (fun _ h ↦ by cases h)
  have hr : ∀ r : XReg, st1.data.regs.getXReg r = st.data.regs.getXReg r := fun r ↦
    reg_of hm1 (r := r) (v := .reg r) (by cases r <;> rfl) rfl
  have hc : (SBool.not (.bit .W32 (.reg .X0) 0)).eval (envF m0 st.data) = !ok := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    show (!(low .W32 st.data.regs.X0.toBitVec).getLsbD 0) = !ok
    rw [hx0, okWord_toBitVec]
    cases ok <;> decide
  simp only [PcOk, hc] at hpc1
  cases ok with
  | false =>
    simp only [Bool.not_false, ↓reduceIte] at hpc1
    exact Eventually.mono (none13 hp h (hnone rfl) hf1 (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.NextLevel.b26Offset) NativeRustcVmArm.Vm.NextLevel.label_13_at))) hR
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact cont rfl st1 hpc1 hf1 hd hr

end

end

end NativeRustcVmArm.Whir.NextLevel
