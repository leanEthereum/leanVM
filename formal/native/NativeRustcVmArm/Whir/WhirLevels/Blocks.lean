module

public import NativeRustcVmArm.Whir.WhirLevels.Basic

/-!
# `whir_levels`: blocks shared by the levels

A block reading `n` bytes at a register (`readBlock`, the `lvS`/`wS`/`lv0S` states); the `None`
test after each call (`cbz_step`, the blocks equal to `b2`); the epilogue returning `None` (`b38`,
`exit_none`); the frame's environment (`frame_wf`, `frame_match`) and its changes (`changes_of`).
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.WhirLevels

public section

theorem inf [Host] {k : Nat} (hp : Placed code k) {bl : List Directive} {j : Nat}
    (hb : bl.IsInfixAt code j) (hne : bl ≠ []) : bl.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

/-- The frame's environment. -/
abbrev frameEnv (m0 st : MachineData) : Env := Env.ofMachine st [(base m0 96, 96)]

section
variable [Labels] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat}

theorem frame_wf (c : Ctx a s0 levels ba b claim m0 rate) {st : MachineData} (hf : WFr m0 st) :
    (frameEnv m0 st).WF := by
  have hN := c.hN
  have hv := stack_val.1
  exact Env.wf_of ⟨⟨fun i hi ↦ hf.kept _ (frame_mapped c.stack (by omega) i hi),
    base_noWrap (by omega)⟩, trivial⟩ (List.pairwise_singleton _ _)

theorem frame_match (c : Ctx a s0 levels ba b claim m0 rate) {st : MachineData} (hf : WFr m0 st) :
    Match (frameEnv m0 st) epiS st := by
  have hN := c.hN
  have hv := stack_val.1
  refine match_ofMachine ⟨rfl, fun _ ↦ ?_, trivial⟩ ?_ trivial trivial trivial trivial
  · have e1 := base_toNat (m0 := m0) (F := 96) (by omega)
    have := c.stack.1
    show (base m0 96).toNat % 16 = 0
    omega
  · rw [hf.sp]; simp [Sym.eval]

omit [Labels] in
/-- The frame's changes are the contract's. -/
theorem changes_of {st : MachineData} (hf : WFr m0 st) : ChangesIn m0 st whirLevelsStack
    [⟨pA m0, whirBytes⟩, ⟨tA m0, tstateBytes⟩] :=
  NativeRustcVm.SameOutside.mono hf.same fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact Or.inr hq
    · exact Or.inl ⟨_, List.mem_cons_self, hq⟩
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩

end

section
variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {k : Nat}

/-- **A block reading the `n` bytes at register `r`**, from a state of the frame: the frame and
the memory kept. -/
theorem readBlock {st : MachineState} (hf : WFr m0 st.data) {ds : List Directive} {j : Nat}
    {r : XReg} {n : Nat} {x0 : BitVec 64} {S' : SState} {x : Exit} {R : MachineState → Prop}
    (hk : ds.IsInfixAt Host.prog j) (hx : exec ds (init [(n, false)] .sp [(r, .ptr 0 0)]) =
      some (S', x)) (hpc : st.pc = Host.addrOf j) (hr : (st.data.regs.getXReg r).toBitVec = x0)
    (hmap : NativeRustcVm.Mapped st.data.dmem x0 n) (hnw : NoWrap x0 n)
    (hmem : S'.mem = []) (hsp : S'.sp = .sp)
    (hkeep : (init [(n, false)] .sp [(r, .ptr 0 0)]).reg .X29 = some (.reg .X29) ∧
      S'.reg .X29 = some (.reg .X29))
    (cont : ∀ st', WFr m0 st'.data → st'.data.dmem = st.data.dmem →
      Match (Env.ofMachine st.data [(x0, n)]) (init [(n, false)] .sp [(r, .ptr 0 0)]) st.data →
      Match (Env.ofMachine st.data [(x0, n)]) S' st'.data →
      PcOk (Env.ofMachine st.data [(x0, n)]) x (Host.addrOf (j + ds.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf : (Env.ofMachine st.data [(x0, n)]).WF :=
    Env.wf_of ⟨⟨hmap, hnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine st.data [(x0, n)]) (init [(n, false)] .sp [(r, .ptr 0 0)])
      st.data :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by simp [Sym.eval, hr], trivial⟩ trivial trivial trivial
  refine exec_at hk hx hwf hpc hm fun st' hm' hpc' ↦
    cont st' ?_ (hm'.dmem_eq hwf hmem) hm hm' hpc'
  refine Fr.ofBlock hf hm hm' hwf rfl hmem (by rw [hsp]; rfl) fun r' hr' ↦ ?_
  simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact ⟨_, hkeep.1, hkeep.2⟩

/-- **The `None` test** (`cbz w0`, a block equal to `b2`) after a call returning `0` or `1`: to
`b38` on `0`, to the next block on `1`, the registers and the memory kept. -/
theorem cbz_step (hp : Placed code k) {j : Nat} (hj : b2.IsInfixAt code j) {st : MachineState}
    (hf : WFr m0 st.data) (hpc : st.pc = Host.addrOf (k + j)) {R : MachineState → Prop}
    (hx : st.data.regs.X0 = 0 ∨ st.data.regs.X0 = 1)
    (c0 : st.data.regs.X0 = 0 → ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.WhirLevels.b38Offset) → WFr m0 st'.data →
      st'.data.dmem = st.data.dmem →
      (∀ r, st'.data.regs.getXReg r = st.data.regs.getXReg r) → Eventually (step1 Host.exe) R st')
    (c1 : st.data.regs.X0 = 1 → ∀ st', st'.pc = Host.addrOf (k + (j + 1)) → WFr m0 st'.data →
      st'.data.dmem = st.data.dmem →
      (∀ r, st'.data.regs.getXReg r = st.data.regs.getXReg r) → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  refine hf.regsBlock (inf hp hj (by simp [b2])) run_b2 hpc rfl rfl (by decide)
    fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
  have hk1 : ∀ r' : XReg, st1.data.regs.getXReg r' = st.data.regs.getXReg r' := fun r' ↦
    reg_of hm1 (v := .reg r') (by cases r' <;> rfl) rfl
  simp only [PcOk] at hpc1
  rcases hx with hx | hx
  · have hc : (SBool.cmp CmpOp.eq RegWidth.W32 (Sym.reg XReg.X0) (Sym.lit 0)).eval
        (Env.ofMachine st.data []) = true := by
      simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
      rw [show st.data.regs.getXReg .X0 = st.data.regs.X0 from rfl, hx]
      rfl
    simp only [hc, ↓reduceIte] at hpc1
    rw [hp.label (j := NativeRustcVmArm.Vm.WhirLevels.b38Offset) NativeRustcVmArm.Vm.WhirLevels.label_27_at] at hpc1
    exact c0 hx st1 hpc1 hf1 hd1 hk1
  · have hc : (SBool.cmp CmpOp.eq RegWidth.W32 (Sym.reg XReg.X0) (Sym.lit 0)).eval
        (Env.ofMachine st.data []) = false := by
      simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
      rw [show st.data.regs.getXReg .X0 = st.data.regs.X0 from rfl, hx]
      rfl
    rw [hc] at hpc1
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
    exact c1 hx st1 (by rw [hpc1]; simp [b2, Nat.add_assoc]) hf1 hd1 hk1

/-- **The epilogue returning `None`** (`b38`, `.LWhirLevels_27`), the model's run rejected. -/
theorem exit_none (hp : Placed code k) (c : Ctx a s0 levels ba b claim m0 rate)
    {st : MachineState} (hf : WFr m0 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.WhirLevels.b38Offset))
    (hR : runAll s0 levels b claim m0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  have hwf := frame_wf c hf
  have hm := frame_match c hf
  refine exec_at (inf hp b38_in_code (by simp [b38])) run_b38 hwf hpc hm
    fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hret, hsv⟩ := hf.exit hm' hwf (by decide)
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf rfl
  have h0 : st'.data.regs.X0 = 0 := reg_of hm' (r := .X0) rfl rfl
  simp only [PcOk] at hpc'
  refine ⟨hpc'.trans hret, ?_, ?_, ?_, hsv⟩
  · rw [h0]
    show (0 : UInt64) = okWord (runAll s0 levels b claim m0).isSome
    rw [hR]; rfl
  · intro x s' h
    change runAll s0 levels b claim m0 = _ at h
    rw [hR] at h; cases h
  · intro q hq; rw [hd]; exact changes_of hf q hq

end

end

end NativeRustcVmArm.Whir.WhirLevels
