module

public import NativeRustcVmArm.Code.Vm.VerifyExecution.Names
public import NativeRustcVmArm.Top.VerifyExecution.Basic

/-!
# `verify_execution`: the blocks between the calls

The blocks' places and labels (`hb*`, `lbl_*`). Between the calls the blocks run from `callS`
(`At.env`) and keep the body (`At.block`). What the function's run ends in (`Done`: X0 the walk's
success, the `TState` its last state, memory changed only where `Writable`, the callee-saved
registers kept); the epilogue (`exitRet`), the failure path at `.LVerifyExecution_10`
(`fail`), the branch after a call (`branch`: to `fail` when the callee returned `None`).
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyExecution
open NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes)

public section

section
variable [Labels] {a : DecArea} {m0 st : MachineData}

/-- What `verify_execution` ends in, its walk's result `r`: returned to the caller, X0 `r`'s
success, the `TState` its last state, memory changed only where `Writable`, the callee-saved
registers and SP kept. -/
@[expose] def Done (a : DecArea) (m0 : MachineData) (r : Option (Unit × TState))
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ st.data.regs.X0 = okWord r.isSome ∧
    NextAt st.data.dmem m0.regs.X0.toBitVec a r ∧ SameOutside m0.dmem st.data.dmem (Writable m0) ∧
    Saved m0 st.data


/-- The environment between the calls: the frame (region 0) and the working area's first 72 bytes
(region 1). -/
@[expose] def envOf (m0 st : MachineData) : Env :=
  Env.ofMachine st [(m0.regs.SP.toBitVec - BitVec.ofNat 64 96, 96), (m0.regs.X4.toBitVec, 72)]

theorem frame_toNat (g : Geo a m0) :
    (m0.regs.SP.toBitVec - BitVec.ofNat 64 96).toNat = m0.regs.SP.toBitVec.toNat - 96 :=
  toNat_subAddr (by have := g.s; omega)

theorem At.frameMapped (h : At m0 st) (g : Geo a m0) :
    Mapped st.dmem (m0.regs.SP.toBitVec - BitVec.ofNat 64 96) 96 := by
  have hs := g.s
  have hsl := m0.regs.SP.toBitVec.isLt
  have hsb : (stackBelow m0 verifyExecutionStack).toNat = m0.regs.SP.toBitVec.toNat - 18384 :=
    toNat_subAddr hs
  have := frame_toNat g
  exact h.mapped (Mapped.within g.mS (by rw [hsb]; unfold verifyExecutionStack; omega)
    (by rw [hsb]; omega) (by rw [hsb]; unfold verifyExecutionStack; omega))

/-- **The blocks' start** between the calls. -/
theorem At.env (h : At m0 st) (g : Geo a m0) : (envOf m0 st).WF ∧ Match (envOf m0 st) callS st := by
  have hs := g.s
  have hsl := m0.regs.SP.toBitVec.isLt
  have hF := frame_toNat g
  have hal := g.al
  have := g.wS
  have := g.wN
  refine ⟨Env.wf_of ⟨⟨h.frameMapped g, show (m0.regs.SP.toBitVec - BitVec.ofNat 64 96).toNat + 96 ≤
      2 ^ 64 by rw [hF]; omega⟩,
      ⟨h.mapped (Mapped.within (a' := m0.regs.X4.toBitVec) (n' := 72) g.mW (by omega) le_rfl
        (by omega)),
        show m0.regs.X4.toBitVec.toNat + 72 ≤ 2 ^ 64 by omega⟩,
      trivial⟩ (List.pairwise_pair.mpr (show (m0.regs.SP.toBitVec - BitVec.ofNat 64 96).toNat + 96 ≤
        m0.regs.X4.toBitVec.toNat ∨ m0.regs.X4.toBitVec.toNat + 72 ≤
        (m0.regs.SP.toBitVec - BitVec.ofNat 64 96).toNat by rw [hF]; omega)),
    match_ofMachine ⟨rfl, fun _ ↦ show (m0.regs.SP.toBitVec - BitVec.ofNat 64 96).toNat % 16 = 0 by
      rw [hF]; omega, rfl, fun h ↦ absurd h (by decide),
      trivial⟩ (show st.regs.SP.toBitVec = _ + BitVec.ofInt 64 0 by rw [h.body.sp]; simp)
      ⟨show (st.regs.getXReg .X19).toBitVec = _ + BitVec.ofInt 64 0 by
        show st.regs.X19.toBitVec = _
        rw [h.x19]; simp, trivial⟩ trivial trivial trivial⟩

/-- **A block between the calls** writing only where `Writable` and off the slots, keeping
`kept`, keeps the body. -/
theorem At.blockW (h : At m0 st) (g : Geo a m0) {st' : MachineData} {S₁ : SState}
    (hm : Match (envOf m0 st) S₁ st') (hk : keepsRegs callS S₁ kept = true)
    (hW : ∀ p, Written (envOf m0 st) S₁ p → Writable m0 p ∧
      (p.toNat < m0.regs.SP.toBitVec.toNat - 96 + 16 ∨ m0.regs.SP.toBitVec.toNat ≤ p.toNat)) :
    At m0 st' := by
  obtain ⟨hwf, hm₀⟩ := h.env g
  have hk' := hk
  simp only [keepsRegs, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hk'
  have hreg : ∀ r ∈ kept, st'.regs.getXReg r = st.regs.getXReg r := fun r hr ↦ by
    obtain ⟨hs, he⟩ := hk'.1 r hr
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    exact Match.reg_eq hm₀ hm hv (he.trans hv)
  refine ⟨h.body.block' slotsIn (by have := g.s; omega) hm₀ hm hwf rfl hk (fun r hr hn ↦ ?_) hW,
    (hreg .X19 (by simp [kept])).trans h.x19, (hreg .X20 (by simp [kept])).trans h.x20⟩
  cases r <;> simp_all [calleeSaved, slots, kept]

/-- **A block between the calls** writing nothing and keeping `kept` keeps the body and memory. -/
theorem At.block (h : At m0 st) (g : Geo a m0) {st' : MachineData} {S₁ : SState}
    (hm : Match (envOf m0 st) S₁ st') (hk : keepsRegs callS S₁ kept = true) (hmem : S₁.mem = []) :
    At m0 st' ∧ st'.dmem = st.dmem :=
  ⟨h.blockW g hm hk fun p hp ↦ (by
    obtain ⟨w, hw, -⟩ := hp
    rw [hmem] at hw
    cases hw), hm.dmem_eq (h.env g).1 hmem⟩

/-- `cbz w0` after a call returning `okWord b`. -/
theorem cbz_eval {st : MachineData} {b : Bool} (hx : st.regs.X0 = okWord b) :
    (SBool.cmp .eq .W32 (.reg .X0) (.lit 0)).eval (envOf m0 st) = !b := by
  simp only [SBool.eval, Sym.eval, envOf, Env.ofMachine_regs]
  rw [show st.regs.getXReg .X0 = okWord b from hx]
  cases b <;> rfl

/-- `cmp x0, #1; b.ne` after a call returning `okWord b`. -/
theorem bne_eval {st : MachineData} {b : Bool} (hx : st.regs.X0 = okWord b) :
    (SBool.cmp .eq .W64 (.reg .X0) (.lit 1)).not.eval (envOf m0 st) = !b := by
  simp only [SBool.eval, Sym.eval, envOf, Env.ofMachine_regs]
  rw [show st.regs.getXReg .X0 = okWord b from hx]
  cases b <;> rfl

end

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b9Offset) :=
  b9_in_code.trans hp.1 (by simp [b9])
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b10Offset) :=
  b10_in_code.trans hp.1 (by simp [b10])
theorem hb11 (hp : Placed code k) : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b11Offset) :=
  b11_in_code.trans hp.1 (by simp [b11])
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b12Offset) :=
  b12_in_code.trans hp.1 (by simp [b12])
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b13Offset) :=
  b13_in_code.trans hp.1 (by simp [b13])
theorem hb14 (hp : Placed code k) : b14.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b14Offset) :=
  b14_in_code.trans hp.1 (by simp [b14])
theorem hb15 (hp : Placed code k) : b15.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b15Offset) :=
  b15_in_code.trans hp.1 (by simp [b15])
theorem hb16 (hp : Placed code k) : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b16Offset) :=
  b16_in_code.trans hp.1 (by simp [b16])
theorem hb17 (hp : Placed code k) : b17.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b17Offset) :=
  b17_in_code.trans hp.1 (by simp [b17])
theorem hb18 (hp : Placed code k) : b18.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b18Offset) :=
  b18_in_code.trans hp.1 (by simp [b18])
theorem hb19 (hp : Placed code k) : b19.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b19Offset) :=
  b19_in_code.trans hp.1 (by simp [b19])
theorem hb20 (hp : Placed code k) : b20.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b20Offset) :=
  b20_in_code.trans hp.1 (by simp [b20])
theorem hb21 (hp : Placed code k) : b21.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyExecution.b21Offset) :=
  b21_in_code.trans hp.1 (by simp [b21])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.VerifyExecution.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyExecution.entryOffset) NativeRustcVmArm.Vm.VerifyExecution.entry_at
theorem lbl_10 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.VerifyExecution.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b20Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyExecution.b20Offset) NativeRustcVmArm.Vm.VerifyExecution.label_10_at
theorem lbl_11 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.VerifyExecution.label_11 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b21Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyExecution.b21Offset) NativeRustcVmArm.Vm.VerifyExecution.label_11_at


variable {a : DecArea} {m0 : MachineData}

/-- **The epilogue** at `.LVerifyExecution_11`: X0 and memory kept, the entry's registers back. -/
theorem exitRet (hp : Placed code k) (g : Geo a m0) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b21Offset)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      st'.data.regs.X0 = st.data.regs.X0 ∧ st'.data.dmem = st.data.dmem ∧
        Saved m0 st'.data) st := by
  have hs := g.s
  have hsl := m0.regs.SP.toBitVec.isLt
  have hF := frame_toNat g
  have hal := g.al
  have hwf : (Env.ofMachine st.data [(m0.regs.SP.toBitVec - BitVec.ofNat 64 96, 96)]).WF :=
    Env.wf_of ⟨⟨h.frameMapped g, show (m0.regs.SP.toBitVec - BitVec.ofNat 64 96).toNat + 96 ≤
      2 ^ 64 by rw [hF]; omega⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine st.data [(m0.regs.SP.toBitVec - BitVec.ofNat 64 96, 96)]) frameS
      st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ show (m0.regs.SP.toBitVec - BitVec.ofNat 64 96).toNat % 16 = 0 by
      rw [hF]; omega, trivial⟩
      (show st.data.regs.SP.toBitVec = _ + BitVec.ofInt 64 0 by rw [h.body.sp]; simp)
      trivial trivial trivial trivial
  refine exec_at (hb21 hp) run_b21 hwf hpc hm fun st' hm' hpc' ↦ ?_
  have hr := b21_restores
  rw [after_eq run_b21] at hr
  obtain ⟨hsv, hret, hdm⟩ := h.body.ret hm' hwf (by simp [slots]) hr.1 hr.2
  exact Eventually.done _ ⟨hpc'.trans hret, UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl), hdm, hsv⟩

/-- **The failure path** at `.LVerifyExecution_10`: X0 zero. -/
theorem fail (hp : Placed code k) (g : Geo a m0) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b20Offset)) : Eventually (step1 Host.exe) (Done a m0 none) st := by
  obtain ⟨hwf, hm⟩ := h.env g
  refine exec_at (hb20 hp) run_b20 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hk := call_keeps b20 (by simp)
  rw [after_eq run_b20] at hk
  obtain ⟨h1, -⟩ := h.block g hm1 hk.1 hk.2
  have hx0 : st1.data.regs.X0 = 0 := UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl)
  refine Eventually.mono (exitRet hp g h1 hpc1) fun st' ⟨h1', h2', h3', h4'⟩ ↦
    ⟨h1', (by rw [h2', hx0]; rfl), fun _ _ h ↦ (by cases h), fun q hq ↦ ?_, h4'⟩
  rw [h3']
  exact h1.body.same q hq

/-- **The branch after a call** that returned `okWord b` in X0: to `fail` (the walk's result
`none`) when `b` is false, else on with the registers, memory and body kept. -/
theorem branch (hp : Placed code k) (g : Geo a m0) {ds : List Directive} {j : Nat} {S₁ : SState}
    {c : SBool} (hk : ds.IsInfixAt Host.prog (k + j))
    (hrun : exec ds callS = some (S₁, .cond c NativeRustcVmArm.Vm.VerifyExecution.label_10))
    (hkeep : S₁.regs = callS.regs ∧ S₁.sp = callS.sp ∧ S₁.mem = [])
    (hkept : keepsRegs callS S₁ kept = true) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + j)) {b : Bool} (hc : c.eval (envOf m0 st.data) = !b)
    {r : Option (Unit × TState)} (hnone : b = false → r = none)
    (cont : b = true → ∀ st' : MachineState, At m0 st'.data →
      (∀ x, st'.data.regs.getXReg x = st.data.regs.getXReg x) → st'.data.dmem = st.data.dmem →
      st'.pc = Host.addrOf (k + j + ds.length) → Eventually (step1 Host.exe) (Done a m0 r) st') :
    Eventually (step1 Host.exe) (Done a m0 r) st := by
  obtain ⟨hwf, hm⟩ := h.env g
  refine exec_at hk hrun hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨h1, hd1⟩ := h.block g hm1 hkept hkeep.2.2
  have hregs : ∀ x, st1.data.regs.getXReg x = st.data.regs.getXReg x := fun x ↦ by
    have hs : ∃ v, callS.reg x = some v := by cases x <;> exact ⟨_, rfl⟩
    obtain ⟨v, hv⟩ := hs
    exact Match.reg_eq hm hm1 hv (by rw [SState.reg, hkeep.1]; exact hv)
  simp only [PcOk, hc] at hpc1
  cases b with
  | false =>
    rw [hnone rfl]
    simp only [Bool.not_false, ite_true, lbl_10 hp] at hpc1
    exact fail hp g h1 hpc1
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hpc1
    exact cont rfl st1 h1 hregs hd1 hpc1

end

end NativeRustcVmArm.Top.VerifyExecution
