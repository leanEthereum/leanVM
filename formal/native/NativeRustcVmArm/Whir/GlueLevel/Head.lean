module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Whir.GlueLevel.Basic

/-!
# `glue_level` up to its first store

`b0` saves the registers and `μ` in the frame, loads the claim and the batched value, and calls
`EW::mul` for `λ · oodValue`; `b1` adds the claim and calls it for `λ²`; `b2` calls it for
`λ² · batched`. At `b3` (`AtB3`): the claim plus `λ · oodValue`, `λ²` and `λ² · batched` in
registers, the arguments `b4` passes on in callee-saved registers, memory changed in the stack only.
-/

namespace NativeRustcVmArm.Whir.GlueLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.GlueLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- **At `b3`**, after the three products. -/
structure AtB3 (s : WhirStateW) (m0 m : MachineData) : Prop where
  fr : FR m0 m
  so : SO m0 m
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  x26 : m.regs.getXReg .X26 = m0.regs.X1
  x25 : m.regs.getXReg .X25 = m0.regs.X2
  x22 : m.regs.getXReg .X22 = m0.regs.X4
  x21 : m.regs.getXReg .X21 = m0.regs.X5
  claim1 : (⟨m.regs.getXReg .X29, m.regs.getXReg .X20⟩ : EW) = s.claim + lamOf m0 * oodOf m0
  l2 : (⟨m.regs.getXReg .X23, m.regs.getXReg .X24⟩ : EW) = lamOf m0 * lamOf m0
  c2 : (⟨m.regs.X0, m.regs.X1⟩ : EW) = lamOf m0 * lamOf m0 * batOf m0

end

public section

theorem ew_add_comm (a b : EW) : (⟨b.c0 ^^^ a.c0, b.c1 ^^^ a.c1⟩ : EW) = a + b := by
  show (⟨b.c0 ^^^ a.c0, b.c1 ^^^ a.c1⟩ : EW) = ⟨a.c0 ^^^ b.c0, a.c1 ^^^ b.c1⟩
  rw [UInt64.xor_comm b.c0, UInt64.xor_comm b.c1]

variable [Host] {k : Nat} {s : WhirStateW} {m0 : MachineData}

/-- **From the entry to `b3`.** -/
theorem head_step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hpre : GlueLevelPre s m0) {R : MachineState → Prop}
    (cont : ∀ m, AtB3 s m0 m → Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b3Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.GlueLevel.b0Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hstk, hst, -, -, -, -, -, hargs, hpin, -, -, -, hapA, -, -, -⟩ := hpre'
  have hSP : 704 ≤ m0.regs.SP.toNat := hstk.2.1
  have hSPb : m0.regs.SP.toNat = m0.regs.SP.toBitVec.toNat := rfl
  let p := pOf m0
  have hfnw : NoWrap (base m0 112) 112 := Ring.base_noWrap (by omega)
  have hbt : (base m0 112).toNat = m0.regs.SP.toNat - 112 := Ring.base_toNat (by omega)
  have hsbt : (stackBelow m0 glueLevelStack).toNat = m0.regs.SP.toNat - 704 :=
    Ring.base_toNat hstk.2.1
  have hpap : Apart p stateBytes (stackBelow m0 glueLevelStack) glueLevelStack := hpin.2
  have hsB : stateBytes = 61152 := rfl
  let env := Env.ofMachine m0 [(base m0 112, 112), (m0.regs.SP.toBitVec, 48), (p, 512)]
  have hwf : env.WF := by
    refine Env.wf_of ⟨⟨Ring.frame_mapped hstk (by decide), hfnw⟩, ⟨hargs.1, hargs.2⟩,
      ⟨NativeRustcVm.Mapped.mono (m := 512) hpin.1.1 (by decide),
        NativeRustcVm.NoWrap.mono (m := 512) hpin.1.2 (by decide)⟩, trivial⟩ (pairwise3 ?_ ?_ ?_)
    · exact Or.inl (by show (base m0 112).toNat + 112 ≤ m0.regs.SP.toBitVec.toNat; omega)
    · show (base m0 112).toNat + 112 ≤ p.toNat ∨ p.toNat + 512 ≤ (base m0 112).toNat
      unfold Apart at hpap
      rw [hsbt, glueLevelStack_eq, hsB] at hpap
      omega
    · show m0.regs.SP.toBitVec.toNat + 48 ≤ m0.regs.X0.toBitVec.toNat ∨
        m0.regs.X0.toBitVec.toNat + 512 ≤ m0.regs.SP.toBitVec.toNat
      unfold Apart at hapA
      rw [hsB] at hapA
      omega
  have hm : Match env entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, rfl,
        fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩
      (by simp [Sym.eval, base])
      ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial trivial
      ⟨by
          show base m0 112 + BitVec.ofInt 64 144 = m0.regs.SP.toBitVec + BitVec.ofInt 64 32
          simp only [base]; bv_omega,
        by
          show base m0 112 + BitVec.ofInt 64 152 = m0.regs.SP.toBitVec + BitVec.ofInt 64 40
          simp only [base]; bv_omega, trivial⟩
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GlueLevel.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  -- the claim and the batched value, as `b0` loads them
  have hc0 : env.load 2 0 8 = s.claim.c0.toBitVec :=
    Ring.load_word (by
      show NativeRustcVm.WordAt m0.dmem (p + BitVec.ofNat 64 0) s.claim.c0
      rw [NativeRustcVm.addr_add_zero]
      exact (NativeRustcVm.ewAt_iff.mp hst.claim).1)
  have hc1 : env.load 2 8 8 = s.claim.c1.toBitVec :=
    Ring.load_word (NativeRustcVm.ewAt_iff.mp hst.claim).2
  have hb0 : env.load 1 32 8 = (whirStackArg m0 4).toBitVec := Ring.load_eq_wordOf env 1 32
  have hb1 : env.load 1 40 8 = (whirStackArg m0 5).toBitVec := Ring.load_eq_wordOf env 1 40
  refine exec_then hk0 run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : FR m0 st1.data :=
    Ring.Fr.ofPrologue hstk.2.1 (by decide) hm1 hwf rfl (by decide) slots_le (by decide)
      (by simp)
  have hso1 : SO m0 st1.data := by
    have := same_region hm1 hwf (r := 0) rfl (by decide)
    exact fun q hq ↦ this q fun h ↦ hq (frame_in_stack hpre h)
  have e1x0 : st1.data.regs.X0 = m0.regs.X1 := (rv hm1 (r := .X0) rfl).trans rfl
  have e1x1 : st1.data.regs.X1 = m0.regs.X2 := (rv hm1 (r := .X1) rfl).trans rfl
  have e1x2 : st1.data.regs.X2 = m0.regs.X6 := (rv hm1 (r := .X2) rfl).trans rfl
  have e1x3 : st1.data.regs.X3 = m0.regs.X7 := (rv hm1 (r := .X3) rfl).trans rfl
  have e1x19 : st1.data.regs.getXReg .X19 = m0.regs.X0 := (rv hm1 (r := .X19) rfl).trans (by
    simp [Sym.eval, env, p])
  have e1x21 : st1.data.regs.getXReg .X21 = m0.regs.X5 := (rv hm1 (r := .X21) rfl).trans rfl
  have e1x22 : st1.data.regs.getXReg .X22 = m0.regs.X4 := (rv hm1 (r := .X22) rfl).trans rfl
  have e1x23 : st1.data.regs.getXReg .X23 = s.claim.c0 :=
    (rv hm1 (r := .X23) rfl).trans (by simp only [Sym.eval]; rw [hc0])
  have e1x24 : st1.data.regs.getXReg .X24 = s.claim.c1 :=
    (rv hm1 (r := .X24) rfl).trans (by simp only [Sym.eval]; rw [hc1])
  have e1x25 : st1.data.regs.getXReg .X25 = m0.regs.X2 := (rv hm1 (r := .X25) rfl).trans rfl
  have e1x26 : st1.data.regs.getXReg .X26 = m0.regs.X1 := (rv hm1 (r := .X26) rfl).trans rfl
  have e1x27 : st1.data.regs.getXReg .X27 = whirStackArg m0 4 :=
    (rv hm1 (r := .X27) rfl).trans (by simp only [Sym.eval]; rw [hb0])
  have e1x28 : st1.data.regs.getXReg .X28 = whirStackArg m0 5 :=
    (rv hm1 (r := .X28) rfl).trans (by simp only [Sym.eval]; rw [hb1])
  -- `λ · oodValue`
  refine mul_call hmul hpre hfr1 hso1 hpc1 fun m2 hfr2 hso2 hq2 ↦ ?_
  have hs2 := hq2.2.2.2.1
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GlueLevel.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk1 run_b1 (Env.wf_nil m2) (match_nil m2) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hfr3, hso3, -⟩ := reg_block hfr2 hso2 hm3 rfl rfl
  have e3x0 : st3.data.regs.X0 = m0.regs.X1 := by
    refine (rv hm3 (r := .X0) rfl).trans ?_
    show m2.regs.getXReg .X26 = _
    rw [hs2 .X26 rfl, e1x26]
  have e3x1 : st3.data.regs.X1 = m0.regs.X2 := by
    refine (rv hm3 (r := .X1) rfl).trans ?_
    show m2.regs.getXReg .X25 = _
    rw [hs2 .X25 rfl, e1x25]
  have e3x2 : st3.data.regs.X2 = m0.regs.X1 := by
    refine (rv hm3 (r := .X2) rfl).trans ?_
    show m2.regs.getXReg .X26 = _
    rw [hs2 .X26 rfl, e1x26]
  have e3x3 : st3.data.regs.X3 = m0.regs.X2 := by
    refine (rv hm3 (r := .X3) rfl).trans ?_
    show m2.regs.getXReg .X25 = _
    rw [hs2 .X25 rfl, e1x25]
  have e3c1 : (⟨st3.data.regs.getXReg .X29, st3.data.regs.getXReg .X20⟩ : EW) =
      s.claim + lamOf m0 * oodOf m0 := by
    rw [rv hm3 (r := .X29) rfl, rv hm3 (r := .X20) rfl]
    sym_simp
    simp only [Env.ofMachine_regs]
    rw [hs2 .X23 rfl, hs2 .X24 rfl, e1x23, e1x24]
    refine Eq.trans ?_ (ew_add_comm s.claim (lamOf m0 * oodOf m0))
    rw [show m2.regs.getXReg .X0 = (lamOf m0 * oodOf m0).c0 by
        rw [show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, hq2.1, e1x0, e1x1, e1x2, e1x3]; rfl,
      show m2.regs.getXReg .X1 = (lamOf m0 * oodOf m0).c1 by
        rw [show m2.regs.getXReg .X1 = m2.regs.X1 from rfl, hq2.2.1, e1x0, e1x1, e1x2, e1x3]; rfl]
    rfl
  -- `λ²`
  refine mul_call hmul hpre hfr3 hso3 hpc3 fun m4 hfr4 hso4 hq4 ↦ ?_
  have hs4 := hq4.2.2.2.1
  have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GlueLevel.b2Offset) := b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk2 run_b2 (Env.wf_nil m4) (match_nil m4) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hfr5, hso5, -⟩ := reg_block hfr4 hso4 hm5 rfl rfl
  have hl2 : (⟨m4.regs.X0, m4.regs.X1⟩ : EW) = lamOf m0 * lamOf m0 := by
    rw [hq4.1, hq4.2.1, e3x0, e3x1, e3x2, e3x3]
    rfl
  have e5x0 : st5.data.regs.X0 = m4.regs.X0 := (rv hm5 (r := .X0) rfl).trans rfl
  have e5x1 : st5.data.regs.X1 = m4.regs.X1 := (rv hm5 (r := .X1) rfl).trans rfl
  have e5x2 : st5.data.regs.X2 = whirStackArg m0 4 := by
    refine (rv hm5 (r := .X2) rfl).trans ?_
    show m4.regs.getXReg .X27 = _
    rw [hs4 .X27 rfl, show st3.data.regs.getXReg .X27 = m2.regs.getXReg .X27 from
      (rv hm3 (r := .X27) rfl).trans rfl, hs2 .X27 rfl, e1x27]
  have e5x3 : st5.data.regs.X3 = whirStackArg m0 5 := by
    refine (rv hm5 (r := .X3) rfl).trans ?_
    show m4.regs.getXReg .X28 = _
    rw [hs4 .X28 rfl, show st3.data.regs.getXReg .X28 = m2.regs.getXReg .X28 from
      (rv hm3 (r := .X28) rfl).trans rfl, hs2 .X28 rfl, e1x28]
  have e5x23 : st5.data.regs.getXReg .X23 = m4.regs.X0 := (rv hm5 (r := .X23) rfl).trans rfl
  have e5x24 : st5.data.regs.getXReg .X24 = m4.regs.X1 := (rv hm5 (r := .X24) rfl).trans rfl
  -- `λ² · batched`
  refine mul_call hmul hpre hfr5 hso5 hpc5 fun m6 hfr6 hso6 hq6 ↦ cont m6 ?_
  have hs6 := hq6.2.2.2.1
  -- the callee-saved registers `b1`, `b2` keep
  have k3 : ∀ r, (after b1 regS).reg r = some (.reg r) →
      st3.data.regs.getXReg r = m2.regs.getXReg r := fun r h ↦
    (rv hm3 (by rw [← after_eq run_b1]; exact h)).trans rfl
  have k5 : ∀ r, (after b2 regS).reg r = some (.reg r) →
      st5.data.regs.getXReg r = m4.regs.getXReg r := fun r h ↦
    (rv hm5 (by rw [← after_eq run_b2]; exact h)).trans rfl
  have chain : ∀ r, calleeSaved r = true → (after b1 regS).reg r = some (.reg r) →
      (after b2 regS).reg r = some (.reg r) → m6.regs.getXReg r = st1.data.regs.getXReg r :=
    fun r hc h1 h2 ↦ by
      rw [hs6 r hc, k5 r h2, hq4.2.2.2.1 r hc, k3 r h1, hs2 r hc]
  refine ⟨hfr6, hso6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [chain .X19 rfl rfl rfl, e1x19]
  · rw [chain .X26 rfl rfl rfl, e1x26]
  · rw [chain .X25 rfl rfl rfl, e1x25]
  · rw [chain .X22 rfl rfl rfl, e1x22]
  · rw [chain .X21 rfl rfl rfl, e1x21]
  · rw [hs6 .X29 rfl, k5 .X29 rfl, hs4 .X29 rfl, hs6 .X20 rfl, k5 .X20 rfl, hs4 .X20 rfl]
    exact e3c1
  · rw [hs6 .X23 rfl, hs6 .X24 rfl, e5x23, e5x24]
    exact hl2
  · rw [hq6.1, hq6.2.1, e5x0, e5x1, e5x2, e5x3]
    show EW.mul ⟨m4.regs.X0, m4.regs.X1⟩ (batOf m0) = _
    rw [hl2]
    rfl

end

end NativeRustcVmArm.Whir.GlueLevel
