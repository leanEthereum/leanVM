module

public import NativeRustcVmArm.Code.Vm.OpenPhase.Names
public import NativeRustcVmArm.Sumcheck.OpenPhase.Check

/-!
# `open_phase`'s entry

`b0` saves the registers and loads the phase's count, height and width; `b1` to `b5` check the
shape and the count (`check_spec`): the exit with `None`, or `.L5` and the positions
(`b6_spec`).
-/

namespace NativeRustcVmArm.Sumcheck.OpenPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.OpenPhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck
open LeanVM.Protocol LeanVM.Protocol.Compile NativeVm

public section

variable [Host] {P : Array OpeningW} {R : Digest} {Q : Array UInt64} {m0 : MachineData} {k : Nat}

/-- **A test block of the frame**: no writes, every register kept. -/
theorem frTest (hpre : OpenPhasePre P R Q m0) {m : MachineData} (hf : FrO m0 m)
    {ds : List Directive} {S' : SState} {x : Exit} {j : Nat} (hk : ds.IsInfixAt Host.prog j)
    (hx : exec ds frS = some (S', x)) (hmem : S'.mem = []) (hsp : S'.sp = .ptr 0 0)
    (hregs : ∀ r, S'.reg r = some (.reg r)) {Rs : MachineState → Prop}
    (cont : ∀ st : MachineState, FrO m0 st.data →
      (∀ r, st.data.regs.getXReg r = m.regs.getXReg r) →
      PcOk (Env.ofMachine m [(base m0 176, 176)]) x (Host.addrOf (j + ds.length)) st →
      Eventually (step1 Host.exe) Rs st) :
    Eventually (step1 Host.exe) Rs ⟨m, Host.addrOf j⟩ := by
  have hS := hpre.1
  have hwf := Bus.wf_frame (F := 176) hS (by decide) hf.kept
  have hm := Bus.match_frame hS (F := 176) (by decide) (by decide) hf.sp
  refine exec_then hk hx hwf hm fun st hm' hpc ↦ cont st ?_ ?_ hpc
  · exact Fr.ofBlock hf hm hm' hwf rfl hmem (by rw [hsp]; rfl) fun r hr ↦ nomatch hr
  · exact fun r ↦ UInt64.toBitVec_inj.mp ((hm'.regs r _ (hregs r)).trans rfl)

/-- **The entry**: the exit with `None`, or `.L8` with the checks passed. -/
theorem check_spec (hp : Placed code k) (hpre : OpenPhasePre P R Q m0) {h w : Nat}
    (hph : PhaseHW m0.dmem (phO m0) P h w) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = retOf m0 ∧ OpenPhasePost P R Q m0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b10Offset) ∧ Checked m0 P Q h w st.data))
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b0Offset)⟩ := by
  have hS := hpre.1
  have hN' := hN hpre
  obtain ⟨-, -, -, -, hqn, -, hmp, hnwp, -, -, -, -, haps, -⟩ := id hpre
  have hpw : phaseWords = 49411 := rfl
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b0Offset) := b0_in_code.trans hp.1 (by simp [b0])
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b1Offset) := b1_in_code.trans hp.1 (by simp [b1])
  have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b2Offset) := b2_in_code.trans hp.1 (by simp [b2])
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b3Offset) := b3_in_code.trans hp.1 (by simp [b3])
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b4Offset) := b4_in_code.trans hp.1 (by simp [b4])
  have hk5 : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b5Offset) := b5_in_code.trans hp.1 (by simp [b5])
  have hl4 : Labels.label NativeRustcVmArm.Vm.OpenPhase.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b5Offset) := hp.label (j := NativeRustcVmArm.Vm.OpenPhase.b5Offset) NativeRustcVmArm.Vm.OpenPhase.label_4_at
  have hl5 : Labels.label NativeRustcVmArm.Vm.OpenPhase.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b6Offset) := hp.label (j := NativeRustcVmArm.Vm.OpenPhase.b6Offset) NativeRustcVmArm.Vm.OpenPhase.label_5_at
  have hl18 : Labels.label NativeRustcVmArm.Vm.OpenPhase.label_18 = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b22Offset) := hp.label (j := NativeRustcVmArm.Vm.OpenPhase.b22Offset) NativeRustcVmArm.Vm.OpenPhase.label_18_at
  have hmq : wireMaxQueries = 256 := rfl
  have hml : wireMaxLeafWords = 64 := rfl
  have hmh : wireMaxHeight = 32 := rfl
  obtain ⟨hh, hw, hsz, hc0, hc8, hc16, -⟩ := id hph
  rw [hpw] at hmp hnwp haps
  have hwf : (Env.ofMachine m0 [(base m0 176, 176), (phO m0, 24)]).WF :=
    Bus.wf_frame2 hS (by decide) (fun _ h ↦ h)
      ⟨NativeRustcVm.Mapped.mono hmp (by omega), NativeRustcVm.NoWrap.mono hnwp (by omega)⟩
      (show Apart m0.regs.X6.toBitVec 24 (stackBelow m0 openPhaseStack) openPhaseStack from by
        unfold Apart at haps ⊢; omega)
  have hm : Match (Env.ofMachine m0 [(base m0 176, 176), (phO m0, 24)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ Bus.base_aligned hS (by decide) (by decide), rfl, nofun,
        trivial⟩ (Bus.env0_sp [(phO m0, 24)])
      ⟨by show (m0.regs.getXReg .X6).toBitVec = _; simp [Sym.eval, Env.base, Env.ofMachine]; rfl,
        trivial⟩ trivial trivial trivial
  have hb1 : (Env.ofMachine m0 [(base m0 176, 176), (phO m0, 24)]).base 1 = phO m0 := rfl
  have hld0 : (Env.ofMachine m0 [(base m0 176, 176), (phO m0, 24)]).load 1 0 8 =
      P.size.toUInt64.toBitVec := load_word (by rw [hb1, NativeRustcVm.addr_add_zero]; exact hc0)
  have hld8 : (Env.ofMachine m0 [(base m0 176, 176), (phO m0, 24)]).load 1 8 8 =
      h.toUInt64.toBitVec := load_word (by rw [hb1]; exact hc8)
  have hld16 : (Env.ofMachine m0 [(base m0 176, 176), (phO m0, 24)]).load 1 16 8 =
      w.toUInt64.toBitVec := load_word (by rw [hb1]; exact hc16)
  refine exec_then hk0 run_b0 hwf hm fun st hm' hpc ↦ ?_
  have hfr : FrO m0 st.data :=
    Fr.ofPrologue (F := 176) (rs := [(phO m0, 24)]) hN' (by decide) hm' hwf rfl
      (by decide +kernel) (by decide) (by decide +kernel)
      (fun r hr ↦ nomatch hr)
  have hregs : Regs m0 P h w st.data :=
    ⟨UInt64.toBitVec_inj.mp ((hm'.regs .X1 _ rfl).trans rfl),
      UInt64.toBitVec_inj.mp ((hm'.regs .X19 _ rfl).trans rfl),
      UInt64.toBitVec_inj.mp ((hm'.regs .X20 _ rfl).trans
        (by simp [Sym.eval, Env.base, Env.ofMachine])),
      UInt64.toBitVec_inj.mp ((hm'.regs .X21 _ rfl).trans hld16),
      UInt64.toBitVec_inj.mp ((hm'.regs .X22 _ rfl).trans hld8),
      UInt64.toBitVec_inj.mp ((hm'.regs .X23 _ rfl).trans hld0)⟩
  have hkeep : ∀ r, r = .X2 ∨ r = .X3 ∨ r = .X4 ∨ r = .X5 →
      st.data.regs.getXReg r = m0.regs.getXReg r := by
    rintro r (rfl | rfl | rfl | rfl) <;> exact UInt64.toBitVec_inj.mp ((hm'.regs _ _ rfl).trans rfl)
  have hsz64 : P.size < 2 ^ 64 := by omega
  have hc : (SBool.cmp CmpOp.eq RegWidth.W64 (.load 1 0 8) (.lit 0)).eval
      (Env.ofMachine m0 [(base m0 176, 176), (phO m0, 24)]) = (P.size == 0) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
    rw [hld0]
    exact toUInt64_eq_iff hsz64 0
  simp only [PcOk] at hpc
  rw [hc] at hpc
  -- Regs, after a test block.
  have regsT : ∀ {m m' : MachineData}, Regs m0 P h w m →
      (∀ r, m'.regs.getXReg r = m.regs.getXReg r) → Regs m0 P h w m' :=
    fun ⟨a1, a19, a20, a21, a22, a23⟩ he ↦ ⟨(he _).trans a1, (he _).trans a19, (he _).trans a20,
      (he _).trans a21, (he _).trans a22, (he _).trans a23⟩
  have fail : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b22Offset) → FrO m0 st.data →
      Regs m0 P h w st.data →
      openPhase R m0.regs.X2.toNat m0.regs.X3.toNat Q P = none →
      Eventually (step1 Host.exe) (fun st ↦ (st.pc = retOf m0 ∧ OpenPhasePost P R Q m0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b10Offset) ∧ Checked m0 P Q h w st.data)) st := by
    intro st hpc hf hr hn
    obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    exact Eventually.mono (exit_fail hp hpre hf hr.x19 hn) fun st h ↦ .inl h
  have toL5 : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b6Offset) → FrO m0 st.data →
      Regs m0 P h w st.data → ShapeOk P Q h w m0.regs.X2.toNat m0.regs.X3.toNat →
      (∀ r, r = .X2 ∨ r = .X3 ∨ r = .X4 ∨ r = .X5 →
        st.data.regs.getXReg r = m0.regs.getXReg r) →
      Eventually (step1 Host.exe) (fun st ↦ (st.pc = retOf m0 ∧ OpenPhasePost P R Q m0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b10Offset) ∧ Checked m0 P Q h w st.data)) st := by
    intro st hpc hf hr hsh hk
    obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    exact b6_spec hp hpre hph hf hr hsh
      (hk .X4 (by simp)) (hk .X5 (by simp))
  have hph' : PhaseHW m0.dmem (phO m0) P h w := hph
  have hX5 : Q.size = (m0.regs.getXReg .X5).toBitVec.toNat := hqn
  have hX5' : Q.size = (m0.regs.getXReg .X5).toNat := hqn
  by_cases h0 : P.size = 0
  · -- No opening: `.L4`, the positions must be none too.
    simp only [h0, beq_self_eq_true, ↓reduceIte] at hpc
    have hpc4 : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b5Offset) := hpc.trans hl4
    obtain ⟨d, pc⟩ := st
    simp only at hpc4
    subst hpc4
    refine frTest hpre hfr hk5 run_b5 rfl rfl (fun r ↦ by cases r <;> rfl)
      fun st1 hf1 he1 hpc1 ↦ ?_
    have hc5 : ((SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X5) (.lit 0)).not.eval
        (Env.ofMachine d [(base m0 176, 176)])) = !(Q.size == 0) := by
      simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
      show (!((d.regs.getXReg .X5).toBitVec == 0#64)) = _
      rw [hkeep .X5 (by simp)]
      have e : ((m0.regs.getXReg .X5).toBitVec == 0#64) =
          ((m0.regs.getXReg .X5).toBitVec.toNat == 0) := by
        by_cases hz : (m0.regs.getXReg .X5).toBitVec = 0#64
        · simp [hz]
        · have : (m0.regs.getXReg .X5).toBitVec.toNat ≠ 0 := fun h' ↦
            hz (BitVec.eq_of_toNat_eq (by simpa using h'))
          simp [hz]; exact this
      rw [e, ← hX5]
    simp only [PcOk] at hpc1
    rw [hc5] at hpc1
    by_cases hq0 : Q.size = 0
    · simp only [hq0, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
      exact toL5 st1 hpc1 hf1 (regsT hregs he1) ⟨.inl h0, by omega⟩
        fun r hr ↦ (he1 r).trans (hkeep r hr)
    · simp only [show (Q.size == 0) = false by simpa using hq0, Bool.not_false, ↓reduceIte]
        at hpc1
      exact fail st1 (hpc1.trans hl18) hf1 (regsT hregs he1)
        (openPhase_none hph' fun ⟨_, hs, _⟩ ↦ hq0 (by omega))
  · simp only [show (P.size == 0) = false by simpa using h0, Bool.false_eq_true, ↓reduceIte]
      at hpc
    have hd := fun (r : XReg) ↦ (rfl : r = r)
    obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    -- `b1`: the width.
    refine frTest hpre hfr hk1 run_b1 rfl rfl (fun r ↦ by cases r <;> rfl)
      fun st1 hf1 he1 hpc1 ↦ ?_
    have hw64 : w < 2 ^ 64 := by omega
    have hh64 : h < 2 ^ 64 := by omega
    have hc1 : ((SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X21) (.reg .X3)).not.eval
        (Env.ofMachine d [(base m0 176, 176)])) = !(w == m0.regs.X3.toNat) := by
      simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
      show (!((d.regs.getXReg .X21).toBitVec == (d.regs.getXReg .X3).toBitVec)) = _
      rw [hregs.x21, hkeep .X3 (by simp), toUInt64_eq_iff hw64]
      rfl
    simp only [PcOk] at hpc1
    rw [hc1] at hpc1
    by_cases hwW : w = m0.regs.X3.toNat
    · simp only [hwW, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
      obtain ⟨d1, pc1⟩ := st1
      simp only at hpc1
      subst hpc1
      -- `b2`: the count.
      refine frTest hpre hf1 hk2 run_b2 rfl rfl (fun r ↦ by cases r <;> rfl)
        fun st2 hf2 he2 hpc2 ↦ ?_
      have hc2 : ((SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X23) (.reg .X5)).not.eval
          (Env.ofMachine d1 [(base m0 176, 176)])) = !(P.size == Q.size) := by
        simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
        show (!((d1.regs.getXReg .X23).toBitVec == (d1.regs.getXReg .X5).toBitVec)) = _
        rw [he1, he1, hregs.x23, hkeep .X5 (by simp), toUInt64_eq_iff hsz64, ← hX5']
      simp only [PcOk] at hpc2
      rw [hc2] at hpc2
      by_cases hPQ : P.size = Q.size
      · simp only [hPQ, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc2
        obtain ⟨d2, pc2⟩ := st2
        simp only at hpc2
        subst hpc2
        -- `b3`: the height.
        refine frTest hpre hf2 hk3 run_b3 rfl rfl (fun r ↦ by cases r <;> rfl)
          fun st3 hf3 he3 hpc3 ↦ ?_
        have hc3 : ((SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X22) (.reg .X2)).eval
            (Env.ofMachine d2 [(base m0 176, 176)])) = (h == m0.regs.X2.toNat) := by
          simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
          show ((d2.regs.getXReg .X22).toBitVec == (d2.regs.getXReg .X2).toBitVec) = _
          rw [he2, he2, he1, he1, hregs.x22, hkeep .X2 (by simp), toUInt64_eq_iff hh64]
          rfl
        simp only [PcOk] at hpc3
        rw [hc3] at hpc3
        have he : ∀ r, st3.data.regs.getXReg r = d.regs.getXReg r := fun r ↦
          (he3 r).trans ((he2 r).trans (he1 r))
        by_cases hhH : h = m0.regs.X2.toNat
        · simp only [hhH, beq_self_eq_true, ↓reduceIte] at hpc3
          exact toL5 st3 (hpc3.trans hl5) hf3 (regsT hregs he) ⟨.inr ⟨hwW, hhH⟩, hPQ⟩
            fun r hr ↦ (he r).trans (hkeep r hr)
        · simp only [show (h == m0.regs.X2.toNat) = false by simpa using hhH,
            Bool.false_eq_true, ↓reduceIte] at hpc3
          obtain ⟨d3, pc3⟩ := st3
          simp only at hpc3
          subst hpc3
          refine frTest hpre hf3 hk4 run_b4 rfl rfl (fun r ↦ by cases r <;> rfl)
            fun st4 hf4 he4 hpc4 ↦ ?_
          exact fail st4 (hpc4.trans hl18) hf4 (regsT hregs fun r ↦ (he4 r).trans (he r))
            (openPhase_none hph' fun ⟨hs, _, _⟩ ↦ hs.elim h0 fun ⟨_, e⟩ ↦ hhH e)
      · simp only [show (P.size == Q.size) = false by simpa using hPQ, Bool.not_false,
          ↓reduceIte] at hpc2
        exact fail st2 (hpc2.trans hl18) hf2 (regsT hregs fun r ↦ (he2 r).trans (he1 r))
          (openPhase_none hph' fun ⟨_, hs, _⟩ ↦ hPQ hs)
    · simp only [show (w == m0.regs.X3.toNat) = false by simpa using hwW, Bool.not_false,
        ↓reduceIte] at hpc1
      exact fail st1 (hpc1.trans hl18) hf1 (regsT hregs he1)
        (openPhase_none hph' fun ⟨hs, _, _⟩ ↦ hs.elim h0 fun ⟨e, _⟩ ↦ hwW e)

end

end NativeRustcVmArm.Sumcheck.OpenPhase
