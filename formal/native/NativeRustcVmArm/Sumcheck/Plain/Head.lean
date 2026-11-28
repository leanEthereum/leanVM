module

public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.Code.Vm.TStateSumcheckRoundPoly.Names
public import NativeRustcVmArm.Sumcheck.Plain.Frame

/-!
# `sumcheck` with `sumcheck_plain`'s closure: a round's polynomial

From the loop's head (`Inv`), `b2` writes `eq = None` and calls `sumcheck_round_poly`; `b3` leaves
for `.L5` on a rejection (`exit_fail`), else at `b4` the polynomial read (`Mid`, `head_spec`).
-/

namespace NativeRustcVmArm.Sumcheck.Plain

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck

@[expose] public section

/-- At `b4`, round `i`'s polynomial `msg` read, the state `s1`, the first `i` challenges `xs`. -/
structure Mid [Labels] (a : DecArea) (s : TState) (m0 : MachineData) (i : Nat) (xs msg : Array EW)
    (s1 : TState) (m : MachineData) : Prop where
  fr : FrP m0 m
  lt : i < nP m0
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  x20 : (m.regs.getXReg .X20).toBitVec = slP m0 + BitVec.ofNat 64 (16 * i)
  x21 : m.regs.getXReg .X21 = m0.regs.X4
  x22 : m.regs.getXReg .X22 = m0.regs.X1
  x23 : (m.regs.getXReg .X23).toBitVec = slP m0 + BitVec.ofNat 64 (16 * nP m0)
  run : (sumcheckFn (claimP m0) (cntP m0) (fun _ ↦ none) (i + 1)).run s =
    some ((xs.push s1.sponge.squeeze.1, polyEval msg s1.sponge.squeeze.1),
      { s1 with sponge := s1.sponge.squeeze.2 })
  xsz : xs.size = i
  xs : NativeRustcVm.EWsAt m.dmem (slP m0) xs.toList
  msz : msg.size = cntP m0
  msg : NativeRustcVm.EWsAt m.dmem (base m0 160 + BitVec.ofNat 64 8) msg.toList
  ts : TStateAt m.dmem (tP m0) a s1

/-- What the loop ends in: the exit (a rejection), or `.L4` after the last round. -/
abbrev Goal [Host] (a : DecArea) (s : TState) (m0 : MachineData) (k : Nat) (st : MachineState) :
    Prop :=
  (st.pc = retOf m0 ∧ SumcheckPlainPost a s m0 st.data) ∨
    (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b7Offset) ∧ Done a s m0 st.data)

end

public section

variable [Host] {a : DecArea} {s : TState} {m0 : MachineData} {k : Nat}

/-- **A round's polynomial**: from the head, a rejection's exit or `b4` with the polynomial. -/
theorem head_spec (hp : Placed code k)
    (hrp : ∀ a s e, Spec (Labels.label NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e))
    (hpre : SumcheckPlainPre a s m0) {i : Nat} {m : MachineData} (hi : Inv a s m0 i m) :
    Eventually (step1 Host.exe)
      (fun st ↦ Goal a s m0 k st ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b4Offset) ∧ ∃ xs msg s1, Mid a s m0 i xs msg s1 st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b2Offset)⟩ := by
  have g := geo hpre
  have hS := hpre.1
  obtain ⟨xs, si, hrun, hsz, hxs, hts⟩ := hi.run
  have hlt := hi.lt
  have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b2Offset) := b2_in_code.trans hp.1 (by simp [b2])
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b3Offset) := b3_in_code.trans hp.1 (by simp [b3])
  have hl5 : Labels.label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b8Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b8Offset) NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.label_5_at
  have hwf2 := Bus.wf_frame (F := 160) hS (by decide) hi.fr.kept
  have hm2 : Match (Env.ofMachine m [(base m0 160, 160)]) frS m :=
    Bus.match_frame hS (by decide) (by decide) hi.fr.sp
  refine exec_then hk2 run_b2 hwf2 hm2 fun st2 hm2' hpc2 ↦ ?_
  have hm2A : Match (Env.ofMachine m [(base m0 160, 160)]) (after b2 frS) st2.data := by
    rw [after_eq run_b2]; exact hm2'
  have hW2 : ∀ w ∈ (after b2 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 160 ∧
      ∀ p ∈ slotsP, w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off := by
    rw [after_eq run_b2]; decide +kernel
  have hfr2 : FrP m0 st2.data :=
    Bus.Fr.block hi.fr g.hN (by decide) hm2A hwf2 (by rw [after_eq run_b2]) hW2
      (by rw [after_eq run_b2]; decide +kernel) slotsP8
  have hWr2 : ∀ q, Written (Env.ofMachine m [(base m0 160, 160)]) (after b2 frS) q →
      InRange (stackBelow m0 sumcheckPlainStack) sumcheckPlainStack q := fun q hq ↦
    g.ctx.inRange_frame (Written.inRange rfl (base_noWrap (le_trans (by decide) g.hN))
      (fun w hw ↦ ⟨(hW2 w hw).1, (hW2 w hw).2.1⟩) hq)
  have hs2 := hm2A.sameOutside hwf2
  have hts2 : TStateAt st2.data.dmem (tP m0) a si :=
    g.t_keep hs2 (hm2A.kept hwf2) (fun q hq ↦ .inl (hWr2 q hq)) hts
  have hxs2 : NativeRustcVm.EWsAt st2.data.dmem (slP m0) xs.toList :=
    g.sl_keep hs2 (fun q hq ↦ .inl (hWr2 q hq)) (by simp [hsz]; omega) hxs
  have heq2 : OptEWAt st2.data.dmem (base m0 160 + BitVec.ofNat 64 88) none :=
    NativeRustcVmArm.Sumcheck.Match.wordAt_write hm2' (r := 0) (o := 88) rfl (by decide)
      (v := .lit 0) (by decide +kernel)
  have hx0 : st2.data.regs.X0.toBitVec = tP m0 :=
    (hm2'.regs .X0 _ rfl).trans (congrArg UInt64.toBitVec hi.x22)
  have hx1 : st2.data.regs.X1 = m0.regs.X4 :=
    UInt64.toBitVec_inj.mp ((hm2'.regs .X1 _ rfl).trans (congrArg UInt64.toBitVec hi.x21))
  have hx2 : st2.data.regs.X2 = m.regs.X2 := UInt64.toBitVec_inj.mp ((hm2'.regs .X2 _ rfl).trans rfl)
  have hx3 : st2.data.regs.X3 = m.regs.X3 := UInt64.toBitVec_inj.mp ((hm2'.regs .X3 _ rfl).trans rfl)
  have hx4 : st2.data.regs.X4.toBitVec = base m0 160 + BitVec.ofNat 64 88 := by
    rw [show st2.data.regs.X4 = st2.data.regs.getXReg .X4 from rfl, hm2'.regs .X4 _ rfl]
    simp [Sym.eval, Env.base, Env.ofMachine]
  have hx5 : st2.data.regs.X5.toBitVec = base m0 160 + BitVec.ofNat 64 8 := by
    rw [show st2.data.regs.X5 = st2.data.regs.getXReg .X5 from rfl, hm2'.regs .X5 _ rfl]
    simp [Sym.eval, Env.base, Env.ofMachine]
  have hreg2 : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 →
      st2.data.regs.getXReg r = m.regs.getXReg r := by
    rintro r (rfl | rfl | rfl | rfl | rfl) <;>
      exact UInt64.toBitVec_inj.mp ((hm2'.regs _ _ rfl).trans rfl)
  refine call_then hpc2 (hrp a si none)
    (g.roundPolyPre hfr2 hts2 heq2 hx0 (by rw [hx1]) hx4 hx5) fun st3 hpc3 hpost3 ↦ ?_
  obtain ⟨hfr3, hmsg3, hsl3⟩ := g.afterRoundPoly hfr2 hpost3 hx0 hx5 keepP_saved
  have hok3 := hpost3.1
  have hsv3 := hpost3.2.2.2.2
  rw [hx1, hx2, hx3] at hok3 hmsg3
  have hreg3 : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 →
      st3.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    (hsv3.1 r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (hreg2 r hr)
  have hwf3 := Bus.wf_frame (F := 160) hS (by decide) hfr3.kept
  have hm3 : Match (Env.ofMachine st3.data [(base m0 160, 160)]) frS st3.data :=
    Bus.match_frame hS (by decide) (by decide) hfr3.sp
  refine exec_at hk3 run_b3 hwf3 hpc3 hm3 fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hfr4, hd4⟩ := frBlock hfr3 hS (by decide) (by decide) hm4 rfl rfl (by decide)
    (by decide)
  have hreg4 : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 →
      st4.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr
    refine Eq.trans ?_ (hreg3 r hr)
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact UInt64.toBitVec_inj.mp ((hm4.regs _ _ rfl).trans rfl)
  have hX0 : (Env.ofMachine st3.data [(base m0 160, 160)]).regs .X0 =
      st3.data.regs.X0.toBitVec := rfl
  simp only [PcOk, SBool.eval, Sym.eval, hX0, getLsbD_low_zero] at hpc4
  cases hr : (sumcheckRoundPoly (cntP m0) ⟨m.regs.X2, m.regs.X3⟩ none).run si with
  | none =>
    rw [hr] at hok3
    have hpc : st4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b8Offset) := by
      rw [hpc4, hok3]; simp [okWord, hl5]
    have hnone := sumcheckFn_run_none_le (sumcheckFn_run_succ_none hrun hr)
      (show i + 1 ≤ nP m0 by omega)
    obtain ⟨d4, pc4⟩ := st4
    simp only at hpc
    subst hpc
    exact Eventually.mono (exit_fail hp hpre hfr4
      (by rw [hreg4 .X19 (.inl rfl)]; exact hi.x19) hnone) fun st h ↦ .inl (.inl h)
  | some p =>
    obtain ⟨msg, s1⟩ := p
    rw [hr] at hok3
    have hpc : st4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b4Offset) := by
      rw [hpc4, hok3]; simp [okWord]; rfl
    obtain ⟨hmsg, hts3⟩ := hmsg3 msg s1 hr
    refine Eventually.done _ (.inr ⟨hpc, xs, msg, s1, hfr4, hlt, ?_, ?_, ?_, ?_, ?_,
      sumcheckFn_run_succ_some hrun hr, hsz, ?_, roundPoly_size g.ok.2.2.2.2.1 hr, ?_, ?_⟩)
    · rw [hreg4 .X19 (.inl rfl)]; exact hi.x19
    · rw [hreg4 .X20 (.inr (.inl rfl))]; exact hi.x20
    · rw [hreg4 .X21 (.inr (.inr (.inl rfl)))]; exact hi.x21
    · rw [hreg4 .X22 (.inr (.inr (.inr (.inl rfl))))]; exact hi.x22
    · rw [hreg4 .X23 (.inr (.inr (.inr (.inr rfl))))]; exact hi.x23
    · rw [hd4]; exact hsl3 xs.toList (by simp [hsz]; omega) hxs2
    · rw [hd4]; exact hmsg
    · rw [hd4]; exact hts3

end

end NativeRustcVmArm.Sumcheck.Plain
