module

public import NativeRustcVmArm.Code.Vm.SumcheckOfGkrStep.Names
public import NativeRustcVmArm.Code.Vm.TStateSumcheckRoundPoly.Names
public import NativeRustcVmArm.Sumcheck.Gkr.Frame

/-!
# `sumcheck` with `gkr_step`'s closure: a round's polynomial

From the loop's head (`Inv`), `b2` tests `i < |pt|`: `b3` copies the point's coordinate `i` into
the frame's `eq` and sets its tag, `b4` the tag `None`; `b5` writes the tag and calls
`sumcheck_round_poly` (`b5_spec`); `b6` leaves for `.L8` on a rejection (`exit_fail`), else at
`b7` the polynomial read (`Mid`, `head_spec`).
-/

namespace NativeRustcVmArm.Sumcheck.Gkr

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SumcheckOfGkrStep
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck

@[expose] public section

/-- At `b7`, round `i`'s polynomial `msg` read, the state `s1`, the first `i` challenges `xs`. -/
structure Mid [Labels] (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m0 : MachineData)
    (i : Nat) (xs msg : Array EW) (s1 : TState) (m : MachineData) : Prop where
  fr : FrG m0 n m
  lt : i < n
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  x20 : (m.regs.getXReg .X20).toBitVec = slG m0 + BitVec.ofNat 64 (16 * i)
  x21 : m.regs.getXReg .X21 = m0.regs.X6
  x22 : m.regs.getXReg .X22 = m0.regs.X4
  x23 : m.regs.getXReg .X23 = m0.regs.X1
  x24 : (m.regs.getXReg .X24).toNat = i
  x25 : (m.regs.getXReg .X25).toBitVec = slG m0 + BitVec.ofNat 64 (16 * n)
  x26 : (m.regs.getXReg .X26).toBitVec = ptG m0 + BitVec.ofNat 64 (16 * i + 8)
  run : (sumcheckFn (claimG m0) (cntG m0) (fun j ↦ pt[j]?) (i + 1)).run s =
    some ((xs.push s1.sponge.squeeze.1, polyEval msg s1.sponge.squeeze.1),
      { s1 with sponge := s1.sponge.squeeze.2 })
  xsz : xs.size = i
  xs : NativeRustcVm.EWsAt m.dmem (slG m0) xs.toList
  msz : msg.size = cntG m0
  msg : NativeRustcVm.EWsAt m.dmem (base m0 192 + BitVec.ofNat 64 8) msg.toList
  ts : TStateAt m.dmem (tG m0) a s1

/-- What the loop ends in: the exit (a rejection), or `.L7` after the last round. -/
abbrev Goal [Host] (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m0 : MachineData)
    (k : Nat) (st : MachineState) : Prop :=
  (st.pc = retOf m0 ∧ SumcheckGkrPost a s pt n m0 st.data) ∨
    (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b10Offset) ∧ Done a s pt n m0 st.data)

end

public section

variable [Host] {a : DecArea} {s : TState} {pt : Array EW} {n : Nat} {m0 : MachineData} {k : Nat}

/-- The registers the loop keeps, from one state to the next. -/
theorem regs_eq {m m' : MachineData}
    (h : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 ∨ r = .X24 ∨ r = .X25 ∨
      r = .X26 → m'.regs.getXReg r = m.regs.getXReg r)
    {i : Nat} (hi : Inv a s pt n m0 i m) (hf : FrG m0 n m')
    (hrun : RoundsG a s pt m0 m'.dmem i ⟨m'.regs.X2, m'.regs.X3⟩) : Inv a s pt n m0 i m' := by
  refine ⟨hf, hi.lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrun⟩
  · rw [h .X19 (by simp)]; exact hi.x19
  · rw [h .X20 (by simp)]; exact hi.x20
  · rw [h .X21 (by simp)]; exact hi.x21
  · rw [h .X22 (by simp)]; exact hi.x22
  · rw [h .X23 (by simp)]; exact hi.x23
  · rw [h .X24 (by simp)]; exact hi.x24
  · rw [h .X25 (by simp)]; exact hi.x25
  · rw [h .X26 (by simp)]; exact hi.x26

/-- **`b5`, `b6`**: the tag of `eq`, `sumcheck_round_poly`; a rejection's exit or `b7` with the
polynomial. -/
theorem b5_spec (hp : Placed code k)
    (hrp : ∀ a s e, Spec (Labels.label NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e))
    (hpre : SumcheckGkrPre a s pt n m0) {i : Nat} {m : MachineData} (hi : Inv a s pt n m0 i m)
    (hx8 : m.regs.X8 = if i < pt.size then 1 else 0)
    (hv : ∀ h : i < pt.size,
      NativeRustcVm.EWAt m.dmem (base m0 192 + BitVec.ofNat 64 96) pt[i]) :
    Eventually (step1 Host.exe)
      (fun st ↦ Goal a s pt n m0 k st ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b7Offset) ∧ ∃ xs msg s1, Mid a s pt n m0 i xs msg s1 st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b5Offset)⟩ := by
  have g := geo hpre
  have hS := hpre.1.1
  obtain ⟨xs, si, hrun, hsz, hxs, hts⟩ := hi.run
  have hlt := hi.lt
  have hk5 : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b5Offset) := b5_in_code.trans hp.1 (by simp [b5])
  have hk6 : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b6Offset) := b6_in_code.trans hp.1 (by simp [b6])
  have hl8 : Labels.label NativeRustcVmArm.Vm.SumcheckOfGkrStep.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b11Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.SumcheckOfGkrStep.b11Offset) NativeRustcVmArm.Vm.SumcheckOfGkrStep.label_8_at
  have hwf2 := Bus.wf_frame (F := 192) hS (by decide) hi.fr.kept
  have hm2 : Match (Env.ofMachine m [(base m0 192, 192)]) frS m :=
    Bus.match_frame hS (by decide) (by decide) hi.fr.sp
  refine exec_then hk5 run_b5 hwf2 hm2 fun st2 hm2' hpc2 ↦ ?_
  have hm2A : Match (Env.ofMachine m [(base m0 192, 192)]) (after b5 frS) st2.data := by
    rw [after_eq run_b5]; exact hm2'
  have hW2 : ∀ w ∈ (after b5 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 192 ∧
      ∀ p ∈ slotsG, w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off := by
    rw [after_eq run_b5]; decide +kernel
  have hfr2 : FrG m0 n st2.data :=
    Bus.Fr.block hi.fr g.hN (by decide) hm2A hwf2 (by rw [after_eq run_b5]) hW2
      (by rw [after_eq run_b5]; decide +kernel) slotsG8
  have hbN := base_noWrap (m0 := m0) (F := 192) (le_trans (by decide) g.hN)
  have hbt := base_toNat (m0 := m0) (F := 192) (le_trans (by decide) g.hN)
  have hWr : ∀ q, Written (Env.ofMachine m [(base m0 192, 192)]) (after b5 frS) q →
      (base m0 192).toNat + 88 ≤ q.toNat ∧ q.toNat < (base m0 192).toNat + 96 := fun q hq ↦ by
    have := Written.toNat (r := 0) (lo := 88) (hi := 96) rfl
      (by rw [after_eq run_b5]; decide) hq
    exact this
  have hWr2 : ∀ q, Written (Env.ofMachine m [(base m0 192, 192)]) (after b5 frS) q →
      InRange (stackBelow m0 sumcheckGkrStack) sumcheckGkrStack q := fun q hq ↦
    g.ctx.inRange_frame (Written.inRange rfl hbN (fun w hw ↦ ⟨(hW2 w hw).1, (hW2 w hw).2.1⟩) hq)
  have hs2 := hm2A.sameOutside hwf2
  have hts2 : TStateAt st2.data.dmem (tG m0) a si :=
    g.t_keep hs2 (hm2A.kept hwf2) (fun q hq ↦ .inl (hWr2 q hq)) hts
  have hxs2 : NativeRustcVm.EWsAt st2.data.dmem (slG m0) xs.toList :=
    g.sl_keep hs2 (fun q hq ↦ .inl (hWr2 q hq)) (by simp [hsz]; omega) hxs
  have htag := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm2' (r := 0) (o := 88) rfl
    (by decide) (v := .reg .X8) (by decide +kernel)
  have heq2 : OptEWAt st2.data.dmem (base m0 192 + BitVec.ofNat 64 88) pt[i]? := by
    by_cases hp' : i < pt.size
    · rw [Array.getElem?_eq_getElem hp']
      refine ⟨?_, ?_⟩
      · have e : UInt64.ofBitVec ((Sym.reg .X8).eval (Env.ofMachine m [(base m0 192, 192)])) =
            1 := by
          show m.regs.X8 = 1
          rw [hx8]; simp only [hp', ↓reduceIte]
        rw [e] at htag; exact htag
      · have := hv hp'
        rw [off, NativeRustcVm.addr_add_add]
        refine NativeRustcVm.BytesAt.of_sameOutside this hs2 fun j hj hq ↦ ?_
        have := hWr _ hq
        rw [NativeRustcVm.length_ewBytes] at hj
        unfold NoWrap at hbN
        rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)] at this
        omega
    · rw [Array.getElem?_eq_none (by omega)]
      have e : UInt64.ofBitVec ((Sym.reg .X8).eval (Env.ofMachine m [(base m0 192, 192)])) =
          0 := by
        show m.regs.X8 = 0
        rw [hx8]; simp only [hp', ↓reduceIte]
      rw [e] at htag; exact htag
  have hx0 : st2.data.regs.X0.toBitVec = tG m0 :=
    (hm2'.regs .X0 _ rfl).trans (congrArg UInt64.toBitVec hi.x23)
  have hx1 : st2.data.regs.X1 = m0.regs.X4 :=
    UInt64.toBitVec_inj.mp ((hm2'.regs .X1 _ rfl).trans (congrArg UInt64.toBitVec hi.x22))
  have hx2 : st2.data.regs.X2 = m.regs.X2 := UInt64.toBitVec_inj.mp ((hm2'.regs .X2 _ rfl).trans rfl)
  have hx3 : st2.data.regs.X3 = m.regs.X3 := UInt64.toBitVec_inj.mp ((hm2'.regs .X3 _ rfl).trans rfl)
  have hx4 : st2.data.regs.X4.toBitVec = base m0 192 + BitVec.ofNat 64 88 := by
    rw [show st2.data.regs.X4 = st2.data.regs.getXReg .X4 from rfl, hm2'.regs .X4 _ rfl]
    simp [Sym.eval, Env.base, Env.ofMachine]
  have hx5 : st2.data.regs.X5.toBitVec = base m0 192 + BitVec.ofNat 64 8 := by
    rw [show st2.data.regs.X5 = st2.data.regs.getXReg .X5 from rfl, hm2'.regs .X5 _ rfl]
    simp [Sym.eval, Env.base, Env.ofMachine]
  have hreg2 : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 ∨ r = .X24 ∨ r = .X25 ∨
      r = .X26 → st2.data.regs.getXReg r = m.regs.getXReg r := by
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact UInt64.toBitVec_inj.mp ((hm2'.regs _ _ rfl).trans rfl)
  refine call_then hpc2 (hrp a si pt[i]?)
    (g.roundPolyPre hfr2 hts2 heq2 hx0 (by rw [hx1]) hx4 hx5) fun st3 hpc3 hpost3 ↦ ?_
  obtain ⟨hfr3, hmsg3, hsl3⟩ := g.afterRoundPoly hfr2 hpost3 hx0 hx5 keepG_saved
  have hok3 := hpost3.1
  have hsv3 := hpost3.2.2.2.2
  rw [hx1, hx2, hx3] at hok3 hmsg3
  have hreg3 : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 ∨ r = .X24 ∨ r = .X25 ∨
      r = .X26 → st3.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    (hsv3.1 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans
      (hreg2 r hr)
  have hwf3 := Bus.wf_frame (F := 192) hS (by decide) hfr3.kept
  have hm3 : Match (Env.ofMachine st3.data [(base m0 192, 192)]) frS st3.data :=
    Bus.match_frame hS (by decide) (by decide) hfr3.sp
  refine exec_at hk6 run_b6 hwf3 hpc3 hm3 fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hfr4, hd4⟩ := frBlock hfr3 hS (by decide) (by decide) hm4 rfl rfl (by decide)
    (by decide)
  have hreg4 : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 ∨ r = .X24 ∨ r = .X25 ∨
      r = .X26 → st4.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr
    refine Eq.trans ?_ (hreg3 r hr)
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact UInt64.toBitVec_inj.mp ((hm4.regs _ _ rfl).trans rfl)
  have hX0 : (Env.ofMachine st3.data [(base m0 192, 192)]).regs .X0 =
      st3.data.regs.X0.toBitVec := rfl
  simp only [PcOk, SBool.eval, Sym.eval, hX0, getLsbD_low_zero] at hpc4
  cases hr : (sumcheckRoundPoly (cntG m0) ⟨m.regs.X2, m.regs.X3⟩ pt[i]?).run si with
  | none =>
    rw [hr] at hok3
    have hpc : st4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b11Offset) := by
      rw [hpc4, hok3]; simp [okWord, hl8]
    have hnone := sumcheckFn_run_none_le (E := fun j ↦ pt[j]?)
      (sumcheckFn_run_succ_none hrun hr) (show i + 1 ≤ n by omega)
    obtain ⟨d4, pc4⟩ := st4
    simp only at hpc
    subst hpc
    exact Eventually.mono (exit_fail hp hpre hfr4
      (by rw [hreg4 .X19 (.inl rfl)]; exact hi.x19) hnone) fun st h ↦ .inl (.inl h)
  | some p =>
    obtain ⟨msg, s1⟩ := p
    rw [hr] at hok3
    have hpc : st4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b7Offset) := by
      rw [hpc4, hok3]; simp [okWord]; rfl
    obtain ⟨hmsg, hts3⟩ := hmsg3 msg s1 hr
    refine Eventually.done _ (.inr ⟨hpc, xs, msg, s1, hfr4, hlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      sumcheckFn_run_succ_some hrun hr, hsz, ?_, roundPoly_size g.ok.2.2.2.2.1 hr, ?_, ?_⟩)
    · rw [hreg4 .X19 (by simp)]; exact hi.x19
    · rw [hreg4 .X20 (by simp)]; exact hi.x20
    · rw [hreg4 .X21 (by simp)]; exact hi.x21
    · rw [hreg4 .X22 (by simp)]; exact hi.x22
    · rw [hreg4 .X23 (by simp)]; exact hi.x23
    · rw [hreg4 .X24 (by simp)]; exact hi.x24
    · rw [hreg4 .X25 (by simp)]; exact hi.x25
    · rw [hreg4 .X26 (by simp)]; exact hi.x26
    · rw [hd4]; exact hsl3 xs.toList (by simp [hsz]; omega) hxs2
    · rw [hd4]; exact hmsg
    · rw [hd4]; exact hts3

/-- **A round's polynomial**: from the head, `eq` set from the point, a rejection's exit or `b7`
with the polynomial. -/
theorem head_spec (hp : Placed code k)
    (hrp : ∀ a s e, Spec (Labels.label NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e))
    (hpre : SumcheckGkrPre a s pt n m0) {i : Nat} {m : MachineData} (hi : Inv a s pt n m0 i m) :
    Eventually (step1 Host.exe)
      (fun st ↦ Goal a s pt n m0 k st ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b7Offset) ∧ ∃ xs msg s1, Mid a s pt n m0 i xs msg s1 st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b2Offset)⟩ := by
  have g := geo hpre
  have hS := hpre.1.1
  have hsz : pt.size = m0.regs.X6.toNat := hpre.2.1
  have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b2Offset) := b2_in_code.trans hp.1 (by simp [b2])
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b3Offset) := b3_in_code.trans hp.1 (by simp [b3])
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b4Offset) := b4_in_code.trans hp.1 (by simp [b4])
  have hl4 : Labels.label NativeRustcVmArm.Vm.SumcheckOfGkrStep.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b4Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.SumcheckOfGkrStep.b4Offset) NativeRustcVmArm.Vm.SumcheckOfGkrStep.label_4_at
  have hl5 : Labels.label NativeRustcVmArm.Vm.SumcheckOfGkrStep.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b5Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.SumcheckOfGkrStep.b5Offset) NativeRustcVmArm.Vm.SumcheckOfGkrStep.label_5_at
  have hwf := Bus.wf_frame (F := 192) hS (by decide) hi.fr.kept
  have hm : Match (Env.ofMachine m [(base m0 192, 192)]) frS m :=
    Bus.match_frame hS (by decide) (by decide) hi.fr.sp
  refine exec_then hk2 run_b2 hwf hm fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hfr2, hd2⟩ := frBlock hi.fr hS (by decide) (by decide) hm2 rfl rfl (by decide)
    (by decide)
  have hsame2 : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 ∨ r = .X24 ∨
      r = .X25 ∨ r = .X26 → st2.data.regs.getXReg r = m.regs.getXReg r := by
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact UInt64.toBitVec_inj.mp ((hm2.regs _ _ rfl).trans rfl)
  have hx2 : st2.data.regs.X2 = m.regs.X2 := UInt64.toBitVec_inj.mp ((hm2.regs .X2 _ rfl).trans rfl)
  have hx3 : st2.data.regs.X3 = m.regs.X3 := UInt64.toBitVec_inj.mp ((hm2.regs .X3 _ rfl).trans rfl)
  have hi2 : Inv a s pt n m0 i st2.data :=
    regs_eq hsame2 hi hfr2 (by rw [hx2, hx3, hd2]; exact hi.run)
  have hc : ((SBool.cmp CmpOp.ult RegWidth.W64 (.reg .X24) (.reg .X21)).not.eval
      (Env.ofMachine m [(base m0 192, 192)])) = !(decide (i < pt.size)) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
    show (!(BitVec.ult (m.regs.getXReg .X24).toBitVec (m.regs.getXReg .X21).toBitVec)) = _
    rw [hi.x21, BitVec.ult]
    congr 2
    rw [show (m.regs.getXReg .X24).toBitVec.toNat = i from hi.x24, hsz]
    rfl
  simp only [PcOk] at hpc2
  rw [hc] at hpc2
  by_cases hp' : i < pt.size
  · simp only [hp', decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc2
    -- `b3`: the coordinate into the frame.
    have hpi := (pt_keep hpre hfr2).getElem (i := i) (by simpa using hp')
    have hnwp : (ptG m0).toNat + 16 * pt.size ≤ 2 ^ 64 := hpre.2.2.2.1
    have hst : Apart (ptG m0) (16 * pt.size) (stackBelow m0 sumcheckGkrStack)
        sumcheckGkrStack := hpre.2.2.2.2.1
    have hpoff : (ptG m0 + BitVec.ofNat 64 (16 * i)).toNat = (ptG m0).toNat + 16 * i :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    have hrd : Readable m0 (ptG m0 + BitVec.ofNat 64 (16 * i)) 16 := by
      refine ⟨fun j hj ↦ ?_, NativeRustcVm.NoWrap.sub hpre.2.2.2.1 (by omega)⟩
      have := (NativeRustcVm.BytesAt.mapped hpre.2.2.1)
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList] at this
      rw [NativeRustcVm.addr_add_add]; exact this _ (by omega)
    have hos : OffStack m0 (ptG m0 + BitVec.ofNat 64 (16 * i)) 16 sumcheckGkrStack :=
      NativeRustcVm.Apart.mono hst (by rw [hpoff]; omega) (by rw [hpoff]; omega)
        (Nat.le_refl _) (Nat.le_refl _)
    have hwf3 : (Env.ofMachine st2.data [(base m0 192, 192),
        (ptG m0 + BitVec.ofNat 64 (16 * i), 16)]).WF :=
      Bus.wf_frame2 hS (by decide) hfr2.kept hrd hos
    have hm3 : Match (Env.ofMachine st2.data [(base m0 192, 192),
        (ptG m0 + BitVec.ofNat 64 (16 * i), 16)]) ptS st2.data :=
      match_ofMachine ⟨rfl, fun _ ↦ Bus.base_aligned hS (by decide) (by decide), rfl, nofun,
          trivial⟩
        (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero,
              Option.map_some, Option.getD_some]; rw [hfr2.sp]; simp)
        ⟨by
          show (st2.data.regs.getXReg .X26).toBitVec = _
          rw [hi2.x26]
          simp only [Sym.eval, Env.base, Env.ofMachine, List.getElem?_cons_succ,
            List.getElem?_cons_zero, Option.map_some, Option.getD_some]
          rw [show (BitVec.ofInt 64 8) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add],
          trivial⟩ trivial trivial trivial
    refine exec_at hk3 run_b3 hwf3 hpc2 hm3 fun st3 hm3' hpc3 ↦ ?_
    have hm3A : Match (Env.ofMachine st2.data [(base m0 192, 192),
        (ptG m0 + BitVec.ofNat 64 (16 * i), 16)]) (after b3 ptS) st3.data := by
      rw [after_eq run_b3]; exact hm3'
    have hW3 : ∀ w ∈ (after b3 ptS).mem, w.r = 0 ∧ w.off + w.n ≤ 192 ∧
        ∀ p ∈ slotsG, w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off := by
      rw [after_eq run_b3]; decide +kernel
    have hfr3 : FrG m0 n st3.data :=
      Bus.Fr.block hfr2 g.hN (by decide) hm3A hwf3 (by rw [after_eq run_b3]) hW3
        (by rw [after_eq run_b3]; decide +kernel) slotsG8
    have hWr3 : ∀ q, Written (Env.ofMachine st2.data [(base m0 192, 192),
        (ptG m0 + BitVec.ofNat 64 (16 * i), 16)]) (after b3 ptS) q →
        InRange (stackBelow m0 sumcheckGkrStack) sumcheckGkrStack q := fun q hq ↦
      g.ctx.inRange_frame (Written.inRange rfl
        (base_noWrap (m0 := m0) (F := 192) (le_trans (by decide) g.hN))
        (fun w hw ↦ ⟨(hW3 w hw).1, (hW3 w hw).2.1⟩) hq)
    have hs3 := hm3A.sameOutside hwf3
    have hsame3 : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 ∨ r = .X24 ∨
        r = .X25 ∨ r = .X26 → st3.data.regs.getXReg r = st2.data.regs.getXReg r := by
      have e : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 ∨ r = .X24 ∨
          r = .X25 → st3.data.regs.getXReg r = st2.data.regs.getXReg r := by
        rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
          exact UInt64.toBitVec_inj.mp ((hm3'.regs _ _ rfl).trans rfl)
      rintro r (h | h | h | h | h | h | h | rfl)
      · exact e r (.inl h)
      · exact e r (.inr (.inl h))
      · exact e r (.inr (.inr (.inl h)))
      · exact e r (.inr (.inr (.inr (.inl h))))
      · exact e r (.inr (.inr (.inr (.inr (.inl h)))))
      · exact e r (.inr (.inr (.inr (.inr (.inr (.inl h))))))
      · exact e r (.inr (.inr (.inr (.inr (.inr (.inr h))))))
      apply UInt64.toBitVec_inj.mp
      rw [hm3'.regs .X26 _ rfl, hi2.x26]
      simp only [Sym.eval, Env.base, Env.ofMachine, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some]
      rw [show (BitVec.ofInt 64 8) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add]
    have hx2' : st3.data.regs.X2 = st2.data.regs.X2 :=
      UInt64.toBitVec_inj.mp ((hm3'.regs .X2 _ rfl).trans rfl)
    have hx3' : st3.data.regs.X3 = st2.data.regs.X3 :=
      UInt64.toBitVec_inj.mp ((hm3'.regs .X3 _ rfl).trans rfl)
    obtain ⟨xs, si, hrun, hsz', hxs, hts⟩ := hi2.run
    have hi3 : Inv a s pt n m0 i st3.data := regs_eq hsame3 hi2 hfr3 (by
      rw [hx2', hx3']
      exact ⟨xs, si, hrun, hsz', g.sl_keep hs3 (fun q hq ↦ .inl (hWr3 q hq))
        (by simp [hsz']; exact Nat.le_of_lt hi.lt) hxs,
        g.t_keep hs3 (hm3A.kept hwf3) (fun q hq ↦ .inl (hWr3 q hq)) hts⟩)
    have hv3 : NativeRustcVm.EWAt st3.data.dmem (base m0 192 + BitVec.ofNat 64 96) pt[i] := by
      have hpi' := NativeRustcVm.ewAt_iff.1 hpi
      have w0 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm3' (r := 0) (o := 96) rfl
        (by decide) (v := .load 1 0 8) (by decide +kernel)
      have w8 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm3' (r := 0) (o := 104) rfl
        (by decide) (v := .load 1 8 8) (by decide +kernel)
      rw [NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add]
      refine ⟨?_, ?_⟩
      · convert w0 using 1
        show pt[i].c0 = UInt64.ofBitVec (Env.load _ 1 0 8)
        rw [NativeRustcVmArm.Sumcheck.load_word (by
          rw [NativeRustcVm.addr_add_zero]; exact hpi'.1)]
        rfl
      · convert w8 using 1
        show pt[i].c1 = UInt64.ofBitVec (Env.load _ 1 8 8)
        rw [NativeRustcVmArm.Sumcheck.load_word (by exact hpi'.2)]
        rfl
    have hx8 : st3.data.regs.X8 = if i < pt.size then 1 else 0 := by
      simp only [hp', ↓reduceIte]; exact UInt64.toBitVec_inj.mp ((hm3'.regs .X8 _ rfl).trans rfl)
    obtain ⟨d3, pc3⟩ := st3
    simp only [PcOk] at hpc3
    rw [hl5] at hpc3
    subst hpc3
    exact b5_spec hp hrp hpre hi3 hx8 fun _ ↦ hv3
  · simp only [hp', decide_false, Bool.not_false, ↓reduceIte] at hpc2
    rw [hl4] at hpc2
    have hwf4 := Bus.wf_frame (F := 192) hS (by decide) hfr2.kept
    have hm4 : Match (Env.ofMachine st2.data [(base m0 192, 192)]) frS st2.data :=
      Bus.match_frame hS (by decide) (by decide) hfr2.sp
    refine exec_at hk4 run_b4 hwf4 hpc2 hm4 fun st3 hm3 hpc3 ↦ ?_
    obtain ⟨hfr3, hd3⟩ := frBlock hfr2 hS (by decide) (by decide) hm3 rfl rfl (by decide)
      (by decide)
    have hsame3 : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 ∨ r = .X24 ∨
        r = .X25 ∨ r = .X26 → st3.data.regs.getXReg r = st2.data.regs.getXReg r := by
      rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        exact UInt64.toBitVec_inj.mp ((hm3.regs _ _ rfl).trans rfl)
    have hx2' : st3.data.regs.X2 = st2.data.regs.X2 :=
      UInt64.toBitVec_inj.mp ((hm3.regs .X2 _ rfl).trans rfl)
    have hx3' : st3.data.regs.X3 = st2.data.regs.X3 :=
      UInt64.toBitVec_inj.mp ((hm3.regs .X3 _ rfl).trans rfl)
    have hi3 : Inv a s pt n m0 i st3.data :=
      regs_eq hsame3 hi2 hfr3 (by rw [hx2', hx3', hd3]; exact hi2.run)
    have hx8 : st3.data.regs.X8 = if i < pt.size then 1 else 0 := by
      simp only [hp', ↓reduceIte]; exact UInt64.toBitVec_inj.mp ((hm3.regs .X8 _ rfl).trans rfl)
    obtain ⟨d3, pc3⟩ := st3
    simp only [PcOk] at hpc3
    subst hpc3
    exact b5_spec hp hrp hpre hi3 hx8 fun h ↦ absurd h hp'

end

end NativeRustcVmArm.Sumcheck.Gkr
