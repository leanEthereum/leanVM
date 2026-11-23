module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.PolyEval.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfGkrStep.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Bus.GkrStep.Frame

/-!
# `gkr_step` up to its sumcheck

`b0` saves X19 to X30 in the 1392-byte frame (the `GkrStateW` in X19, `step` in X20, the `TState`
in X21, `last` in X22) and computes the first grind's bits (`bit_length(1)`); `b1` grinds (`0`
bits); `b2` checks it; `b3` squeezes the combiner (into X24, X25 in `b4`); `b4` evaluates the
values there; `b5` passes the point (`|point|` in X23, the word at SP), `2^step` (X26) and the frame
at `1024` (X27) on to the sumcheck; `b6` checks its result (`AtChildren`).
-/

namespace NativeRustcVmArm.Bus.GkrStep

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrStep
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)
open NativeRustcVm (ewsOf)
open NativeRustcVm.Sumcheck (sumcheckFn)

public section
variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

/-- **The sumcheck** (`b5`, `b6`), from the combiner's evaluation of the values. -/
theorem sc_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0)
    (hsc : ∀ s pt n, Spec (Labels.label NativeRustcVmArm.Vm.SumcheckOfGkrStep.entryLabel) (SumcheckGkrPre a s pt n)
      (SumcheckGkrPost a s pt n))
    (hch : ∀ c cl xs s2 m, AtChildren a s0 g0 m0 c cl xs s2 m →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b7Offset)⟩)
    {c : EW} {s1 : TState} {m : MachineData}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m)
    (h19 : m.regs.getXReg .X19 = m0.regs.X3) (h20 : m.regs.getXReg .X20 = m0.regs.X1)
    (h21 : m.regs.getXReg .X21 = m0.regs.X0) (h22 : m.regs.getXReg .X22 = m0.regs.X2)
    (h24 : m.regs.getXReg .X24 = c.c0) (h25 : m.regs.getXReg .X25 = c.c1)
    (h0 : m.regs.X0 = (polyEval g0.values c).c0) (h1 : m.regs.X1 = (polyEval g0.values c).c1)
    (hts : TStateAt m.dmem m0.regs.X0.toBitVec a s1)
    (hgs : GkrStateWAt m.dmem m0.regs.X3.toBitVec g0)
    (hrc : sampleChallenge.run s0 = some (c, s1)) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b5Offset)⟩ := by
  have hS := pre_stack h
  have hN : gkrStepStack ≤ m0.regs.SP.toNat := hS.2.1
  have cx := ctx h
  have hgk := pre_gk h
  have hstep := pre_step h
  have hsz := pre_size h
  have hnwp : m0.regs.X3.toBitVec.toNat + 1064 ≤ 2 ^ 64 := hgk.2.1
  have hlen : g0.point.size ≤ 63 := by unfold busPointCap at hsz; omega
  -- `b5`
  have hwf : (Env.ofMachine m [(base m0 1392, 1392), (m0.regs.X3.toBitVec, 1064)]).WF :=
    Bus.wf_frame2 hS N_ge hfr.kept ⟨hgk.1, hgk.2.1⟩ hgk.2.2.2.2.1
  have hm := match_frameW (n := 1064) hS N_ge rfl hfr.sp (r := .X19) (by rw [h19])
  refine exec_then (b5_in_code.trans hp.1 (by simp [b5])) run_b5 hwf hm fun st hm' hpc ↦ ?_
  have hlw : NativeRustcVm.WordAt m.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 48)
      g0.point.size.toUInt64 := by
    have := hgs.point.2.1
    rwa [Array.length_toList] at this
  have hL : (Env.ofMachine m [(base m0 1392, 1392), (m0.regs.X3.toBitVec, 1064)]).load 1 48 8 =
      BitVec.ofNat 64 g0.point.size := by
    rw [Transcript.load_ofMachine (b := m0.regs.X3.toBitVec) (n := 1064) rfl hlw]
    rfl
  have hlt := ult_lit g0.point.size (by omega)
  have e23 : (st.data.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 g0.point.size := by
    rw [hm'.regs .X23 _ rfl]
    simp only [Sym.eval, SBool.eval, hL, hlt, ↓reduceIte]
  have e6 : (st.data.regs.getXReg .X6).toBitVec = BitVec.ofNat 64 g0.point.size := by
    rw [hm'.regs .X6 _ rfl]
    simp only [Sym.eval, SBool.eval, hL, hlt, ↓reduceIte]
  have e5 : (st.data.regs.getXReg .X5).toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 56 := by
    rw [hm'.regs .X5 _ rfl]
    simp only [Sym.eval, SBool.eval, hL, hlt, ↓reduceIte]
    rfl
  have e26 : (st.data.regs.getXReg .X26).toBitVec = BitVec.ofNat 64 (2 ^ m0.regs.X1.toNat) := by
    rw [hm'.regs .X26 _ rfl]
    simp only [Sym.eval, Env.ofMachine, h20]
    exact lsl_one _ hstep
  have e4 : (st.data.regs.getXReg .X4).toBitVec = BitVec.ofNat 64 (2 ^ m0.regs.X1.toNat + 1) := by
    rw [hm'.regs .X4 _ rfl]
    simp only [Sym.eval, Env.ofMachine, h20]
    exact orr_one _ hstep
  have e0 : (st.data.regs.getXReg .X0).toBitVec = loc m0 1024 := by
    rw [hm'.regs .X0 _ rfl]; rfl
  have e27 : (st.data.regs.getXReg .X27).toBitVec = loc m0 1024 := by
    rw [hm'.regs .X27 _ rfl]; rfl
  have e7 : (st.data.regs.getXReg .X7).toBitVec = loc m0 16 := by
    rw [hm'.regs .X7 _ rfl]; rfl
  have e1 : st.data.regs.getXReg .X1 = m0.regs.X0 := (reg_of hm' rfl).trans h21
  have e2 : st.data.regs.getXReg .X2 = (polyEval g0.values c).c0 :=
    (reg_of hm' (r' := .X0) rfl).trans h0
  have e3 : st.data.regs.getXReg .X3 = (polyEval g0.values c).c1 :=
    (reg_of hm' (r' := .X1) rfl).trans h1
  have hfr' : Fr m0 1392 gkrStepStack slots keep (outs m0) st.data :=
    Bus.Fr.block hfr hN N_ge hm' hwf rfl (by decide +kernel) (by decide) slots_le
  have hs5 : NativeRustcVm.SameOutside m.dmem st.data.dmem (InRange (base m0 1392) 1392) :=
    NativeRustcVm.SameOutside.mono (hm'.sameOutside hwf) fun q hq ↦
      Written.inRange (r := 0) rfl (Bus.frame_mapped hS N_ge).2 (by decide +kernel) hq
  have hts' : TStateAt st.data.dmem m0.regs.X0.toBitVec a s1 :=
    hts.frame (fun q hq ↦ hm'.kept hwf q hq) (fun q hq ↦ frame_not_tstate cx hq) hs5
  have hgs' : GkrStateWAt st.data.dmem m0.regs.X3.toBitVec g0 :=
    gkrStateWAt_keep hgs hs5 fun q hq ↦ frame_not_p h hq
  have hn : NativeRustcVm.WordAt st.data.dmem st.data.regs.SP.toBitVec g0.point.size.toUInt64 := by
    have := Bus.wordAt_write hm' (r := 0) (o := 0) rfl (by omega)
      (v := .ite (.cmp .ult .W64 (.load 1 48 8) (.lit 64)) (.load 1 48 8) (.lit 0))
      (by decide +kernel)
    simp only [Sym.eval, SBool.eval, hL, hlt, ↓reduceIte, NativeRustcVm.addr_add_zero] at this
    rw [hfr'.sp]
    exact this
  -- the sumcheck
  have hat := Fr.at_ cx hfr' (outs_not_rc h)
  have hptr : NativeRustcVm.EWsAt st.data.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 56)
      g0.point.toList := by
    have := hgs'.point.2.2
    rwa [off, NativeRustcVm.addr_add_add] at this
  have hgk' := cx.outOk_sub hat le_sc hgk
  have hp56 : (m0.regs.X3.toBitVec + BitVec.ofNat 64 56).toNat = m0.regs.X3.toBitVec.toNat + 56 :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have hsl16 := cx.outOk hat le_sc (o := 16) (n := 16 * g0.point.size) (by omega)
  have hout := cx.outOk hat le_sc (o := 1024) (n := 24) (by omega)
  have hfl : (loc m0 16).toNat = m0.regs.SP.toNat - 1392 + 16 := loc_toNat hS (by omega)
  have hfl' : (loc m0 1024).toNat = m0.regs.SP.toNat - 1392 + 1024 := loc_toNat hS (by omega)
  have hpa : NativeRustcVm.Apart m0.regs.X3.toBitVec gkrStateBytes (base m0 1392) 1392 :=
    apart_frame hN N_ge hgk.2.2.2.2.1
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b5_length, NativeRustcVmArm.Vm.GkrStep.b5Length, show k + NativeRustcVmArm.Vm.GkrStep.b5Offset + 113 = k + NativeRustcVmArm.Vm.GkrStep.b6Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b5_length, NativeRustcVmArm.Vm.GkrStep.b5Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b5_next] at hpc
  refine Fr.callLocal (o := 16) (n := 1032) (X := fun q ↦ InRange (loc m0 1024) 24 q ∨
      InRange (loc m0 16) (16 * g0.point.size) q ∨ InRange m0.regs.X0.toBitVec tstateBytes q)
    hfr' hN le_sc keep_callee (slots_lo (by omega)) (by omega) (outs_not_frame h)
    (fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr (loc_mono hS (by omega) (by omega) (by omega) hq)
      · exact .inr (loc_mono hS (by omega) (by omega) (by omega) hq)
      · exact .inl (.inl hq))
    (hsc s1 g0.point g0.point.size) hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩)
    fun m2 hfr2 hq2 hcs2 hs2 ↦ ?_
  · refine ⟨⟨hfr'.stackOk hS rfl le_sc, cx.rcAt hat le_sc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
      ?_, ?_, ?_, ?_, by omega, ?_, ?_⟩
    · show TStateAt _ (st.data.regs.getXReg .X1).toBitVec a s1
      rw [e1]; exact hts'
    · show TStateOk _ (st.data.regs.getXReg .X1).toBitVec a _
      rw [e1]; exact cx.tstateOk hat le_sc
    · show 2 ≤ (st.data.regs.getXReg .X4).toBitVec.toNat
      rw [e4, NativeRustcVm.toNat_ofNat_of_lt (by rcases hstep with h' | h' <;> rw [h'] <;> decide)]
      rcases hstep with h' | h' <;> rw [h'] <;> decide
    · show (st.data.regs.getXReg .X4).toBitVec.toNat ≤ 5
      rw [e4, NativeRustcVm.toNat_ofNat_of_lt (by rcases hstep with h' | h' <;> rw [h'] <;> decide)]
      rcases hstep with h' | h' <;> rw [h'] <;> decide
    · show OutOk _ (st.data.regs.getXReg .X1).toBitVec a (st.data.regs.getXReg .X0).toBitVec 24 _
      rw [e1, e0]; exact hout
    · show OutOk _ (st.data.regs.getXReg .X1).toBitVec a (st.data.regs.getXReg .X7).toBitVec _ _
      rw [e1, e7]; exact hsl16
    · show NativeRustcVm.Apart (st.data.regs.getXReg .X0).toBitVec 24
        (st.data.regs.getXReg .X7).toBitVec _
      rw [e0, e7]
      unfold NativeRustcVm.Apart
      rw [hfl', hfl]
      omega
    · show g0.point.size = (st.data.regs.getXReg .X6).toBitVec.toNat
      rw [e6, NativeRustcVm.toNat_ofNat_of_lt (by omega)]
    · show NativeRustcVm.EWsAt _ (st.data.regs.getXReg .X5).toBitVec _
      rw [e5]; exact hptr
    · show NativeRustcVm.NoWrap (st.data.regs.getXReg .X5).toBitVec _
      rw [e5]; unfold NativeRustcVm.NoWrap; rw [hp56]; omega
    · show NativeRustcVm.Apart (st.data.regs.getXReg .X5).toBitVec _ _ _
      rw [e5]
      exact NativeRustcVm.Apart.mono hgk'.2.2.2.2.1 (by rw [hp56]; omega)
        (by rw [hp56]; unfold gkrStateBytes pointBufBytes busPointCap; omega)
        (Nat.le_refl _) (Nat.le_refl _)
    · show NativeRustcVm.Apart (st.data.regs.getXReg .X5).toBitVec _
        (st.data.regs.getXReg .X1).toBitVec _
      rw [e5, e1]
      exact NativeRustcVm.Apart.mono hgk.2.2.1 (by rw [hp56]; omega)
        (by rw [hp56]; unfold gkrStateBytes pointBufBytes busPointCap; omega)
        (Nat.le_refl _) (Nat.le_refl _)
    · show NativeRustcVm.Apart (st.data.regs.getXReg .X5).toBitVec _
        (st.data.regs.getXReg .X7).toBitVec _
      rw [e5, e7]
      have hA := hgk.2.2.2.2.1
      have hsN : (stackBelow m0 gkrStepStack).toNat = m0.regs.SP.toNat - gkrStepStack := cx.stk
      have := N_ge
      have hgsb : gkrStateBytes = 1064 := rfl
      have hcap : busPointCap = 63 := rfl
      show (m0.regs.X3.toBitVec + BitVec.ofNat 64 56).toNat + 16 * g0.point.size ≤ (loc m0 16).toNat ∨
        (loc m0 16).toNat + 16 * g0.point.size ≤ (m0.regs.X3.toBitVec + BitVec.ofNat 64 56).toNat
      have hA' : m0.regs.X3.toBitVec.toNat + gkrStateBytes ≤ (stackBelow m0 gkrStepStack).toNat ∨
          (stackBelow m0 gkrStepStack).toNat + gkrStepStack ≤ m0.regs.X3.toBitVec.toNat := hA
      rw [hp56, hfl]
      omega
    · exact hn
    · show st.data.regs.SP.toBitVec.toNat + 8 ≤ 2 ^ 64
      have := N_ge
      rw [show st.data.regs.SP.toBitVec = base m0 1392 from hfr'.sp, base_toNat (by omega)]
      have := m0.regs.SP.toNat_lt
      omega
  · rw [show st.data.regs.X0.toBitVec = loc m0 1024 from e0,
      show st.data.regs.X7.toBitVec = loc m0 16 from e7,
      show st.data.regs.X1 = m0.regs.X0 from e1] at hq'
    rcases hq' with hq' | hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr (.inl hq'))
    · exact .inr (.inr (.inr hq'))
    · exact .inl hq'
  -- `b6`: the sumcheck's tag.
  obtain ⟨⟨hopt, hsl, hnext⟩, -, -⟩ := hq2
  have eX0 : st.data.regs.X0.toBitVec = loc m0 1024 := e0
  have eX1 : st.data.regs.X1.toBitVec = m0.regs.X0.toBitVec := by
    rw [show st.data.regs.X1 = m0.regs.X0 from e1]
  have eX7 : st.data.regs.X7.toBitVec = loc m0 16 := e7
  have eC : (⟨st.data.regs.X2, st.data.regs.X3⟩ : EW) = polyEval g0.values c := by
    rw [show st.data.regs.X2 = _ from e2, show st.data.regs.X3 = _ from e3]
  have eX4 : st.data.regs.X4.toNat = 2 ^ m0.regs.X1.toNat + 1 := by
    show (st.data.regs.getXReg .X4).toBitVec.toNat = _
    rw [e4, NativeRustcVm.toNat_ofNat_of_lt
      (by rcases hstep with h' | h' <;> rw [h'] <;> decide)]
  rw [eX0, eC, eX4] at hopt
  rw [eX7, eC, eX4] at hsl
  rw [eX1, eC, eX4] at hnext
  have hrun : run0 s0 g0 m0 = ((sumcheckFn (polyEval g0.values c) (2 ^ m0.regs.X1.toNat + 1)
      (fun i ↦ g0.point[i]?) g0.point.size).run s1).bind fun x ↦
        gkrChildren m0.regs.X1.toNat c x.1.2 x.1.1 x.2 := by
    unfold run0
    rw [gkrStep_run' _ _ _ _ (by rcases hstep with h' | h' <;> omega), hrc]
    rfl
  -- `b6`: the sumcheck's tag.
  refine Fr.runBlock hS N_ge rfl hfr2 (b6_in_code.trans hp.1 (by simp [b6])) run_b6 rfl rfl
    (by decide) (by decide) fun st6 hfr6 hd6 hm6 hpc6 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b6_length, NativeRustcVmArm.Vm.GkrStep.b6Length, show k + NativeRustcVmArm.Vm.GkrStep.b6Offset + 2 = k + NativeRustcVmArm.Vm.GkrStep.b7Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b6_length, NativeRustcVmArm.Vm.GkrStep.b6Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b6_next] at hpc6
  cases hres : (sumcheckFn (polyEval g0.values c) (2 ^ m0.regs.X1.toNat + 1)
      (fun i ↦ g0.point[i]?) g0.point.size).run s1 with
  | none =>
    rw [hres] at hopt
    simp only [Option.map_none, OptEWAt] at hopt
    have hl : (Env.ofMachine m2 [(base m0 1392, 1392)]).load 0 1024 4 = BitVec.ofNat 64 0 :=
      Transcript.load4_of_tag (w := 0) (.inl rfl) hopt
    have hc : SBool.eval (Env.ofMachine m2 [(base m0 1392, 1392)])
        (.not (.bit .W32 (.load 0 1024 4) 0)) = true := by
      show (!(low .W32 ((Env.ofMachine m2 [(base m0 1392, 1392)]).load 0 1024 4)).getLsbD 0) = true
      rw [hl]
      rfl
    simp only [hc, ↓reduceIte] at hpc6
    exact at_pc (hpc6.trans (hp.label (j := NativeRustcVmArm.Vm.GkrStep.b32Offset) NativeRustcVmArm.Vm.GkrStep.label_14_at))
      (fail_spec hp h hfr6 (by rw [hrun, hres]; rfl))
  | some r =>
    obtain ⟨⟨xs, cl⟩, s2⟩ := r
    rw [hres] at hopt hnext
    simp only [Option.map_some, OptEWAt] at hopt
    have hl : (Env.ofMachine m2 [(base m0 1392, 1392)]).load 0 1024 4 = BitVec.ofNat 64 1 :=
      Transcript.load4_of_tag (w := 1) (.inr rfl) hopt.1
    have hc : SBool.eval (Env.ofMachine m2 [(base m0 1392, 1392)])
        (.not (.bit .W32 (.load 0 1024 4) 0)) = false := by
      show (!(low .W32 ((Env.ofMachine m2 [(base m0 1392, 1392)]).load 0 1024 4)).getLsbD 0) = false
      rw [hl]
      rfl
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc6
    obtain ⟨hc0, hc1⟩ := NativeRustcVm.ewAt_iff.mp hopt.2
    rw [off, NativeRustcVm.addr_add_add] at hc0
    rw [off, NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add] at hc1
    have hxs : xs.size = g0.point.size :=
      sumcheckFn_size _ _ _ g0.point.size (by simp only [StateT.run] at hres; exact hres)
    have k23 : st.data.regs.getXReg .X23 = st6.data.regs.getXReg .X23 :=
      ((reg_of hm6 rfl).trans (hcs2 .X23 rfl)).symm
    refine at_pc hpc6 (hch c cl xs s2 st6.data
      { fr := hfr6
        x19 := (reg_of hm6 rfl).trans ((hcs2 .X19 rfl).trans (UInt64.toBitVec_inj.mp
          ((hm'.regs .X19 _ rfl).trans (Transcript.eval_ptr rfl))))
        x20 := (reg_of hm6 rfl).trans ((hcs2 .X20 rfl).trans ((reg_of hm' rfl).trans h20))
        x21 := (reg_of hm6 rfl).trans ((hcs2 .X21 rfl).trans ((reg_of hm' rfl).trans h21))
        x22 := (reg_of hm6 rfl).trans ((hcs2 .X22 rfl).trans ((reg_of hm' rfl).trans h22))
        x23 := by
          rw [← k23, UInt64.toNat, e23, NativeRustcVm.toNat_ofNat_of_lt (by omega), hxs]
        x24 := (reg_of hm6 rfl).trans ((hcs2 .X24 rfl).trans ((reg_of hm' rfl).trans h24))
        x25 := (reg_of hm6 rfl).trans ((hcs2 .X25 rfl).trans ((reg_of hm' rfl).trans h25))
        x26 := by rw [reg_of hm6 rfl, hcs2 .X26 rfl]; exact e26
        x27 := by rw [reg_of hm6 rfl, hcs2 .X27 rfl]; exact e27
        size := by rw [hxs]; exact hsz
        cl0 := by rw [hd6]; exact hc0
        cl1 := by rw [hd6]; exact hc1
        hxs := by rw [hd6]; exact hsl xs cl s2 hres
        ts := by rw [hd6]; exact hnext (xs, cl) s2 rfl
        run := by rw [hrun, hres]; rfl })

/-- **`gkr_step` up to the children**: the prologue, the first grind (of `0` bits), the
combiner, its evaluation of the values, the sumcheck. -/
theorem head_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpe : Spec (Labels.label NativeRustcVmArm.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hsc : ∀ s pt n, Spec (Labels.label NativeRustcVmArm.Vm.SumcheckOfGkrStep.entryLabel) (SumcheckGkrPre a s pt n)
      (SumcheckGkrPost a s pt n))
    (hch : ∀ c cl xs s2 m, AtChildren a s0 g0 m0 c cl xs s2 m →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b7Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b0Offset)⟩ := by
  have hS := pre_stack h
  have hN : gkrStepStack ≤ m0.regs.SP.toNat := hS.2.1
  have cx := ctx h
  -- `b0`: the prologue.
  have hwf := Bus.wf_env0 hS (F := 1392) N_ge
  have hm : Match (Bus.env0 m0 1392) entryS m0 := Bus.match_entry hS N_ge rfl
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  have hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) st.data :=
    Fr.ofPrologue hN N_ge hm1 hwf rfl (by decide +kernel) slots_le (by decide +kernel)
      (by decide)
  have hsame : NativeRustcVm.SameOutside m0.dmem st.data.dmem (InRange (base m0 1392) 1392) :=
    NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf) fun q hq ↦
      Written.inRange (r := 0) rfl (Bus.frame_mapped hS N_ge).2 (by decide +kernel) hq
  have hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s0 :=
    (pre_ts h).frame (fun q hq ↦ hm1.kept hwf q hq) (fun q hq ↦ frame_not_tstate cx hq) hsame
  have hgs : GkrStateWAt st.data.dmem m0.regs.X3.toBitVec g0 :=
    gkrStateWAt_keep (pre_gs h) hsame fun q hq ↦ frame_not_p h hq
  have e19 : st.data.regs.getXReg .X19 = m0.regs.X3 := reg_of hm1 (r' := .X3) rfl
  have e20 : st.data.regs.getXReg .X20 = m0.regs.X1 := reg_of hm1 (r' := .X1) rfl
  have e21 : st.data.regs.getXReg .X21 = m0.regs.X0 := reg_of hm1 (r' := .X0) rfl
  have e22 : st.data.regs.getXReg .X22 = m0.regs.X2 := by
    apply UInt64.toBitVec_inj.mp
    rw [hm1.regs .X22 _ rfl]
    exact trunc_small _ (pre_last h)
  -- `bit_length(1)`
  simp only [PcOk, Nat.add_assoc, NativeRustcVmArm.Vm.GkrStep.b0_next] at hpc
  refine Fr.callSpec hfr hN le_bl keep_callee slots_le (outs_not_frame h) hbl hpc trivial
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun _ h ↦ .inl h, hq.2.2⟩)
    fun m2 hfr2 hq2 hcs2 ↦ ?_
  have hx0 : m2.regs.X0 = 1 := by
    apply UInt64.toNat_inj.mp
    rw [hq2.1]
    have : st.data.regs.X0.toNat = 1 := by
      show (st.data.regs.getXReg .X0).toBitVec.toNat = 1
      rw [reg_lit hm1 (r := .X0) (n := 1) rfl]; rfl
    rw [this]; rfl
  have hts2 : TStateAt m2.dmem m0.regs.X0.toBitVec a s0 :=
    hts.frame (fun q hq ↦ hq2.2.2.2.2 q hq) (fun q hq ↦ (callee_apart h hfr le_bl hq).1) hq2.2.1
  have hgs2 : GkrStateWAt m2.dmem m0.regs.X3.toBitVec g0 :=
    gkrStateWAt_keep hgs hq2.2.1 fun q hq ↦ (callee_apart h hfr le_bl hq).2.1
  -- `b1`: the first grind, of `0` bits.
  have f19 := (hcs2 .X19 rfl).trans e19
  have f20 := (hcs2 .X20 rfl).trans e20
  have f21 := (hcs2 .X21 rfl).trans e21
  have f22 := (hcs2 .X22 rfl).trans e22
  have hwf1 := Bus.wf_frame hS N_ge hfr2.kept
  have hm1' := Bus.match_frame hS N_ge rfl hfr2.sp
  refine exec_then (b1_in_code.trans hp.1 (by simp [b1])) run_b1 hwf1 hm1' fun st1 hm1'' hpc1 ↦ ?_
  have hfr1 : Fr m0 1392 gkrStepStack slots keep (outs m0) st1.data :=
    Fr.ofBlock hfr2 hm1' hm1'' hwf1 rfl rfl rfl (by decide)
  have hd1 : st1.data.dmem = m2.dmem := hm1''.dmem_eq hwf1 rfl
  have g0' : st1.data.regs.X0 = m0.regs.X0 := (reg_of hm1'' (r := .X0) (r' := .X21) rfl).trans f21
  have g1 : grindBits st1.data = 0 := by
    have : (st1.data.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 0 := by
      have hlt : SBool.eval (Env.ofMachine m2 [(base m0 1392, 1392)])
          (.cmp .ult .W32 (.reg .X0) (.lit 3)) = true := by
        show CmpOp.ult.apply .W32 (m2.regs.getXReg .X0).toBitVec (BitVec.ofNat 64 3) = true
        rw [show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, hx0]
        rfl
      rw [hm1''.regs .X1 _ rfl]
      simp only [Sym.eval, hlt, ↓reduceIte]
    unfold grindBits
    rw [show st1.data.regs.X1.toNat = (st1.data.regs.getXReg .X1).toBitVec.toNat from rfl, this]
    rfl
  have hat1 := Fr.at_ cx hfr1 (outs_not_rc h)
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b1_length, NativeRustcVmArm.Vm.GkrStep.b1Length, show k + NativeRustcVmArm.Vm.GkrStep.b1Offset + 4 = k + NativeRustcVmArm.Vm.GkrStep.b2Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b1_length, NativeRustcVmArm.Vm.GkrStep.b1Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b1_next] at hpc1
  refine Fr.callSpec hfr1 hN le_grind keep_callee slots_le (outs_not_frame h) (hgr s0) hpc1
    ⟨hfr1.stackOk hS rfl le_grind, cx.rcAt hat1 le_grind, by rw [g0', hd1]; exact hts2,
      by rw [g0']; exact cx.tstateOk hat1 le_grind, by rw [g1]; decide⟩
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ by
      rw [g0'] at hq'
      exact hq'.elim (fun h' ↦ .inr (.inl h')) .inl, hq.2.2.2⟩)
    fun m3 hfr3 hq3 hcs3 ↦ ?_
  obtain ⟨hx3, hnext3, hs3, hsv3⟩ := hq3
  rw [g1, grind_zero_run] at hx3 hnext3
  rw [g0'] at hnext3 hs3
  have hts3 : TStateAt m3.dmem m0.regs.X0.toBitVec a s0 := hnext3 () s0 rfl
  have hgs3 : GkrStateWAt m3.dmem m0.regs.X3.toBitVec g0 := by
    rw [← hd1] at hgs2
    exact gkrStateWAt_keep hgs2 hs3 fun q hq ↦ hq.elim (fun h' ↦ (p_apart h · |>.1 h'))
      fun h' ↦ (callee_apart h hfr1 le_grind h').2.1
  -- `b2`: the grind's result, `Some`.
  have k19 := (hcs3 .X19 rfl).trans ((reg_of hm1'' (r := .X19) (r' := .X19) rfl).trans f19)
  have k20 := (hcs3 .X20 rfl).trans ((reg_of hm1'' (r := .X20) (r' := .X20) rfl).trans f20)
  have k21 := (hcs3 .X21 rfl).trans ((reg_of hm1'' (r := .X21) (r' := .X21) rfl).trans f21)
  have k22 := (hcs3 .X22 rfl).trans ((reg_of hm1'' (r := .X22) (r' := .X22) rfl).trans f22)
  refine Fr.runBlock hS N_ge rfl hfr3 (b2_in_code.trans hp.1 (by simp [b2])) run_b2 rfl rfl
    (by decide) (by decide) fun st4 hfr4 hd4 hm4 hpc4 ↦ ?_
  have hc4 : SBool.eval (Env.ofMachine m3 [(base m0 1392, 1392)])
      (.cmp .eq .W32 (.un .trunc .W32 (.reg .X0)) (.lit 0)) = false := by
    show CmpOp.eq.apply .W32 (UnOp.apply .trunc .W32 (m3.regs.getXReg .X0).toBitVec)
      (BitVec.ofNat 64 0) = false
    rw [show m3.regs.getXReg .X0 = m3.regs.X0 from rfl, hx3]
    rfl
  simp only [PcOk, hc4, Bool.false_eq_true, ↓reduceIte, NativeRustcVmArm.Vm.GkrStep.b2_length, NativeRustcVmArm.Vm.GkrStep.b2Length,
    show k + NativeRustcVmArm.Vm.GkrStep.b2Offset + 3 = k + NativeRustcVmArm.Vm.GkrStep.b3Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b2_length, NativeRustcVmArm.Vm.GkrStep.b2Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b2_next] at hpc4
  -- `b3`: the combiner.
  refine at_pc hpc4 (Fr.runBlock hS N_ge rfl hfr4 (b3_in_code.trans hp.1 (by simp [b3])) run_b3
    rfl rfl (by decide) (by decide) fun st5 hfr5 hd5 hm5 hpc5 ↦ ?_)
  have l19 := (reg_of hm5 (r := .X19) (r' := .X19) rfl).trans
    ((reg_of hm4 (r := .X19) (r' := .X19) rfl).trans k19)
  have l20 := (reg_of hm5 (r := .X20) (r' := .X20) rfl).trans
    ((reg_of hm4 (r := .X20) (r' := .X20) rfl).trans k20)
  have l21 := (reg_of hm5 (r := .X21) (r' := .X21) rfl).trans
    ((reg_of hm4 (r := .X21) (r' := .X21) rfl).trans k21)
  have l22 := (reg_of hm5 (r := .X22) (r' := .X22) rfl).trans
    ((reg_of hm4 (r := .X22) (r' := .X22) rfl).trans k22)
  have l0 : st5.data.regs.X0.toBitVec = m0.regs.X0.toBitVec := by
    rw [show st5.data.regs.X0 = st5.data.regs.getXReg .X0 from rfl,
      reg_of hm5 (r := .X0) (r' := .X21) rfl, reg_of hm4 rfl, k21]
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b3_length, NativeRustcVmArm.Vm.GkrStep.b3Length, show k + NativeRustcVmArm.Vm.GkrStep.b3Offset + 2 = k + NativeRustcVmArm.Vm.GkrStep.b4Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b3_length, NativeRustcVmArm.Vm.GkrStep.b3Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b3_next] at hpc5
  refine squeeze_call cx hsq hfr5 (outs_not_rc h) le_sq keep_callee slots_le (outs_not_frame h)
    (fun q hq ↦ .inl hq) hpc5 l0 (by rw [hd5, hd4]; exact hts3)
    fun m6 hfr6 hts6 h60 h61 hcs6 hs6 ↦ ?_
  have hgs6 : GkrStateWAt m6.dmem m0.regs.X3.toBitVec g0 := by
    rw [← hd4, ← hd5] at hgs3
    refine gkrStateWAt_keep hgs3 hs6 fun q hq ↦ hq.elim (fun h' ↦ ?_)
      fun h' ↦ (callee_apart h hfr5 le_sq h').2.1
    intro hp'
    have hnwt := (pre_ts h).footprint.1.2
    have hsb : spongeBytes ≤ tstateBytes := by decide
    exact (p_apart h hp').1 (NativeRustcVm.InRange.mono h' (NativeRustcVm.NoWrap.mono hnwt hsb)
      hnwt (Nat.le_refl _) (by omega))
  -- `b4`: the values at the combiner.
  have hwf7 := Bus.wf_frame hS N_ge hfr6.kept
  have hm7 := Bus.match_frame hS N_ge rfl hfr6.sp
  refine exec_then (b4_in_code.trans hp.1 (by simp [b4])) run_b4 hwf7 hm7 fun st7 hm7' hpc7 ↦ ?_
  have hfr7 : Fr m0 1392 gkrStepStack slots keep (outs m0) st7.data :=
    Fr.ofBlock hfr6 hm7 hm7' hwf7 rfl rfl rfl (by decide)
  have hd7 : st7.data.dmem = m6.dmem := hm7'.dmem_eq hwf7 rfl
  have n19 := (reg_of hm7' (r := .X19) (r' := .X19) rfl).trans ((hcs6 .X19 rfl).trans l19)
  have n20 := (reg_of hm7' (r := .X20) (r' := .X20) rfl).trans ((hcs6 .X20 rfl).trans l20)
  have n21 := (reg_of hm7' (r := .X21) (r' := .X21) rfl).trans ((hcs6 .X21 rfl).trans l21)
  have n22 := (reg_of hm7' (r := .X22) (r' := .X22) rfl).trans ((hcs6 .X22 rfl).trans l22)
  have n24 : st7.data.regs.getXReg .X24 = s0.sponge.squeeze.1.c0 :=
    (reg_of hm7' (r' := .X0) rfl).trans h60
  have n25 : st7.data.regs.getXReg .X25 = s0.sponge.squeeze.1.c1 :=
    (reg_of hm7' (r' := .X1) rfl).trans h61
  have n0 : st7.data.regs.X0 = m0.regs.X3 := (reg_of hm7' (r := .X0) (r' := .X19) rfl).trans
    ((hcs6 .X19 rfl).trans l19)
  have n1 : st7.data.regs.X1.toNat = 3 := by
    show (st7.data.regs.getXReg .X1).toBitVec.toNat = 3
    rw [reg_lit hm7' (r := .X1) (n := 3) rfl]; rfl
  have n2 : st7.data.regs.X2 = s0.sponge.squeeze.1.c0 := (reg_of hm7' (r := .X2) (r' := .X0) rfl).trans h60
  have n3 : st7.data.regs.X3 = s0.sponge.squeeze.1.c1 := (reg_of hm7' (r := .X3) (r' := .X1) rfl).trans h61
  have hgk := pre_gk h
  have hat7 := Fr.at_ cx hfr7 (outs_not_rc h)
  have hval : NativeRustcVm.EWsAt st7.data.dmem m0.regs.X3.toBitVec g0.values.toList := by
    rw [hd7]; exact hgs6.values
  have hsz3 : g0.values.toList.length = 3 := by rw [Array.length_toList]; exact hgs6.values_size
  have hslice : slice st7.data st7.data.regs.X0 st7.data.regs.X1 = g0.values := by
    unfold slice
    rw [n0, show st7.data.regs.X1.toNat = g0.values.toList.length by rw [n1, hsz3],
      NativeRustcVm.ewsOf_of_ewsAt hval, Array.toArray_toList]
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b4_length, NativeRustcVmArm.Vm.GkrStep.b4Length, show k + NativeRustcVmArm.Vm.GkrStep.b4Offset + 7 = k + NativeRustcVmArm.Vm.GkrStep.b5Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b4_length, NativeRustcVmArm.Vm.GkrStep.b4Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b4_next] at hpc7
  refine Fr.callSpec hfr7 hN le_pe keep_callee slots_le (outs_not_frame h) hpe hpc7
    ⟨hfr7.stackOk hS rfl le_pe, by rw [n1]; omega, ?_⟩
    (fun m' hq ↦ ⟨Bus.changes_zero hq.2.1, hq.2.2⟩) fun m8 hfr8 hq8' hcs8 ↦ ?_
  · unfold SliceOk Readable OffStack
    rw [n1, n0]
    have := cx.outOk_sub hat7 le_pe hgk
    exact ⟨⟨fun i hi ↦ this.1 i (by unfold gkrStateBytes pointBufBytes busPointCap; omega),
      NativeRustcVm.NoWrap.mono this.2.1 (by decide)⟩,
      NativeRustcVm.Apart.mono this.2.2.2.2.1 (Nat.le_refl _)
        (by unfold gkrStateBytes pointBufBytes busPointCap; omega) (Nat.le_refl _) (Nat.le_refl _)⟩
  obtain ⟨hret, hch8, hsv8⟩ := hq8'
  rw [hslice, n2, n3] at hret
  have hs8 := Bus.changes_zero (outs := fun _ ↦ False) hch8
  have hts8 : TStateAt m8.dmem m0.regs.X0.toBitVec a { s0 with sponge := s0.sponge.squeeze.2 } := by
    rw [← hd7] at hts6
    exact hts6.frame (fun q hq ↦ hsv8.2.2 q hq) (fun q hq ↦ hq.elim
      (fun h' ↦ (callee_apart h hfr7 le_pe h').1) False.elim) hs8
  have hgs8 : GkrStateWAt m8.dmem m0.regs.X3.toBitVec g0 := by
    rw [← hd7] at hgs6
    exact gkrStateWAt_keep hgs6 hs8 fun q hq ↦ hq.elim
      (fun h' ↦ (callee_apart h hfr7 le_pe h').2.1) False.elim
  exact sc_spec hp h hsc hch hfr8 ((hcs8 .X19 rfl).trans n19) ((hcs8 .X20 rfl).trans n20)
    ((hcs8 .X21 rfl).trans n21) ((hcs8 .X22 rfl).trans n22) ((hcs8 .X24 rfl).trans n24)
    ((hcs8 .X25 rfl).trans n25) (congrArg EW.c0 hret) (congrArg EW.c1 hret) hts8 hgs8 rfl

end

end NativeRustcVmArm.Bus.GkrStep
