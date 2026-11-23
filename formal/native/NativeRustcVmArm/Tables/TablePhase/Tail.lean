module

public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.Powers.Names
public import NativeRustcVmArm.Code.Vm.TableSumcheck.Names
public import NativeRustcVmArm.Tables.TablePhase.Facts
public import NativeRustcVmArm.Tables.Frame
public import NativeRustcVmArm.Tables.Common
public import NativeRustcVm.Tables.Phase

/-!
# `table_phase` after `ξ`

From `b4` (`ξ` in X0, X1): its five powers into the frame (`powers`), the target, the dot of
the last three and the bus's totals (`dot`), the table sumcheck (`table_sumcheck`), the exit
(`tail`). `exit7`: the epilogue; `tstate_keep`: the `TState` across a callee's changes in the
function's stack.
-/

namespace NativeRustcVmArm.Tables.TablePhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TablePhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables
open NativeRustcVm.Layout (LayoutWAt layoutBytes)
open NativeRustcVm.Bus (BusWAt busBytes)
open NativeRustcVmArm.Sumcheck (Ctx At)

@[expose] public section

/-- The outputs: the `TState` (X0) and the evaluations (X3). -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange m0.regs.X0.toBitVec tstateBytes q ∨ InRange m0.regs.X3.toBitVec tableEvalsBytes q

/-- What `table_phase` reaches. -/
abbrev Goal [Labels] (a : DecArea) (s : TState) (L : LayoutW) (bus : BusResultW) (m0 : MachineData)
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ TablePhasePost a s L bus m0 st.data

end

public section

theorem N_ge [Labels] : 128 ≤ tablePhaseStack := by unfold tablePhaseStack; omega

/-- **The `TState`** across changes in the function's stack. -/
theorem tstate_keep [Labels] {m0 : MachineData} {t : BitVec 64} {a : DecArea} {N F : Nat}
    (c : Ctx m0 t a N F) {R : BitVec 64 → Prop} (hR : ∀ q, R q → InRange (stackBelow m0 N) N q)
    {d d' : DataMem} {s : TState} (hts : TStateAt d t a s) (hk : Kept d d')
    (hs : SameOutside d d' R) : TStateAt d' t a s := by
  have hnw : NoWrap (stackBelow m0 N) N := by
    unfold NoWrap; rw [c.stk]; have := c.spN; have := Sumcheck.Ctx.sp_lt m0; omega
  exact hts.frame hk (fun q hq ↦ ⟨NativeRustcVm.Apart.not_inRange c.tok.1.symm hnw c.fp.1.2 (hR q hq),
    NativeRustcVm.Apart.not_inRange c.tok.2.1.symm hnw c.fp.2.1.2 (hR q hq)⟩) hs

section
variable [Host] {k : Nat} {a : DecArea} {s : TState} {L : LayoutW} {bus : BusResultW}
  {m0 : MachineData}

/-- **The exit** (`b7`): the registers restored, X0 kept, `ret`. -/
theorem exit7 (hp : Placed code k) (hS : StackOk m0 tablePhaseStack) {m : MachineData}
    (hfr : Fr m0 128 tablePhaseStack slots keep (outs m0) m)
    (hpost : ∀ m' : MachineData, m'.dmem = m.dmem → m'.regs.X0 = m.regs.X0 →
      m'.regs.X0 = okWord ((tablePhase L bus).run s).isSome ∧
      (∀ x s', (tablePhase L bus).run s = some (x, s') →
        TableEvalsAt m'.dmem m0.regs.X3.toBitVec x) ∧
      NextAt m'.dmem m0.regs.X0.toBitVec a ((tablePhase L bus).run s)) :
    Eventually (step1 Host.exe) (Goal a s L bus m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TablePhase.b7Offset)⟩ := by
  have hwf := Bus.wf_frame hS N_ge hfr.kept
  have hm := Bus.match_frame hS N_ge rfl hfr.sp
  refine exec_then (b7_in_code.trans hp.1 (by simp [b7])) run_b7 hwf hm fun st hm' hpc ↦ ?_
  have hm'' : Match (Env.ofMachine m [(base m0 128, 128)]) (Bus.after b7 sF) st.data := by
    rw [Bus.after_eq run_b7]; exact hm'
  obtain ⟨hok, hmem, h0⟩ := ok_b7
  obtain ⟨hret, hsv⟩ := hfr.exit hm'' hwf hok
  have hd : st.data.dmem = m.dmem := hm''.dmem_eq hwf hmem
  obtain ⟨p1, p2, p3⟩ := hpost st.data hd (Bus.Gkr.reg_of hm'' h0)
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc, hret], p1, p2, p3, ?_, hsv⟩
  rw [hd]
  exact NativeRustcVm.SameOutside.mono hfr.same fun q hq ↦ hq.elim (fun h ↦ .inr (.inr h)) fun h ↦ h.elim .inl (.inr ∘ .inl)

omit [Host] in
/-- A register a block kept, from the block's list. -/
theorem reg_keep {S : SState} {L : List XReg}
    (h : L.all (fun r ↦ S.reg r == some (.reg r)) = true) {r : XReg} (hr : r ∈ L) :
    S.reg r = some (.reg r) :=
  beq_iff_eq.mp (List.all_eq_true.mp h r hr)

omit [Host] in
theorem inRange_le {x q : BitVec 64} {n n' : Nat} (h : InRange x n q) (hn : n ≤ n') :
    InRange x n' q := by
  unfold InRange at *; omega

/-- **After `ξ`** (`b4` on): the powers, the target, the table sumcheck, the exit. -/
theorem tail (hp : Placed code k)
    (hpow : Spec (Labels.label NativeRustcVmArm.Vm.Powers.entryLabel) PowersPre PowersPost)
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost)
    (hsum : ∀ a s heights bus, Spec (Labels.label NativeRustcVmArm.Vm.TableSumcheck.entryLabel)
      (TableSumcheckPre a s heights bus) (TableSumcheckPost a s heights bus))
    (hpre : TablePhasePre a s L bus m0) {s1 : TState}
    (hg : (grind (grindingBits 4)).run s = some ((), s1)) {m : MachineData}
    (hfr : Fr m0 128 tablePhaseStack slots keep (outs m0) m)
    (x19 : m.regs.getXReg .X19 = m0.regs.X3) (x20 : m.regs.getXReg .X20 = m0.regs.X2)
    (x21 : m.regs.getXReg .X21 = m0.regs.X0) (x22 : m.regs.getXReg .X22 = m0.regs.X1)
    (x0 : m.regs.X0 = s1.sponge.squeeze.1.c0) (x1 : m.regs.X1 = s1.sponge.squeeze.1.c1)
    (hts : TStateAt m.dmem m0.regs.X0.toBitVec a { s1 with sponge := s1.sponge.squeeze.2 }) :
    Eventually (step1 Host.exe) (Goal a s L bus m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TablePhase.b4Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hS, hrc, hT, hts0, htok, heo, hRt, hRe, hLin, hL, hBin, hB⟩ := hpre'
  have hN := hS.2.1
  have c : Ctx m0 m0.regs.X0.toBitVec a tablePhaseStack 128 :=
    Bus.Gkr.ctx_of hS hrc hts0 htok N_ge rfl
  have hor : ∀ q, outs m0 q → ¬InRange rcAddr 192 q := fun q hq ↦
    hq.elim c.not_rc_tstate (Bus.Gkr.out_not_rc c heo)
  have hof : ∀ q, outs m0 q → ¬InRange (base m0 128) 128 q := fun q hq ↦
    hq.elim (Bus.Gkr.tstate_not_frame c) (Bus.Gkr.out_not_frame c heo)
  have hnwN : NoWrap (base m0 tablePhaseStack) tablePhaseStack := base_noWrap hN
  have hstk : ∀ q, InRange (base m0 128) 80 q → InRange (stackBelow m0 tablePhaseStack)
      tablePhaseStack q := fun q hq ↦ Bus.frame_inRange hN N_ge (inRange_le hq (by omega))
  -- The inputs, kept.
  have hin : ∀ {x : BitVec 64} {n : Nat}, ReadIn m0 x n tablePhaseStack
      [⟨m0.regs.X0.toBitVec, tstateBytes⟩, ⟨m0.regs.X3.toBitVec, tableEvalsBytes⟩] →
      ∀ j < n, ¬outs m0 (x + BitVec.ofNat 64 j) := fun {x n} h j hj ho ↦ ho.elim
    (Bus.not_inRange_of_apart (h.2.2 ⟨m0.regs.X0.toBitVec, tstateBytes⟩ (by simp)) h.1.2
      hts0.footprint.1.2 hj)
    (Bus.not_inRange_of_apart (h.2.2 ⟨m0.regs.X3.toBitVec, tableEvalsBytes⟩ (by simp)) h.1.2
      heo.2.1 hj)
  -- `b4`: the powers zeroed, `powers`.
  have hwf := Bus.wf_frame hS N_ge hfr.kept
  have hm := Bus.match_frame hS N_ge rfl hfr.sp
  refine exec_then (b4_in_code.trans hp.1 (by simp [b4])) run_b4 hwf hm fun st4 hm4 hpc4 ↦ ?_
  have hm4' : Match (Env.ofMachine m [(base m0 128, 128)]) (Bus.after b4 sF) st4.data := by
    rw [Bus.after_eq run_b4]; exact hm4
  obtain ⟨hsp4, hw4, hkk4, hk4, g0, g1, g2, g3, g23⟩ := ok_b4
  have hfr4 := Bus.Fr.block hfr hN N_ge hm4' hwf hsp4
    (fun w hw ↦ ⟨(hw4 w hw).1, by have := (hw4 w hw).2; omega, fun p hp ↦ by
      have := (hw4 w hw).2; have := slots_hi p hp; omega⟩)
    hkk4 slots_le
  have hle_p : 128 + powersStack ≤ tablePhaseStack := by unfold tablePhaseStack; omega
  have e2 : st4.data.regs.X2.toBitVec = base m0 128 := by
    show (st4.data.regs.getXReg .X2).toBitVec = _
    rw [hm4'.regs .X2 _ g2, eval_ptr0]; simp
  have e3 : st4.data.regs.X3.toNat = 5 := by
    show (st4.data.regs.getXReg .X3).toBitVec.toNat = 5
    rw [Bus.Gkr.reg_lit hm4' g3]; rfl
  have exi : ewArg st4.data.regs.X0 st4.data.regs.X1 = s1.sponge.squeeze.1 := by
    show (⟨st4.data.regs.getXReg .X0, st4.data.regs.getXReg .X1⟩ : EW) = _
    rw [Bus.Gkr.reg_of hm4' g0, Bus.Gkr.reg_of hm4' g1]
    exact (congrArg₂ EW.mk x0 x1).trans rfl
  have hl80 := Bus.local_ok (o := 0) (n := 80) hS hle_p (by omega) hfr4.kept hfr4.sp
  rw [NativeRustcVm.addr_add_zero] at hl80
  have hpc4' : st4.pc = Labels.label NativeRustcVmArm.Vm.Powers.entryLabel ∧ retOf st4.data = Host.addrOf (k + NativeRustcVmArm.Vm.TablePhase.b5Offset) := hpc4
  have hat4 := Bus.Gkr.Fr.at_ c hfr4 hor
  refine Bus.Gkr.Fr.callLocal (o := 0) (n := 80) (X := fun q ↦ InRange (base m0 128) 80 q) hfr4 hN
    hle_p keep_callee slots_hi (by omega) hof
    (fun q hq ↦ .inr (by rw [NativeRustcVm.addr_add_zero]; exact hq)) hpow hpc4'
    ⟨hfr4.stackOk hS rfl hle_p, by unfold SliceOk; rw [e2, e3]; exact hl80⟩
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q h ↦
      h.elim (fun h ↦ .inr (by rw [e2, e3] at h; exact h)) .inl, hq.2.2⟩)
    fun m5 hfr5 hq5 hcs5 hs5 ↦ ?_
  have hpw : NativeRustcVm.EWsAt m5.dmem (base m0 128) (powers s1.sponge.squeeze.1 5).toList := by
    have := hq5.1; rw [e2, e3, exi] at this; exact this
  have hts5 : TStateAt m5.dmem m0.regs.X0.toBitVec a { s1 with sponge := s1.sponge.squeeze.2 } :=
    tstate_keep c (fun q hq ↦ hq.elim (fun h ↦ (callee_in c hat4 hle_p h).1) (hstk q))
      (tstate_keep c (fun q hq ↦ Bus.frame_inRange hN N_ge (Bus.Written.inRange rfl
        (base_noWrap (by omega)) (fun w hw ↦ ⟨(hw4 w hw).1, by have := (hw4 w hw).2; omega⟩) hq))
        hts (hm4'.kept hwf) (hm4'.sameOutside hwf)) hq5.2.2.2.2 hs5
  -- `b5`: the dot's arguments, `dot`.
  have hle_d : 128 + dotStack ≤ tablePhaseStack := by unfold tablePhaseStack; omega
  refine Bus.Gkr.Fr.runBlock hS N_ge rfl hfr5 (b5_in_code.trans hp.1 (by simp [b5])) run_b5 rfl rfl
    (by decide) (by decide) fun st6 hfr6 hd6 hm6 hpc6 ↦ ?_
  have hm6' : Match (Env.ofMachine m5 [(base m0 128, 128)]) (Bus.after b5 sF) st6.data := by
    rw [Bus.after_eq run_b5]; exact hm6
  obtain ⟨-, -, hk5, f0, f1, f2, f3⟩ := ok_b5
  have b23 : (m5.regs.getXReg .X23).toBitVec = base m0 128 := by
    rw [hcs5 .X23 rfl, hm4'.regs .X23 _ g23, eval_ptr0]; simp
  have x20_5 : m5.regs.getXReg .X20 = m0.regs.X2 := by
    rw [hcs5 .X20 rfl, Bus.Gkr.reg_of hm4' (reg_keep hk4 (by simp)), x20]
  have e60 : st6.data.regs.X0.toBitVec = base m0 128 + BitVec.ofNat 64 32 := by
    show (st6.data.regs.getXReg .X0).toBitVec = _
    rw [hm6'.regs .X0 _ f0]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [b23]
  have e62 : st6.data.regs.X2.toBitVec = m0.regs.X2.toBitVec + BitVec.ofNat 64 107720 := by
    show (st6.data.regs.getXReg .X2).toBitVec = _
    rw [hm6'.regs .X2 _ f2]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [x20_5]
  have e61 : st6.data.regs.X1.toNat = 3 := by
    show (st6.data.regs.getXReg .X1).toBitVec.toNat = 3
    rw [Bus.Gkr.reg_lit hm6' f1]; rfl
  have e63 : st6.data.regs.X3.toNat = 3 := by
    show (st6.data.regs.getXReg .X3).toBitVec.toNat = 3
    rw [Bus.Gkr.reg_lit hm6' f3]; rfl
  have hat6 := Bus.Gkr.Fr.at_ c hfr6 hor
  have hl48 := Bus.local_ok (o := 32) (n := 48) hS hle_d (by omega) hfr6.kept hfr6.sp
  have hbt := ReadIn.fr hfr6 hS hle_d (ReadIn.sub hBin (o := 107720) (k := 48)
    (by unfold busBytes NativeRustcVm.Bus.busTotalsOff NativeRustcVm.Bus.busPointOff
          NativeRustcVm.Bus.pointBufBytes NativeRustcVm.Bus.formsBytes; decide)
    (by unfold busBytes NativeRustcVm.Bus.busTotalsOff NativeRustcVm.Bus.busPointOff
          NativeRustcVm.Bus.pointBufBytes NativeRustcVm.Bus.formsBytes; decide))
  have hpc6' : st6.pc = Labels.label NativeRustcVmArm.Vm.Dot.entryLabel ∧ retOf st6.data = Host.addrOf (k + NativeRustcVmArm.Vm.TablePhase.b6Offset) := hpc6
  refine Fr.leaf hfr6 hN hle_d keep_callee slots_le hof hdot
    (fun m m' hq ↦ ⟨Bus.changes_zero hq.2.1, hq.2.2⟩) hpc6'
    ⟨hfr6.stackOk hS rfl hle_d, by unfold SliceOk; rw [e60, e61]; exact hl48,
      by unfold SliceOk; rw [e62, e63]; exact ⟨hbt.1, hbt.2.1⟩⟩ fun m7 hfr7 hq7 hcs7 ↦ ?_
  -- The powers and the target.
  set P := powers s1.sponge.squeeze.1 5 with hPdef
  have hP5' : P.size = 5 := by rw [hPdef]; exact size_powers _ _
  have hP5 : P.toList.length = 5 := by simpa using hP5'
  have hsplit := hpw
  rw [← List.take_append_drop 2 P.toList, NativeRustcVm.ewsAt_append] at hsplit
  have htk : (P.toList.take 2).length = 2 := by simp; omega
  have hdr : (P.toList.drop 2).length = 3 := by simp; omega
  rw [htk] at hsplit
  have hB6 : BusWAt st6.data.dmem m0.regs.X2.toBitVec bus :=
    BusWAt.of_same hB (same_in hfr6 hS hBin.1.2 hBin.2.1 (hin hBin))
  have htot : NativeRustcVm.ewsOf st6.data.dmem (m0.regs.X2.toBitVec + BitVec.ofNat 64 107720) 3 =
      bus.totals.toList := by
    have := NativeRustcVm.ewsOf_of_ewsAt hB6.totals
    rwa [show bus.totals.toList.length = 3 by simp [hB6.totals_size]] at this
  have hfp6 : NativeRustcVm.ewsOf st6.data.dmem (base m0 128 + BitVec.ofNat 64 32) 3 =
      P.toList.drop 2 := by
    rw [hd6]
    have := NativeRustcVm.ewsOf_of_ewsAt hsplit.2
    rwa [hdr] at this
  have htarget : ewRet m7 = dot (P.extract 2 5) bus.totals := by
    rw [hq7.1]
    unfold slice
    rw [e60, e61, e62, e63, hfp6, htot, extract_drop hP5']
  -- What the dot kept.
  have hfb : ∀ i < 80, InRange (base m0 128) 128 (base m0 128 + BitVec.ofNat 64 i) := fun i hi ↦
    NativeRustcVm.inRange_add (by omega) (by norm_num)
  have hpw7 : NativeRustcVm.EWsAt m7.dmem (base m0 128) P.toList := by
    refine NativeRustcVm.BytesAt.of_sameOutside (by rw [hd6]; exact hpw) hq7.2.1 fun i hi h ↦ ?_
    rw [NativeRustcVm.length_ewsBytes, hP5] at hi
    exact h.elim (Bus.not_inRange_zero _ _) fun h ↦ (callee_in c hat6 hle_d h).2 (hfb i hi)
  have hts7 : TStateAt m7.dmem m0.regs.X0.toBitVec a { s1 with sponge := s1.sponge.squeeze.2 } :=
    tstate_keep c (fun q hq ↦ hq.elim (fun h ↦ (Bus.not_inRange_zero _ _ h).elim)
      (fun h ↦ (callee_in c hat6 hle_d h).1)) (by rw [hd6]; exact hts5) hq7.2.2.2.2 hq7.2.1
  -- `b6`: the sumcheck's arguments.
  have hle_s : 128 + tableSumcheckStack ≤ tablePhaseStack := by unfold tablePhaseStack; omega
  refine Bus.Gkr.Fr.runBlock hS N_ge rfl hfr7 (b6_in_code.trans hp.1 (by simp [b6])) run_b6 rfl rfl
    (by decide) (by decide) fun st8 hfr8 hd8 hm8 hpc8 ↦ ?_
  have hm8' : Match (Env.ofMachine m7 [(base m0 128, 128)]) (Bus.after b6 sF) st8.data := by
    rw [Bus.after_eq run_b6]; exact hm8
  obtain ⟨-, -, hk6, h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok_b6
  have tr : ∀ r, r ∈ mids → calleeSaved r = true → m7.regs.getXReg r =
      st4.data.regs.getXReg r := fun r hr hc ↦ by
    rw [hcs7 r hc, Bus.Gkr.reg_of hm6' (reg_keep hk5 hr), hcs5 r hc]
  have e80 : st8.data.regs.X0 = m0.regs.X0 := by
    rw [show st8.data.regs.X0 = st8.data.regs.getXReg .X0 from rfl, Bus.Gkr.reg_of hm8' h0,
      tr .X21 (by simp) rfl, Bus.Gkr.reg_of hm4' (reg_keep hk4 (by simp)), x21]
  have e87 : st8.data.regs.X7 = m0.regs.X3 := by
    rw [show st8.data.regs.X7 = st8.data.regs.getXReg .X7 from rfl, Bus.Gkr.reg_of hm8' h7,
      tr .X19 (by simp) rfl, Bus.Gkr.reg_of hm4' (reg_keep hk4 (by simp)), x19]
  have e82 : st8.data.regs.X2 = m0.regs.X2 := by
    rw [show st8.data.regs.X2 = st8.data.regs.getXReg .X2 from rfl, Bus.Gkr.reg_of hm8' h2,
      tr .X20 (by simp) rfl, Bus.Gkr.reg_of hm4' (reg_keep hk4 (by simp)), x20]
  have e81 : st8.data.regs.X1.toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 24 := by
    show (st8.data.regs.getXReg .X1).toBitVec = _
    rw [hm8'.regs .X1 _ h1]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [tr .X22 (by simp) rfl, Bus.Gkr.reg_of hm4' (reg_keep hk4 (by simp)), x22]
  have e83 : st8.data.regs.X3.toBitVec = base m0 128 := by
    show (st8.data.regs.getXReg .X3).toBitVec = _
    rw [hm8'.regs .X3 _ h3, eval_ptr0]; simp
  have e84 : st8.data.regs.X4.toBitVec = base m0 128 + BitVec.ofNat 64 32 := by
    show (st8.data.regs.getXReg .X4).toBitVec = _
    rw [hm8'.regs .X4 _ h4]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [tr .X23 (by simp) rfl, ← hcs5 .X23 rfl, b23]
  have e856 : (⟨st8.data.regs.X5, st8.data.regs.X6⟩ : EW) = dot (P.extract 2 5) bus.totals := by
    rw [← htarget]
    show (⟨st8.data.regs.getXReg .X5, st8.data.regs.getXReg .X6⟩ : EW) =
      ⟨m7.regs.getXReg .X0, m7.regs.getXReg .X1⟩
    rw [Bus.Gkr.reg_of hm8' h5, Bus.Gkr.reg_of hm8' h6]
  -- `table_sumcheck`.
  have hat8 := Bus.Gkr.Fr.at_ c hfr8 hor
  have hd8' : st8.data.dmem = m7.dmem := hd8
  have hL8 : LayoutWAt st8.data.dmem m0.regs.X1.toBitVec L :=
    LayoutWAt.of_same hL (same_in hfr8 hS hLin.1.2 hLin.2.1 (hin hLin))
  have hB8 : BusWAt st8.data.dmem m0.regs.X2.toBitVec bus :=
    BusWAt.of_same hB (same_in hfr8 hS hBin.1.2 hBin.2.1 (hin hBin))
  have hpw8 : NativeRustcVm.EWsAt st8.data.dmem (base m0 128) P.toList := by rw [hd8']; exact hpw7
  have hsplit8 := hpw8
  rw [← List.take_append_drop 2 P.toList, NativeRustcVm.ewsAt_append, htk] at hsplit8
  have hcp : arrE st8.data st8.data.regs.X3 2 = P.extract 0 2 := by
    unfold arrE
    rw [e83, ← extract_take]
    have := NativeRustcVm.ewsOf_of_ewsAt hsplit8.1
    rw [htk] at this
    rw [this]
  have hfp : arrE st8.data st8.data.regs.X4 3 = P.extract 2 5 := by
    unfold arrE
    rw [e84, ← extract_drop hP5']
    have := NativeRustcVm.ewsOf_of_ewsAt hsplit8.2
    rw [hdr] at this
    rw [this]
  have hws : ∀ {o n : Nat}, o + n ≤ 128 → ∀ w ∈ ([⟨m0.regs.X0.toBitVec, tstateBytes⟩,
      ⟨m0.regs.X3.toBitVec, tableEvalsBytes⟩] : List NativeRustcVm.Region),
      Apart (base m0 128 + BitVec.ofNat 64 o) n w.addr w.size := fun {o n} hon w hw ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact c.apart_of_stack hon htok.1
    · exact c.apart_of_stack hon heo.2.2.2.2.1
  have hl32 := Bus.local_ok (o := 0) (n := 32) hS hle_s (by omega) hfr8.kept hfr8.sp
  rw [NativeRustcVm.addr_add_zero] at hl32
  have hl48' := Bus.local_ok (o := 32) (n := 48) hS hle_s (by omega) hfr8.kept hfr8.sp
  have hrod : ∀ q, outs m0 q → ∀ t : NativeRustcVm.Data.Item,
      ¬InRange (rodataAddr t) t.bytes.length q := fun q hq t ↦ hq.elim
    (fun h ↦ not_rodata hts0.footprint.1.2 hRt (fun t ↦ (hT t).2.1) h t)
    (fun h ↦ not_rodata heo.2.1 hRe (fun t ↦ (hT t).2.1) h t)
  have hpc8' : st8.pc = Labels.label NativeRustcVmArm.Vm.TableSumcheck.entryLabel ∧ retOf st8.data = Host.addrOf (k + NativeRustcVmArm.Vm.TablePhase.b7Offset) :=
    hpc8
  have hts8 : TStateAt st8.data.dmem m0.regs.X0.toBitVec a
      { s1 with sponge := s1.sponge.squeeze.2 } := by rw [hd8']; exact hts7
  have hpre8 : TableSumcheckPre a { s1 with sponge := s1.sponge.squeeze.2 } L.tableLogHeights bus
      st8.data := by
    refine ⟨hfr8.stackOk hS rfl hle_s, c.rcAt hat8 hle_s, tablesAt_fr hfr8 hS hle_s hT hrod,
      by rw [e80]; exact hts8, by rw [e80]; exact c.tstateOk hat8 hle_s,
      by rw [e80, e87]; exact c.outOk_sub hat8 hle_s heo, by rw [e80]; exact hRt,
      by rw [e87]; exact hRe, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e80, e87, e81]
      exact ReadIn.fr hfr8 hS hle_s (ReadIn.sub hLin (by decide) (by decide))
    · rw [e81]; exact hL8.heightsAt
    · rw [e80, e87, e82]; exact ReadIn.fr hfr8 hS hle_s hBin
    · rw [e82]; exact hB8
    · rw [e80, e87, e83]
      have h0 := hws (o := 0) (n := 32) (by omega)
      rw [NativeRustcVm.addr_add_zero] at h0
      exact ⟨hl32.1, hl32.2, h0⟩
    · rw [e80, e87, e84]; exact ⟨hl48'.1, hl48'.2, hws (o := 32) (n := 48) (by omega)⟩
  refine Bus.Gkr.Fr.callSpec hfr8 hN hle_s keep_callee slots_le hof
    (hsum a { s1 with sponge := s1.sponge.squeeze.2 } L.tableLogHeights bus) hpc8' hpre8
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q h ↦ ?_, hq.2.2.2.2⟩)
    fun m9 hfr9 hq9 _ ↦ ?_
  · rw [e80, e87] at h
    rcases h with h | h | h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · exact .inl h
  -- The exit.
  have hrun : (tablePhase L bus).run s = (tableSumcheck L.tableLogHeights bus.forms (P.extract 0 2)
      (P.extract 2 5) bus.point (dot (P.extract 2 5) bus.totals)).run
      { s1 with sponge := s1.sponge.squeeze.2 } := by
    rw [tablePhase_run, hg]; rfl
  obtain ⟨q0, q1, q2, -, -⟩ := hq9
  rw [hcp, hfp, e856, ← hrun] at q0 q1 q2
  rw [e87] at q1
  rw [e80] at q2
  exact exit7 hp hS hfr9 fun m' hd' hx0' ↦ ⟨by rw [hx0', q0], fun x s' hr ↦ by
    rw [hd']; exact q1 x s' hr, fun x s' hr ↦ by rw [hd']; exact q2 x s' hr⟩

end

end

end NativeRustcVmArm.Tables.TablePhase
