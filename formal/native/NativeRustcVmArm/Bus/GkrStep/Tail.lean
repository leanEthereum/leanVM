module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.Bus.GkrStep.Prods

/-!
# `gkr_step`'s coordinates and new values

`b19` to `b21` grind (`bit_length` of `(step << last) - 1`, at most `3`, so `0` bits); `b22`
samples the `step` coordinates `y` into the frame at `1264`; `b23` to `b26` evaluate each child
there (`multilinear_eval`), writing the values; `b26` checks `|xs| + step ≤ 63`; `b27`, `b28`
write the point's length and `y`: `AtCopy`, at `.LGkrStep_11`.
-/

namespace NativeRustcVmArm.Bus.GkrStep

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrStep
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)

public section

/-- The registers kept from the check on: X19 to X23, X26, X27. -/
structure TRegs (m0 : MachineData) (n : Nat) (m : MachineData) : Prop where
  x19 : m.regs.getXReg .X19 = m0.regs.X3
  x20 : m.regs.getXReg .X20 = m0.regs.X1
  x21 : m.regs.getXReg .X21 = m0.regs.X0
  x22 : m.regs.getXReg .X22 = m0.regs.X2
  x23 : (m.regs.getXReg .X23).toNat = n
  x26 : (m.regs.getXReg .X26).toBitVec = BitVec.ofNat 64 (2 ^ m0.regs.X1.toNat)
  x27 : (m.regs.getXReg .X27).toBitVec = loc m0 1024

theorem TRegs.call {m0 : MachineData} {n : Nat} {m m' : MachineData} (hr : TRegs m0 n m)
    (hcs : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r) : TRegs m0 n m' :=
  ⟨(hcs _ rfl).trans hr.x19, (hcs _ rfl).trans hr.x20, (hcs _ rfl).trans hr.x21,
    (hcs _ rfl).trans hr.x22, by rw [hcs _ rfl]; exact hr.x23, by rw [hcs _ rfl]; exact hr.x26,
    by rw [hcs _ rfl]; exact hr.x27⟩

theorem TRegs.block [Labels] {m0 : MachineData} {n : Nat} {m m' : MachineData}
    {rs : List (BitVec 64 × Nat)} {S : SState} (hr : TRegs m0 n m)
    (hm : Match (Env.ofMachine m rs) S m')
    (hk : [XReg.X20, .X21, .X22, .X23, .X26, .X27].all
      (fun r ↦ S.reg r == some (.reg r)) = true)
    (h19 : (m'.regs.getXReg .X19) = m0.regs.X3) : TRegs m0 n m' := by
  have K := Bus.KeepRegs.of_block hm hk
  exact ⟨h19, (K _ (by simp)).trans hr.x20, (K _ (by simp)).trans hr.x21,
    (K _ (by simp)).trans hr.x22, by rw [K _ (by simp)]; exact hr.x23,
    by rw [K _ (by simp)]; exact hr.x26, by rw [K _ (by simp)]; exact hr.x27⟩

/-- `(step << last) - 1` is at most `3`. -/
theorem lsl_sub_le (x y : UInt64) (hx : x.toNat = 1 ∨ x.toNat = 2) (hy : y.toNat ≤ 1) :
    (BinOp.apply .sub .W64 (BinOp.apply .lslv .W64 x.toBitVec y.toBitVec)
      (BitVec.ofNat 64 1)).toNat ≤ 3 := by
  have hx' : x = 1 ∨ x = 2 := hx.elim (fun h ↦ .inl (UInt64.toNat_inj.mp h))
    (fun h ↦ .inr (UInt64.toNat_inj.mp h))
  have hy' : y = 0 ∨ y = 1 := by
    rcases (show y.toNat = 0 ∨ y.toNat = 1 by omega) with h | h
    · exact .inl (UInt64.toNat_inj.mp h)
    · exact .inr (UInt64.toNat_inj.mp h)
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> decide

/-- A bit length of at most `3`: below `3`. -/
theorem bitLength_lt (n : Nat) (h : n ≤ 3) : LeanVM.Protocol.Verifier.bitLength n < 3 := by
  unfold LeanVM.Protocol.Verifier.bitLength
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

/-- `x < 3` unsigned, of a word below `3`. -/
theorem ult3 (x : UInt64) (h : x.toNat < 3) :
    CmpOp.ult.apply .W32 x.toBitVec (BitVec.ofNat 64 3) = true := by
  have : x = 0 ∨ x = 1 ∨ x = 2 := by
    rcases (show x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 by omega) with h | h | h
    · exact .inl (UInt64.toNat_inj.mp h)
    · exact .inr (.inl (UInt64.toNat_inj.mp h))
    · exact .inr (.inr (UInt64.toNat_inj.mp h))
  rcases this with rfl | rfl | rfl <;> rfl

/-- **At `b23`** (`k + NativeRustcVmArm.Vm.GkrStep.b23Offset`): the coordinates `y` sampled into the frame at `1264`. -/
structure AtEval [Labels] (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData)
    (xs h0 h1 h2 y : Array EW) (s' : TState) (m : MachineData) : Prop where
  fr : Fr m0 1392 gkrStepStack slots keep (outs m0) m
  regs : TRegs m0 xs.size m
  size : xs.size + m0.regs.X1.toNat ≤ busPointCap
  hxs : NativeRustcVm.EWsAt m.dmem (loc m0 16) xs.toList
  c0 : NativeRustcVm.EWsAt m.dmem (loc m0 1024) h0.toList
  c1 : NativeRustcVm.EWsAt m.dmem (loc m0 1088) h1.toList
  c2 : NativeRustcVm.EWsAt m.dmem (loc m0 1152) h2.toList
  s0' : h0.size = 2 ^ m0.regs.X1.toNat
  s1' : h1.size = 2 ^ m0.regs.X1.toNat
  s2' : h2.size = 2 ^ m0.regs.X1.toNat
  ys : NativeRustcVm.EWsAt m.dmem (loc m0 1264) y.toList
  ysize : y.size = m0.regs.X1.toNat
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a s'
  run : run0 s0 g0 m0 =
    some (⟨#[multilinearEval h0 y, multilinearEval h1 y, multilinearEval h2 y], y ++ xs⟩, s')

variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

/-- **The second grind and the coordinates** (`b19` to `b22`). -/
theorem coords_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    {xs h0 h1 h2 : Array EW} {s3 : TState}
    (heval : ∀ y s' m, AtEval a s0 g0 m0 xs h0 h1 h2 y s' m →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b23Offset)⟩)
    {m : MachineData} (hi : AtTail a s0 g0 m0 xs h0 h1 h2 s3 m) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b19Offset)⟩ := by
  have hS := pre_stack h
  have hN : gkrStepStack ≤ m0.regs.SP.toNat := hS.2.1
  have cx := ctx h
  have hxl := xs_le hi.size
  have hstep := pre_step h
  have R0 : TRegs m0 xs.size m := ⟨hi.x19, hi.x20, hi.x21, hi.x22, hi.x23, hi.x26, hi.x27⟩
  -- `b19`: `bit_length((step << last) - 1)`.
  refine Fr.runBlock hS N_ge rfl hi.fr (b19_in_code.trans hp.1 (by simp [b19])) run_b19 rfl rfl
    (by decide) (by decide) fun st hfr hd hm hpc ↦ ?_
  have R1 := R0.block hm (by decide +kernel) ((reg_of hm rfl).trans hi.x19)
  have hv : st.data.regs.X0.toNat ≤ 3 := by
    show (st.data.regs.getXReg .X0).toBitVec.toNat ≤ 3
    rw [hm.regs .X0 _ rfl]
    show (BinOp.apply .sub .W64 (BinOp.apply .lslv .W64 (m.regs.getXReg .X20).toBitVec
      (m.regs.getXReg .X22).toBitVec) (BitVec.ofNat 64 1)).toNat ≤ 3
    rw [hi.x20, hi.x22]
    exact lsl_sub_le _ _ hstep (pre_last h)
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b19_length, NativeRustcVmArm.Vm.GkrStep.b19Length, show k + NativeRustcVmArm.Vm.GkrStep.b19Offset + 3 = k + NativeRustcVmArm.Vm.GkrStep.b20Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b19_length, NativeRustcVmArm.Vm.GkrStep.b19Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b19_next] at hpc
  refine leaf_call h le_bl hbl (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1
      fun _ hq' ↦ .inr hq', hq.2.2⟩) hfr hpc trivial fun m2 hfr2 hq2 hcs2 hc2 hk2 ↦ ?_
  have hx2 : m2.regs.X0.toNat < 3 := by rw [hq2.1]; exact bitLength_lt _ hv
  have R2 := R1.call hcs2
  -- `b20`: the grind, of `0` bits.
  have hwf3 := Bus.wf_frame hS N_ge hfr2.kept
  have hm3 := Bus.match_frame hS N_ge rfl hfr2.sp
  refine exec_then (b20_in_code.trans hp.1 (by simp [b20])) run_b20 hwf3 hm3 fun st3 hm3' hpc3 ↦ ?_
  have hfr3 : Fr m0 1392 gkrStepStack slots keep (outs m0) st3.data :=
    Fr.ofBlock hfr2 hm3 hm3' hwf3 rfl rfl rfl (by decide)
  have hd3 : st3.data.dmem = m2.dmem := hm3'.dmem_eq hwf3 rfl
  have R3 := R2.block hm3' (by decide +kernel) ((reg_of hm3' rfl).trans R2.x19)
  have g0' : st3.data.regs.X0 = m0.regs.X0 := (reg_of hm3' (r := .X0) (r' := .X21) rfl).trans R2.x21
  have g1 : grindBits st3.data = 0 := by
    have hlt : SBool.eval (Env.ofMachine m2 [(base m0 1392, 1392)])
        (.cmp .ult .W32 (.reg .X0) (.lit 3)) = true := ult3 _ hx2
    have : (st3.data.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 0 := by
      rw [hm3'.regs .X1 _ rfl]
      simp only [Sym.eval, hlt, ↓reduceIte]
    unfold grindBits
    rw [show st3.data.regs.X1.toNat = (st3.data.regs.getXReg .X1).toBitVec.toNat from rfl, this]
    rfl
  have hts2 := ts_leaf h hfr le_bl hc2 hk2 (by rw [hd]; exact hi.ts)
  have hat3 := Fr.at_ cx hfr3 (outs_not_rc h)
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b20_length, NativeRustcVmArm.Vm.GkrStep.b20Length, show k + NativeRustcVmArm.Vm.GkrStep.b20Offset + 4 = k + NativeRustcVmArm.Vm.GkrStep.b21Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b20_length, NativeRustcVmArm.Vm.GkrStep.b20Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b20_next] at hpc3
  refine Fr.callSpec hfr3 hN le_grind keep_callee slots_le (outs_not_frame h) (hgr s3) hpc3
    ⟨hfr3.stackOk hS rfl le_grind, cx.rcAt hat3 le_grind, by rw [g0', hd3]; exact hts2,
      by rw [g0']; exact cx.tstateOk hat3 le_grind, by rw [g1]; decide⟩
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ by
      rw [g0'] at hq'
      exact hq'.elim (fun h' ↦ .inr (.inl h')) .inl, hq.2.2.2⟩)
    fun m4 hfr4 hq4 hcs4 ↦ ?_
  obtain ⟨hx4, hnext4, hs4, hsv4⟩ := hq4
  rw [g1, grind_zero_run] at hx4 hnext4
  rw [g0'] at hnext4 hs4
  have hts4 : TStateAt m4.dmem m0.regs.X0.toBitVec a s3 := hnext4 () s3 rfl
  have R4 := R3.call hcs4
  -- the frame's elements across `bit_length` and the grind
  have keep4 : ∀ o (zs : List EW), o + 16 * zs.length ≤ 1392 →
      NativeRustcVm.EWsAt m.dmem (loc m0 o) zs → NativeRustcVm.EWsAt m4.dmem (loc m0 o) zs :=
    fun o zs ho hz ↦ ews_call hS hfr3.sp le_grind (X := InRange m0.regs.X0.toBitVec tstateBytes)
      (NativeRustcVm.SameOutside.mono hs4 fun _ hq ↦ hq.symm) ho (fun i _ ↦ loc_not_ts h (by omega))
      (by rw [hd3]; exact ews_leaf hS hfr.sp le_bl hc2 ho (by rw [hd]; exact hz))
  -- `b21`
  refine Fr.runBlock hS N_ge rfl hfr4 (b21_in_code.trans hp.1 (by simp [b21])) run_b21 rfl rfl
    (by decide) (by decide) fun st5 hfr5 hd5 hm5 hpc5 ↦ ?_
  have hc5 : SBool.eval (Env.ofMachine m4 [(base m0 1392, 1392)]) (.not (.bit .W32 (.reg .X0) 0)) =
      false := by
    show (!(low .W32 (m4.regs.getXReg .X0).toBitVec).getLsbD 0) = false
    rw [show m4.regs.getXReg .X0 = m4.regs.X0 from rfl, hx4, okWord_bit]
    rfl
  simp only [PcOk, hc5, Bool.false_eq_true, ↓reduceIte, NativeRustcVmArm.Vm.GkrStep.b21_length, NativeRustcVmArm.Vm.GkrStep.b21Length,
    show k + NativeRustcVmArm.Vm.GkrStep.b21Offset + 1 = k + NativeRustcVmArm.Vm.GkrStep.b22Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b21_length, NativeRustcVmArm.Vm.GkrStep.b21Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b21_next] at hpc5
  have R5 := R4.block hm5 (by decide +kernel) ((reg_of hm5 rfl).trans R4.x19)
  -- `b22`: the coordinates.
  have hwf6 := Bus.wf_frame hS N_ge hfr5.kept
  have hm6 := Bus.match_frame hS N_ge rfl hfr5.sp
  refine at_pc hpc5 (exec_then (b22_in_code.trans hp.1 (by simp [b22])) run_b22 hwf6 hm6
    fun st6 hm6' hpc6 ↦ ?_)
  have hfr6 : Fr m0 1392 gkrStepStack slots keep (outs m0) st6.data :=
    Bus.Fr.block hfr5 hN N_ge hm6' hwf6 rfl (by decide +kernel) (by decide) slots_le
  have R6 := R5.block hm6' (by decide +kernel) ((reg_of hm6' rfl).trans R5.x19)
  have hw22 : ∀ w ∈ (Transcript.after b22 frS).mem, w.r = 0 ∧ 1264 ≤ w.off := by decide +kernel
  rw [Transcript.after_eq run_b22] at hw22
  have keep6 : ∀ o (zs : List EW), o + 16 * zs.length ≤ 1264 →
      NativeRustcVm.EWsAt m.dmem (loc m0 o) zs → NativeRustcVm.EWsAt st6.data.dmem (loc m0 o) zs :=
    fun o zs ho hz ↦ ews_block hm6' hwf6 (L := 16 * zs.length) (by omega)
      (fun w hw ↦ ⟨(hw22 w hw).1, .inr (by have := (hw22 w hw).2; omega)⟩)
      (Nat.le_refl _) (by rw [hd5]; exact keep4 o zs (by omega) hz)
  have hts6 := ts_block h hm6' hwf6 (by decide +kernel) (by rw [hd5]; exact hts4)
  have n0 : st6.data.regs.X0 = m0.regs.X0 := (reg_of hm6' (r := .X0) (r' := .X21) rfl).trans R5.x21
  have n1 : st6.data.regs.X1.toBitVec = loc m0 1264 := by
    show (st6.data.regs.getXReg .X1).toBitVec = _
    rw [hm6'.regs .X1 _ rfl]; rfl
  have n2 : st6.data.regs.X2.toNat = m0.regs.X1.toNat := by
    rw [show st6.data.regs.X2 = m0.regs.X1 from (reg_of hm6' (r := .X2) (r' := .X20) rfl).trans
      R5.x20]
  have hat6 := Fr.at_ cx hfr6 (outs_not_rc h)
  have hn : 16 * m0.regs.X1.toNat ≤ 32 := by omega
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b22_length, NativeRustcVmArm.Vm.GkrStep.b22Length, show k + NativeRustcVmArm.Vm.GkrStep.b22Offset + 8 = k + NativeRustcVmArm.Vm.GkrStep.b23Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b22_length, NativeRustcVmArm.Vm.GkrStep.b22Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b22_next] at hpc6
  refine Fr.callLocal (o := 1264) (n := 16 * m0.regs.X1.toNat)
    (X := fun q ↦ InRange (loc m0 1264) (16 * m0.regs.X1.toNat) q ∨
      InRange m0.regs.X0.toBitVec tstateBytes q)
    hfr6 hN le_samp keep_callee (slots_lo (by omega)) (by omega) (outs_not_frame h)
    (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inl h')) (hsc s3) hpc6 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩)
    fun m7 hfr7 hq7 hcs7 hs7 ↦ ?_
  · refine ⟨hfr6.stackOk hS rfl le_samp, cx.rcAt hat6 le_samp, by rw [n0]; exact hts6,
      by rw [n0]; exact cx.tstateOk hat6 le_samp, ?_⟩
    rw [n0, n1, n2]
    exact cx.outOk hat6 le_samp (o := 1264) (by omega)
  · rw [n0, n1, n2] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr hq')
    · exact .inl hq'
  · obtain ⟨⟨ys, s', hrun, hys, hts7⟩, -, -⟩ := hq7
    rw [n0] at hts7
    rw [n1] at hys
    rw [n2] at hrun
    have keep7 : ∀ o (zs : List EW), o + 16 * zs.length ≤ 1264 →
        NativeRustcVm.EWsAt m.dmem (loc m0 o) zs → NativeRustcVm.EWsAt m7.dmem (loc m0 o) zs :=
      fun o zs ho hz ↦ ews_call hS hfr6.sp le_samp hs7 (by omega) (fun i hi hq ↦ hq.elim
        (fun h' ↦ not_loc' hS (by omega) (by omega) (by omega) h')
        (fun h' ↦ loc_not_ts h (by omega) h')) (keep6 o zs ho hz)
    have hl0 : h0.toList.length = 2 ^ m0.regs.X1.toNat := by rw [Array.length_toList, hi.s0']
    have hl1 : h1.toList.length = 2 ^ m0.regs.X1.toNat := by rw [Array.length_toList, hi.s1']
    have hl2 : h2.toList.length = 2 ^ m0.regs.X1.toNat := by rw [Array.length_toList, hi.s2']
    have hn' := two_pow_le h
    exact heval ys s' m7
      { fr := hfr7
        regs := R6.call hcs7
        size := hi.size
        hxs := keep7 16 _ (by omega) hi.hxs
        c0 := keep7 1024 _ (by omega) hi.c0
        c1 := keep7 1088 _ (by omega) hi.c1
        c2 := keep7 1152 _ (by omega) hi.c2
        s0' := hi.s0'
        s1' := hi.s1'
        s2' := hi.s2'
        ys := hys
        ysize := sampleChallenges_size hrun
        ts := hts7
        run := by rw [hi.run, hrun]; rfl }

end

end NativeRustcVmArm.Bus.GkrStep
