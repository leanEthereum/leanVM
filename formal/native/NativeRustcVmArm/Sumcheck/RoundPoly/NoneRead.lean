module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.SumE.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Code.Vm.TStateSumcheckRoundPoly.Names
public import NativeRustcVmArm.Sumcheck.RoundPoly.NoneTail

/-!
# `sumcheck_round_poly` in plain mode, after `read_scalar`

After `read_scalar` (`b10`, `none_b10`): a rejection, or the constant into `msg[0]` and
`read_scalars` of the tail (`b11`); after it (`b12`, `none_b12`): a rejection, or the tail's sum
(`sum_e`, `b13`), then `none_b14`.
-/

namespace NativeRustcVmArm.Sumcheck.RoundPoly

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateSumcheckRoundPoly
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

@[expose] public section

/-- The registers `sumcheck_round_poly` keeps in plain mode, before the constant. -/
structure ConstRegs (m0 : MachineData) (m : MachineData) : Prop where
  x19 : m.regs.getXReg .X19 = m0.regs.X5
  x20 : m.regs.getXReg .X20 = m0.regs.X3
  x21 : m.regs.getXReg .X21 = m0.regs.X2
  x22 : m.regs.getXReg .X22 = m0.regs.X0
  x25 : m.regs.getXReg .X25 = m0.regs.X1

end

public section

variable [Host] {a : DecArea} {s : TState} {m0 : MachineData} {k : Nat}

/-- **After `read_scalars`**, at `b12`: the tail's sum, or a rejection. -/
theorem none_b12 (hp : Placed code k)
    (hsum : Spec (Labels.label NativeRustcVmArm.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hpre : RoundPolyPre a s none m0) {p0 : EW} {s0 : TState}
    (hr0 : runR m0 s none = runN m0 p0 s0) {m : MachineData}
    (hf : RFrame m0 m) (hg : NoneRegs m0 m)
    (hhead : NativeRustcVm.EWsAt m.dmem (msgAt m0 + BitVec.ofNat 64 0) [p0])
    (hx0 : m.regs.X0 = okWord ((readScalars (cnt m0 - 2)).run s0).isSome)
    (htail : ∀ tail s1, (readScalars (cnt m0 - 2)).run s0 = some (tail, s1) →
      NativeRustcVm.EWsAt m.dmem (msgAt m0 + BitVec.ofNat 64 32) tail.toList ∧
        TStateAt m.dmem (tAt m0) a s1) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ RoundPolyPost a s none m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b12Offset)⟩ := by
  have hc2 : 2 ≤ cnt m0 := hpre.2.2.2.2.1
  have hc5 : cnt m0 ≤ maxCount := hpre.2.2.2.2.2.1
  have hmc : maxCount = 5 := rfl
  have hwf := wf_envB hpre hf
  have hk12 : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b12Offset) := b12_in_code.trans hp.1 (by simp [b12])
  have hk13 : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b13Offset) := b13_in_code.trans hp.1 (by simp [b13])
  have hl8 : Labels.label NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b18Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b18Offset) NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.label_8_at
  refine exec_then hk12 run_b12 hwf (match_bodyS hpre hf hg.x19) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hf2, -⟩ := RFrame.of_block hpre hf hm2 rfl rfl rfl rfl
  have hm2' : Match (envB m0 m) (after b12 bodyS) st2.data := by
    rw [after_eq run_b12]; exact hm2
  have hX0 : (envB m0 m).regs .X0 = m.regs.X0.toBitVec := rfl
  simp only [PcOk, SBool.eval, Sym.eval, hX0, getLsbD_low_zero] at hpc2
  cases hr1 : (readScalars (cnt m0 - 2)).run s0 with
  | none =>
    rw [hr1] at hx0
    have hpc : st2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b18Offset) := by
      rw [hpc2, hx0]; simp [okWord, hl8]
    obtain ⟨d2, pc2⟩ := st2
    simp only at hpc
    subst hpc
    refine Eventually.mono (fail_spec hp hpre hf2) fun st ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, ?_⟩
    refine post_none ?_ h2 (h3 ▸ hf2.same) h4
    rw [hr0]
    simp [runN, hr1]
  | some p =>
    obtain ⟨tail, s1⟩ := p
    rw [hr1] at hx0
    obtain ⟨htl, hts⟩ := htail tail s1 hr1
    have hsz : tail.size = cnt m0 - 2 := readScalars_size hr1
    have hpc : st2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b13Offset) := by
      rw [hpc2, hx0]; simp [okWord]; rfl
    refine exec_at hk13 run_b13 hwf hpc hm2' fun st3 hm3 hpc3 ↦ ?_
    obtain ⟨hf3, hd3⟩ := RFrame.of_block hpre hf hm3 rfl rfl rfl rfl
    have hg3 := hg.of_block hm3 rfl rfl rfl rfl rfl
    have ht3 : NTailAt m0 a p0 tail s1 st3.data := ⟨hf3, hd3 ▸ hhead, hd3 ▸ htl, hd3 ▸ hts⟩
    have h30 : st3.data.regs.X0.toBitVec = msgAt m0 + BitVec.ofNat 64 32 :=
      reg_msg (r := .X0) (o := 32) hm3 rfl
    have h31 : st3.data.regs.X1.toNat = cnt m0 - 2 := by
      rw [show st3.data.regs.X1 = st3.data.regs.getXReg .X1 from rfl,
        reg_of_match' (r := .X1) (r' := .X23) hm3 rfl]
      exact hg.x23
    have ho := msgOk hpre
    rw [hmc] at ho
    refine call_then hpc3 hsum ?pre fun st4 hpc4 hpost4 ↦ ?_
    case pre =>
      have hr : Readable st3.data st3.data.regs.X0.toBitVec (16 * st3.data.regs.X1.toNat) := by
        rw [h30, h31]
        exact ⟨NativeRustcVm.Mapped.sub (fun i hi ↦ hf3.at_.kept _ (ho.1 i hi)) (by omega),
          NativeRustcVm.NoWrap.sub ho.2.1 (by omega)⟩
      exact ⟨by rw [h31]; omega, hr⟩
    obtain ⟨hsumv, hs4, hsv4⟩ := hpost4
    have hsl : slice st3.data st3.data.regs.X0 st3.data.regs.X1 = tail := by
      unfold slice
      rw [show st3.data.regs.X1.toNat = tail.toList.length by simp [h31, hsz], h30,
        NativeRustcVm.ewsOf_of_ewsAt ht3.tail]
    rw [hsl] at hsumv
    have ht4 := ht3.of_call hpre (by omega) (Nc := sumEStack) (by decide)
      (fun p hp ↦ hs4 p fun h ↦ h.elim (fun h' ↦ Nat.not_lt_zero _ h') hp) hsv4
    obtain ⟨d4, pc4⟩ := st4
    simp only at hpc4
    subst hpc4
    exact none_b14 hp hbl hgr hpre hr0 hr1 (hg3.of_saved hsv4) ht4
      (congrArg EW.c0 hsumv) (congrArg EW.c1 hsumv)

/-- **After `read_scalar`**, at `b10`: the constant into `msg[0]`, `read_scalars`, the rest; or a
rejection. -/
theorem none_b10 (hp : Placed code k)
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hsum : Spec (Labels.label NativeRustcVmArm.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hpre : RoundPolyPre a s none m0) {m : MachineData}
    (hf : RFrame m0 m) (hg : ConstRegs m0 m)
    (hopt : OptEWAt m.dmem (fr m0 + BitVec.ofNat 64 8) ((readScalar.run s).map (·.1)))
    (hnext : NextAt m.dmem (tAt m0) a (readScalar.run s)) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ RoundPolyPost a s none m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b10Offset)⟩ := by
  have c := ctx_of hpre
  have hc2 : 2 ≤ cnt m0 := hpre.2.2.2.2.1
  have hc5 : cnt m0 ≤ maxCount := hpre.2.2.2.2.2.1
  have hmc : maxCount = 5 := rfl
  have hwf := wf_envB hpre hf
  have hm := match_bodyS hpre hf hg.x19
  have hk10 : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b10Offset) := b10_in_code.trans hp.1 (by simp [b10])
  have hk11 : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b11Offset) := b11_in_code.trans hp.1 (by simp [b11])
  have hl8 : Labels.label NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b18Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b18Offset) NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.label_8_at
  have hb0 : (envB m0 m).base 0 = fr m0 := rfl
  refine exec_then hk10 run_b10 hwf hm fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hf2, -⟩ := RFrame.of_block hpre hf hm2 rfl rfl rfl rfl
  have hm2' : Match (envB m0 m) (after b10 bodyS) st2.data := by
    rw [after_eq run_b10]; exact hm2
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, low_W64] at hpc2
  cases h0 : readScalar.run s with
  | none =>
    rw [h0] at hopt
    have htag : (envB m0 m).load 0 8 8 = 0#64 := by
      rw [load_word (v := 0) (by rw [hb0]; exact hopt)]; rfl
    have hpc : st2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b18Offset) := by
      rw [hpc2, htag]; simp [hl8]
    obtain ⟨d2, pc2⟩ := st2
    simp only at hpc
    subst hpc
    refine Eventually.mono (fail_spec hp hpre hf2) fun st ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, ?_⟩
    refine post_none ?_ h2 (h3 ▸ hf2.same) h4
    simp [runR, roundPoly_none_run, h0]
  | some q =>
    obtain ⟨p0, s0⟩ := q
    rw [h0] at hopt
    have hts0 : TStateAt m.dmem (tAt m0) a s0 := hnext p0 s0 h0
    have hr0 : runR m0 s none = runN m0 p0 s0 := by
      simp only [runR, roundPoly_none_run, h0, Option.bind_some]
    have htag : (envB m0 m).load 0 8 8 = 1#64 := by
      rw [load_word (v := 1) (by rw [hb0]; exact hopt.1)]; rfl
    have hpc : st2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b11Offset) := by
      rw [hpc2, htag]; simp; rfl
    refine exec_at hk11 run_b11 hwf hpc hm2' fun st3 hm3 hpc3 ↦ ?_
    have hm3' : Match (envB m0 m) (after b11 (after b10 bodyS)) st3.data := by
      rw [after_eq run_b11]; exact hm3
    -- `b11`'s writes: the constant into `msg[0]`.
    have hno := (msgOk hpre).2.1
    unfold NoWrap at hno
    rw [hmc] at hno
    have hW : ∀ p, Written (envB m0 m) (after b11 (after b10 bodyS)) p →
        (msgAt m0).toNat ≤ p.toNat ∧ p.toNat < (msgAt m0).toNat + 16 := fun p h ↦ by
      have := Written.toNat (r := 1) (lo := 0) (hi := 16) rfl
        (by rw [after_eq run_b11]; decide) h
      omega
    have hWr : ∀ p, Written (envB m0 m) (after b11 (after b10 bodyS)) p →
        InRange (msgAt m0) (16 * maxCount) p := fun p h ↦ by
      have := hW p h
      rw [Sym.inRange_iff (by rw [hmc]; omega)]
      rw [hmc]; omega
    have hs3 := hm3'.sameOutside hwf
    have hk3 : Kept m.dmem st3.data.dmem := hm3'.kept hwf
    have hf3 : RFrame m0 st3.data := hf.after_write hpre (Nc := 0) (by decide)
      (R := Written (envB m0 m) (after b11 (after b10 bodyS)))
      (fun p hp ↦ ⟨Or.inl (hWr p hp), msg_not_fr hpre (hWr p hp)⟩)
      (fun p hp ↦ hs3 p fun h ↦ hp (Or.inl h))
      (Match.sp_eq hm hm3' (by rw [after_eq run_b11]; rfl)) hk3
      (reg_of_match (r := .X28) hm3 rfl) (reg_of_match (r := .X29) hm3 rfl)
    have hts3 : TStateAt st3.data.dmem (tAt m0) a s0 :=
      tstate_keep hpre hs3 hk3 (fun p hp ↦ Or.inl (hWr p hp)) hts0
    have hp0 : NativeRustcVm.EWAt m.dmem (fr m0 + BitVec.ofNat 64 16) p0 := by
      have := hopt.2
      unfold off at this
      rw [NativeRustcVm.addr_add_add] at this
      exact this
    have hp0' := (NativeRustcVm.ewAt_iff.1 hp0)
    have hp24 : NativeRustcVm.WordAt m.dmem (fr m0 + BitVec.ofNat 64 24) p0.c1 := by
      have := hp0'.2
      rw [NativeRustcVm.addr_add_add] at this
      exact this
    have hhead3 : NativeRustcVm.EWsAt st3.data.dmem (msgAt m0 + BitVec.ofNat 64 0) [p0] := by
      have w0 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm3 (r := 1) (o := 0) rfl
        (by decide) (fun i hi ↦ by
          match i, hi with
          | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl)
      have w1 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm3 (r := 1) (o := 8) rfl
        (by decide) (fun i hi ↦ by
          match i, hi with
          | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl)
      rw [NativeRustcVm.ewsAt_singleton, NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add]
      refine ⟨?_, ?_⟩
      · convert w0 using 1
        show p0.c0 = UInt64.ofBitVec ((envB m0 m).load 0 16 8)
        rw [load_word (by rw [hb0]; exact hp0'.1)]
      · convert w1 using 1
        show p0.c1 = UInt64.ofBitVec ((envB m0 m).load 0 24 8)
        rw [load_word (by rw [hb0]; exact hp24)]
    have hg3 : NoneRegs m0 st3.data := by
      refine ⟨x19_of_match hm3 rfl, (reg_of_match (r := .X20) hm3 rfl).trans hg.x20,
        (reg_of_match (r := .X21) hm3 rfl).trans hg.x21,
        (reg_of_match (r := .X22) hm3 rfl).trans hg.x22, ?_⟩
      rw [UInt64.toNat, hm3.regs .X23 _ rfl]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
      show ((m.regs.getXReg .X25).toBitVec - 2#64).toNat = _
      rw [hg.x25]
      have : 2 ≤ m0.regs.X1.toBitVec.toNat := hc2
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (by simpa using this))]
      rfl
    have h30 : st3.data.regs.X0 = m0.regs.X0 :=
      (reg_of_match' (r := .X0) (r' := .X22) hm3 rfl).trans hg.x22
    have h31 : st3.data.regs.X1.toBitVec = msgAt m0 + BitVec.ofNat 64 32 :=
      reg_msg (r := .X1) (o := 32) hm3 rfl
    have h32 : st3.data.regs.X2.toNat = cnt m0 - 2 := by
      have e : st3.data.regs.getXReg .X2 = st3.data.regs.getXReg .X23 :=
        UInt64.toBitVec_inj.mp ((hm3.regs .X2 _ rfl).trans (hm3.regs .X23 _ rfl).symm)
      show (st3.data.regs.getXReg .X2).toNat = _
      rw [e]; exact hg3.x23
    refine call_then hpc3 (hrss a s0) ?pre fun st4 hpc4 hpost4 ↦ ?_
    case pre =>
      simp only [ReadScalarsPre, h30, h31, h32]
      exact ⟨c.stackOk hf3.at_ (by decide), c.rcAt hf3.at_ (by decide), hts3,
        c.tstateOk hf3.at_ (by decide), msgOut hpre hf3 (by decide) (by decide) (by omega)⟩
    simp only [ReadScalarsPost, h30, h31, h32] at hpost4
    obtain ⟨hok4, hxs4, hnext4, hs4, hsv4⟩ := hpost4
    have hR4 : ∀ p, (InRange (msgAt m0 + BitVec.ofNat 64 32) (16 * (cnt m0 - 2)) p ∨
        InRange (tAt m0) tstateBytes p) → Chg m0 p ∧ ¬ InRange (fr m0) 112 p := by
      intro p hp
      rcases hp with hp | hp
      · have := (msg_bounds hpre (o := 32) (by decide) (by omega) hp).1
        exact ⟨Or.inl this, msg_not_fr hpre this⟩
      · exact ⟨Or.inr (Or.inl hp), t_not_fr hpre hp⟩
    have hf4 : RFrame m0 st4.data :=
      hf3.after_call hpre (Nc := readScalarsStack) (by decide) hR4
        (fun p hp ↦ hs4 p fun h ↦ hp (or_assoc.2 h)) hsv4
    have hhead4 : NativeRustcVm.EWsAt st4.data.dmem (msgAt m0 + BitVec.ofNat 64 0) [p0] := by
      refine NativeRustcVm.BytesAt.of_sameOutside hhead3 hs4 fun i hi hR ↦ ?_
      rw [NativeRustcVm.length_ewsBytes] at hi
      simp only [List.length_singleton] at hi
      have hin : InRange (msgAt m0) (16 * maxCount)
          (msgAt m0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 i) := by
        rw [NativeRustcVm.addr_add_add]
        exact NativeRustcVm.inRange_add (by omega) (by omega)
      rcases hR with hR | hR | hR
      · have := (msg_bounds hpre (o := 32) (by decide) (by omega) hR).2.1
        rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)] at this
        omega
      · exact t_not_msg hpre hR hin
      · exact stack_not_msg hpre (callee_stack hpre hf3 (by decide) hR) hin
    have hg4 := hg3.of_saved hsv4
    obtain ⟨d4, pc4⟩ := st4
    simp only at hpc4
    subst hpc4
    refine none_b12 hp hsum hbl hgr hpre hr0 hf4 hg4 hhead4 hok4 fun tail s1 h ↦
      ⟨hxs4 tail s1 h, hnext4 tail s1 h⟩

end

end NativeRustcVmArm.Sumcheck.RoundPoly
