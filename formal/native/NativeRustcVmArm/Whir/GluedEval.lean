module

public import NativeRustcVmArm.Code.Vm.EqEval.Names
public import NativeRustcVmArm.Code.Vm.GluedEval.Names
public import NativeRustcVmArm.Code.Vm.InducedWeight.Names
public import NativeRustcVmArm.Whir.GluedEval.Exec
public import NativeRustcVmArm.Whir.MathFrame

/-!
# `glued_eval`

`b0` reads the glued claim's `kind`. Kind `1` (`induced μ queries weights`): `b1` passes `μ`, the
queries' and the weights' slices (their buffers' counts, below `231`) and the point to
`induced_weight` and jumps there (a tail call), whose contract ends the function. Kind `0`
(`eq z`): `b2` saves X30, X19 in a 16-byte frame and calls `eq_eval` on `z` (its buffer's count,
below `31`) and the point; `b3` stores `Some` of the result and returns.
-/

namespace NativeRustcVmArm.Whir.GluedEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GluedEval
open NativeVm.Model NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm.Transcript (off OptEWAt)

public section

theorem stack_le : 16 + eqEvalStack ≤ gluedEvalStack ∧ 16 ≤ gluedEvalStack ∧
    inducedWeightStack ≤ gluedEvalStack := by
  decide

theorem load_kind {env : Env} {w : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (env.base 1 + BitVec.ofNat 64 24) w) :
    env.load 1 24 8 = w.toBitVec := load_word h

theorem eight_add (p : BitVec 64) (o : Nat) : off p o + 8#64 = off p (o + 8) := by
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off, off, addr_add]

/-- The count of a buffer, below its cap, as the executor compares it. -/
theorem count_ult {n N : Nat} (h : n ≤ N) (hN : N + 1 < 2 ^ 64) :
    (n.toUInt64.toBitVec).ult (BitVec.ofNat 64 (N + 1)) = true := by
  rw [toBitVec_ult_ofNat hN, natCast_toUInt64_toNat (by omega)]
  simp
  omega

variable [Host] {k : Nat}

/-- **`glued_eval`'s contract.** -/
theorem gluedEval_spec (hp : Placed code k)
    (heq : Spec (label NativeRustcVmArm.Vm.EqEval.entryLabel) EqEvalPre EqEvalPost)
    (hind : Spec (label NativeRustcVmArm.Vm.InducedWeight.entryLabel) InducedWeightPre InducedWeightPost)
    (g : GluedClaimW) : Spec (label NativeRustcVmArm.Vm.GluedEval.entryLabel) (GluedEvalPre g) (GluedEvalPost g) := by
  intro m ⟨hS, hg, hgin, hx, hout⟩
  obtain ⟨hsle1, hsle2, hsle3⟩ := stack_le
  rw [show Labels.label NativeRustcVmArm.Vm.GluedEval.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.GluedEval.b0Offset) from hp.label NativeRustcVmArm.Vm.GluedEval.entry_at]
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GluedEval.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let p := m.regs.X1.toBitVec
  let fb := m.regs.SP.toBitVec - BitVec.ofNat 64 16
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hsle2
  let env := Env.ofMachine m [(fb, 16), (p, 6064)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨hfmap, hfnw⟩, ⟨hgin.1.1, hgin.1.2⟩, trivial⟩
      (List.pairwise_pair.mpr (apart_frame hgin.2 hsle2 hS.2.1).symm)
  have hm : Match env entryS m :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hsle2 rfl, rfl, fun h ↦ absurd h (by decide),
        trivial⟩
      (by simp [Sym.eval, fb])
      ⟨by simp [Sym.eval, p]; rfl, trivial⟩ trivial trivial trivial
  have hb1 : env.base 1 = p := rfl
  have hload : ∀ {o : Nat} {w : UInt64}, NativeRustcVm.WordAt m.dmem (off p o) w →
      env.load 1 o 8 = w.toBitVec := fun h ↦ load_word h
  have hgb : gluedBytes = 6064 := rfl
  have hsc : stackCap = 30 := rfl
  refine exec_then hk0 run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  obtain ⟨-, -, -, hw⟩ := hg
  cases hgw : g.weight with
  | eq z =>
    rw [hgw] at hw
    obtain ⟨hkind, hzlen, hzw, hzs⟩ := hw
    rw [hload hkind, show ((0 : UInt64).toBitVec == BitVec.ofNat 64 0) = true from rfl] at hpc1
    simp only [↓reduceIte] at hpc1
    rw [show Labels.label NativeRustcVmArm.Vm.GluedEval.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.GluedEval.b2Offset) from hp.label (j := NativeRustcVmArm.Vm.GluedEval.b2Offset) NativeRustcVmArm.Vm.GluedEval.label_2_at] at hpc1
    have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GluedEval.b2Offset) := b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk2 (exec_after run_b0 run_b2) hwf hpc1 hm1 fun st2 hm2 hpc2 ↦ ?_
    have hfr : Frame m 16 gluedEvalStack slots [⟨m.regs.X0.toBitVec, 24⟩] st2.data :=
      Frame.of_entry hS hsle2 hwf hm2 rfl (after_eq (exec_after run_b0 run_b2) ▸ b2_frame).1
        (after_eq (exec_after run_b0 run_b2) ▸ b2_frame).2.2
        (after_eq (exec_after run_b0 run_b2) ▸ b2_frame).2.1
    have hz30 : z.toList.length ≤ 30 := hzlen
    have hzl := hload (o := 40) hzw
    have hx0 : st2.data.regs.X0 = UInt64.ofBitVec (off p 48) := reg_eq <| by
      refine (hm2.regs .X0 _ rfl).trans ?_
      sym_simp
      rw [hzl, count_ult hz30 (by decide)]
      simp only [↓reduceIte]
      rw [hb1]
      rfl
    have hx1 : st2.data.regs.X1 = z.toList.length.toUInt64 := reg_eq <| by
      refine (hm2.regs .X1 _ rfl).trans ?_
      sym_simp
      rw [hzl, count_ult hz30 (by decide)]
      simp only [↓reduceIte]
      rfl
    have hx2 : st2.data.regs.X2 = m.regs.X2 := reg_eq ((hm2.regs .X2 _ rfl).trans rfl)
    have hx3 : st2.data.regs.X3 = m.regs.X3 := reg_eq ((hm2.regs .X3 _ rfl).trans rfl)
    have hx19 : (st2.data.regs.getXReg .X19).toBitVec = m.regs.X0.toBitVec := hm2.regs .X19 _ rfl
    -- the bytes `b2` keeps: outside the frame
    have hsame2 := same_region hm2 hwf (r := 0) rfl (after_eq (exec_after run_b0 run_b2) ▸ b2_mem)
    have hkeep : ∀ {a : BitVec 64} {n : Nat}, NoWrap a n → Apart a n fb 16 → ∀ i < n,
        st2.data.dmem.get? (a + BitVec.ofNat 64 i) = m.dmem.get? (a + BitVec.ofNat 64 i) :=
      fun hna hap i hi ↦ hsame2 _ (not_inRange_of_apart hap hna hfnw hi)
    have hgap : Apart p 6064 fb 16 := apart_frame hgin.2 hsle2 hS.2.1
    have hxap : Apart m.regs.X2.toBitVec (16 * m.regs.X3.toNat) fb 16 :=
      apart_frame hx.2 hsle2 hS.2.1
    have hpre : EqEvalPre st2.data := by
      refine ⟨hfr.stackOk hS rfl hsle1, ?_, ?_⟩
      · rw [hx0, hx1]
        refine hfr.sliceOk hS hsle1 (WhirIn.sliceOk hgin ?_)
        rw [natCast_toUInt64_toNat (by omega)]
        show 48 + 16 * _ ≤ 6064
        omega
      · rw [hx2, hx3]; exact hfr.sliceOk hS hsle1 hx
    refine call_then hpc2 heq hpre fun st3 hpc3 ⟨hval, hch, hsv⟩ ↦ ?_
    have hfr3 := hfr.call hS hsle1 (by decide) (changesIn_of_changes hch) hsv
    have hz : slice st2.data st2.data.regs.X0 st2.data.regs.X1 = z := by
      rw [hx0, hx1, slice, natCast_toUInt64_toNat (by omega), UInt64.toBitVec_ofBitVec,
        NativeRustcVm.ewsOf_congr (d := m.dmem) fun i hi ↦ ?_]
      · rw [show off p 48 = off p 40 + 8#64 from (eight_add p 40).symm,
          NativeRustcVm.ewsOf_of_ewsAt hzs, Array.toArray_toList]
      · rw [off, addr_add]
        exact hkeep hgin.1.2 hgap _ (by omega)
    have hpt : slice st2.data st2.data.regs.X2 st2.data.regs.X3 = slice m m.regs.X2 m.regs.X3 := by
      rw [hx2, hx3, slice, slice, NativeRustcVm.ewsOf_congr fun i hi ↦ hkeep hx.1.2 hxap i hi]
    rw [hz, hpt] at hval
    have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.GluedEval.b3Offset) := hpc3
    have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GluedEval.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
    let o := m.regs.X0.toBitVec
    let env3 := Env.ofMachine st3.data [(fb, 16), (o, 24)]
    have hwf3 : env3.WF :=
      Env.wf_of ⟨⟨fun i hi ↦ hfr3.kept _ (hfmap i hi), hfnw⟩,
          ⟨fun i hi ↦ hfr3.kept _ (hout.1.1 i hi), hout.1.2⟩, trivial⟩
        (List.pairwise_pair.mpr (apart_frame hout.2 hsle2 hS.2.1).symm)
    have hm3 : Match env3 retS st3.data :=
      match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hsle2 rfl, rfl,
          fun h ↦ absurd h (by decide), trivial⟩
        (by rw [hfr3.sp]; simp [Sym.eval, fb])
        ⟨by
          show (st3.data.regs.getXReg .X19).toBitVec = _
          rw [hsv.1 .X19 rfl, hx19]
          simp [Sym.eval, o], trivial⟩ trivial trivial trivial
    refine exec_at hk3 run_b3 hwf3 hpc3' hm3 fun st4 hm4 hpc4 ↦ Eventually.done _ ?_
    obtain ⟨hsaved, hx30⟩ :=
      hfr3.ret hm4 hwf3 (List.mem_map.mpr ⟨(0, .X30), by simp [slots], rfl⟩)
        (after_eq run_b3 ▸ b3_restores)
    have hb31 : env3.regions[1]? = some (o, 24) := rfl
    refine ⟨hpc4.trans (by simp only [retOf, hx30]), ⟨?_, ?_⟩, ?_, hsaved⟩
    · have := Match.wordAt_write hm4 hb31 (o := 0) (by decide) (v := .lit 1) (by decide)
      rw [NativeRustcVm.addr_add_zero] at this
      exact this
    · rw [NativeRustcVm.ewAt_iff, hgw, show GluedWeight.eval (.eq z) (slice m m.regs.X2 m.regs.X3) =
        ewRet st3.data from hval.symm]
      refine ⟨Match.wordAt_write hm4 hb31 (o := 8) (by decide) (v := .reg .X0)
        (by decide), ?_⟩
      have := Match.wordAt_write hm4 hb31 (o := 16) (by decide) (v := .reg .X1)
        (by decide)
      rwa [show off o 8 + 8#64 = o + BitVec.ofNat 64 16 from eight_add o 8] 
    · intro a ha
      rw [hm4.get?_mem0 hwf3 fun hw ↦ ha (.inl ⟨_, List.mem_singleton_self _,
        Written.inRange hb31 hout.1.2 (after_eq run_b3 ▸ b3_mem) hw⟩)]
      exact hfr3.same a ha
  | induced mu queries weights =>
    rw [hgw] at hw
    obtain ⟨hkind, hmu, hmuw, ⟨hql, hqw, hqs⟩, ⟨hwl, hww, hws⟩⟩ := hw
    rw [hload hkind, show ((1 : UInt64).toBitVec == BitVec.ofNat 64 0) = false from rfl] at hpc1
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
    have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.GluedEval.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk1 (exec_after run_b0 run_b1) hwf hpc1 hm1 fun st2 hm2 hpc2 ↦ ?_
    have hd2 : st2.data.dmem = m.dmem := hm2.dmem_eq hwf rfl
    have hsv2 : Saved m st2.data :=
      Match.saved hm hm2 hwf rfl (after_eq (exec_after run_b0 run_b1) ▸ b1_keeps)
    have hfr : Frame m 0 gluedEvalStack [] [⟨m.regs.X0.toBitVec, 24⟩] st2.data :=
      Frame.of_saved hsv2 hd2
    have hq230 : queries.toList.length ≤ 230 := hql
    have hw230 : weights.toList.length ≤ 230 := hwl
    have hql' := hload (o := 528) hqw
    have hwl' := hload (o := 2376) hww
    have hx0 : st2.data.regs.X0 = m.regs.X0 := reg_eq ((hm2.regs .X0 _ rfl).trans rfl)
    have hx1 : st2.data.regs.X1 = mu.toUInt64 := reg_eq <| by
      refine (hm2.regs .X1 _ rfl).trans ?_; sym_simp; rw [hload (o := 32) hmuw]; rfl
    have hx2 : st2.data.regs.X2 = UInt64.ofBitVec (off p 536) := reg_eq <| by
      refine (hm2.regs .X2 _ rfl).trans ?_
      sym_simp
      rw [hql', count_ult hq230 (by decide)]
      simp only [↓reduceIte]
      rw [hb1]
      rfl
    have hx3 : st2.data.regs.X3 = queries.toList.length.toUInt64 := reg_eq <| by
      refine (hm2.regs .X3 _ rfl).trans ?_
      sym_simp
      rw [hql', count_ult hq230 (by decide)]
      simp only [↓reduceIte]
      rfl
    have hx4 : st2.data.regs.X4 = UInt64.ofBitVec (off p 2384) := reg_eq <| by
      refine (hm2.regs .X4 _ rfl).trans ?_
      sym_simp
      rw [hwl', count_ult hw230 (by decide)]
      simp only [↓reduceIte]
      rw [hb1]
      rfl
    have hx5 : st2.data.regs.X5 = weights.toList.length.toUInt64 := reg_eq <| by
      refine (hm2.regs .X5 _ rfl).trans ?_
      sym_simp
      rw [hwl', count_ult hw230 (by decide)]
      simp only [↓reduceIte]
      rfl
    have hx6 : st2.data.regs.X6 = m.regs.X2 := reg_eq ((hm2.regs .X6 _ rfl).trans rfl)
    have hx7 : st2.data.regs.X7 = m.regs.X3 := reg_eq ((hm2.regs .X7 _ rfl).trans rfl)
    have hx30 : st2.data.regs.X30 = m.regs.X30 := reg_eq ((hm2.regs .X30 _ rfl).trans rfl)
    have hmu' : mu.toUInt64.toNat = mu := natCast_toUInt64_toNat (by omega)
    have hpre : InducedWeightPre st2.data := by
      refine ⟨hfr.stackOk hS rfl (by omega), ?_, ?_, ?_, ?_⟩
      · rw [hx2, hx3, UInt64.toBitVec_ofBitVec, natCast_toUInt64_toNat (by omega)]
        refine ⟨hfr.readable (Readable.sub hgin.1 ?_), hfr.offStack hS (by omega)
          (OffStack.sub hgin.2 hgin.1.2 ?_)⟩ <;>
        · show 536 + 8 * _ ≤ 6064
          omega
      · rw [hx4, hx5]
        refine hfr.sliceOk hS (by omega) (WhirIn.sliceOk hgin ?_)
        rw [natCast_toUInt64_toNat (by omega)]
        show 2384 + 16 * _ ≤ 6064
        omega
      · rw [hx6, hx7]; exact hfr.sliceOk hS (by omega) hx
      · rw [hx0]
        exact ⟨hfr.readable hout.1, hfr.offStack hS (by omega) hout.2⟩
    refine (Spec.apply hind hpc2 hpre).mono fun st' ⟨hpc', hval, hch, hsv⟩ ↦
      ⟨hpc'.trans (by simp only [retOf, hx30]), ?_, ?_, hsv2.trans hsv⟩
    · rw [hx0, hx1, hmu'] at hval
      simp only [hmu, ↓reduceIte] at hval
      convert hval using 3
      rw [hgw, GluedWeight.eval, hx2, hx3, hx4, hx5, hx6, hx7, wordSlice, slice, slice, slice, hd2,
        UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofBitVec, natCast_toUInt64_toNat (by omega),
        natCast_toUInt64_toNat (by omega),
        show off p 536 = off p 528 + 8#64 from (eight_add p 528).symm,
        show off p 2384 = off p 2376 + 8#64 from (eight_add p 2376).symm,
        NativeRustcVm.wordsOf_of_wordsAt hqs, NativeRustcVm.ewsOf_of_ewsAt hws,
        Array.toArray_toList, Array.toArray_toList]
    · rw [hx0] at hch
      exact ChangesIn.trans (fun a _ ↦ by rw [hd2]) hch (f := 0) (by rw [hsv2.2.1]; simp)
        (by omega) hS.2.1

end

end NativeRustcVmArm.Whir.GluedEval
