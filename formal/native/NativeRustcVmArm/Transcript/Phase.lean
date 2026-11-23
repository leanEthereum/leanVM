module

public import NativeRustcVmArm.Code.Vm.DecodedPhase.Names
public import NativeRustcVmArm.Code.Vm.DecodedPhaseCount.Names
public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Transcript.Phase.Exec
public import NativeRustcVmArm.Transcript.Arith

/-!
# `Decoded::phase` on AArch64

**`phase_spec`**: X0 becomes phase `k`'s address if `k` (X1) is below the phase count, else `0`,
given `phase_count`'s contract. `b0` saves X30, X20, X19 and calls `phase_count`; `b1` compares `k`
with the count and `7`: below both, `b3` compares the phase's end `phaseBase l k + phaseWords` with
the slice's length (always within, `decodedWords l ≤ len`) and `b5` returns the base's address;
otherwise `b2` returns `0`.
-/

namespace NativeRustcVmArm.Transcript.Phase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.DecodedPhase
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 32 := by decide

theorem toBitVec_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem ult_or_eq_of_le {v w : BitVec 64} (h : v.toNat ≤ w.toNat) : (v.ult w || v == w) = true := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · simp only [BitVec.ult, h, decide_true, Bool.true_or]
  · rw [BitVec.eq_of_toNat_eq h]; simp

variable [Host] {k : Nat}

/-- **`Decoded::phase` meets its contract.** -/
theorem phase_spec (hp : Placed code k)
    (hcount : ∀ a stream openings, Spec (Labels.label NativeRustcVmArm.Vm.DecodedPhaseCount.entryLabel)
      (PhaseCountPre a stream openings) (PhaseCountPost openings))
    (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW)) :
    Spec (Labels.label NativeRustcVmArm.Vm.DecodedPhase.entryLabel) (PhasePre a stream openings) (PhasePost a openings) := by
  rintro m0 ⟨hst, hdf, hmap, hnw, hap, hapS, hreg, hapA, hdec⟩
  set dp := m0.regs.X0.toBitVec with hdp
  have hn : phaseStack ≤ m0.regs.SP.toNat := hst.2.1
  have hnw' : dp.toNat + 24 ≤ 2 ^ 64 := hnw
  have hfnw := frame_noWrap (m := m0) (F := 32) hn
  have hrn : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hreg.2
  have hapF : NativeRustcVm.Apart dp 24 (frameBase m0 32) 32 := apart_frame hapS hn le_rfl
  have hapAF : NativeRustcVm.Apart a.words (8 * a.len) (frameBase m0 32) 32 :=
    apart_frame hapA hn le_rfl
  have hl64 := hdec.l_lt
  have hlen := hdec.len
  have hph := hdec.phases_le
  -- `b0`: the prologue, `bl phase_count`.
  have hwf0 : (frameEnv m0 m0 32 []).WF :=
    Env.wf_of ⟨⟨frame_mapped (F := 32) hst le_rfl, hfnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 32 []) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst le_rfl (by decide), trivial⟩
      frameBase_add.symm trivial trivial trivial trivial
  unfold NativeRustcVmArm.Vm.DecodedPhase.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.DecodedPhase.entryOffset) NativeRustcVmArm.Vm.DecodedPhase.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hws, hx0, hx19, hx20⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 32 slots st1.data := Frame.of_prologue hwf0 hm1 hpro slots_le
  have hs1 : SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange (frameBase m0 32) 32) :=
    sameOutside_region hwf0 hm1 rfl hws
  have hX0 : st1.data.regs.X0 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X0 _ hx0)
  have hX19 : st1.data.regs.X19 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ hx19)
  have hX20 : st1.data.regs.X20 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X20 _ hx20)
  -- What the frame's writes keep: the `Decoded` and the area.
  have hAd : Agree m0.dmem st1.data.dmem dp 24 (fun _ ↦ False) :=
    agree_of_sameOutside hnw (fun q hq h ↦ not_inRange_of_apart hapF hnw hfnw h hq)
      (SameOutside.mono hs1 fun _ hq ↦ Or.inr hq)
  have hAa : Agree m0.dmem st1.data.dmem a.words (8 * a.len) (fun _ ↦ False) :=
    agree_of_sameOutside hreg.2 (fun q hq h ↦ not_inRange_of_apart hapAF hreg.2 hfnw h hq)
      (SameOutside.mono hs1 fun _ hq ↦ Or.inr hq)
  have hdf1 : DecFieldsAt st1.data.dmem dp a := by
    obtain ⟨h0, h1, h2⟩ := hdf
    refine ⟨?_, wordAt_agree hAd (by omega) (fun _ _ ↦ id) h1,
      wordAt_agree hAd (by omega) (fun _ _ ↦ id) h2⟩
    rw [← off_zero dp] at h0 ⊢
    exact wordAt_agree hAd (by omega) (fun _ _ ↦ id) h0
  have hdec1 : DecodedAt st1.data.dmem a stream openings := hdec.agree hAa
  -- `phase_count`.
  have hpre1 : PhaseCountPre a stream openings st1.data := by
    unfold PhaseCountPre
    rw [hX0]
    exact ⟨stackOk_callee hst hf1.kept hf1.sp le_rfl (by decide) (by decide), hdf1,
      Mapped.keeps hmap hf1.kept, hnw, hap, Region.Ok.keeps hreg hf1.kept, hdec1⟩
  refine call_then hpc1 (hcount a stream openings) hpre1 fun st2 hpc2 ⟨hcnt, hs2, hsv2⟩ => ?_
  have hd2 : st2.data.dmem = st1.data.dmem :=
    Std.ExtHashMap.ext_getElem? fun q ↦ by
      rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
      exact hs2 q id
  have hf2 : Frame m0 32 slots st2.data :=
    Frame.call hf1 hsv2 hs2 (fun _ h ↦ h.elim) hfnw slots_le
  have h19 : st2.data.regs.X19 = m0.regs.X0 := (hsv2.1 .X19 rfl).trans hX19
  have h20 : st2.data.regs.X20 = m0.regs.X1 := (hsv2.1 .X20 rfl).trans hX20
  -- `b1`: `k` against the count and `7`.
  have hwf2 : (frameEnv m0 st2.data 32 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 32) hst le_rfl) hf2.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm2 : Match (frameEnv m0 st2.data 32 []) cmpS st2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst le_rfl (by decide), trivial⟩
      (by rw [hf2.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2
    (hpc2.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.DecodedPhase.b0Offset + NativeRustcVmArm.Vm.DecodedPhase.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.DecodedPhase.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.DecodedPhase.b0_next])) hm2 fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hmem3, hx19c, hx20c⟩ := after_eq run_b1 ▸ ok_b1
  have hf3 : Frame m0 32 slots st3.data := Frame.of_block hf2 hwf2 hm3 hmid3 slots_le
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hsz : openings.size ≤ 8 := hph
  have hr20 : (st2.data.regs.getXReg .X20).toBitVec = m0.regs.X1.toBitVec := by
    show st2.data.regs.X20.toBitVec = _; rw [h20]
  have hr0 : (st2.data.regs.getXReg .X0).toBitVec.toNat = openings.size := by
    show st2.data.regs.X0.toBitVec.toNat = _
    rw [hcnt, toBitVec_toUInt64 (by omega)]
  simp only [PcOk] at hpc3
  split at hpc3
  swap
  · -- `b2`: `k` not below the count: `None`.
    rename_i hc
    have hk : ¬ m0.regs.X1.toNat < openings.size := by
      intro hk
      sym_simp at hc
      simp only [Env.ofMachine_regs, hr20, BitVec.ult, hr0] at hc
      simp at hc
      apply hc.2 hk
      apply BitVec.eq_of_toNat_eq
      have := hc.1 hk
      rw [BitVec.toNat_ofNat]
      show m0.regs.X1.toNat = 7 % 2 ^ 64
      omega
    have hwf3 : (frameEnv m0 st3.data 32 []).WF :=
      Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 32) hst le_rfl) hf3.kept, hfnw⟩, trivial⟩
        (List.pairwise_singleton _ _)
    have hm3' : Match (frameEnv m0 st3.data 32 []) noneS st3.data :=
      match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst le_rfl (by decide), trivial⟩
        (by rw [hf3.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf3
      (hpc3.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.DecodedPhase.b1_next])) hm3' fun st4 hm4 hpc4 => ?_
    obtain ⟨hepi, hmem4, hx0'⟩ := after_eq run_b2 ▸ ok_b2
    obtain ⟨hsv4, hsl4⟩ := Frame.epilogue hf3 hwf3 hm4 hepi
    have hx30 : st4.data.regs.X30 = m0.regs.X30 := hsl4 (0, .X30) (List.mem_cons_self ..)
    have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
    refine .done _ ⟨by simp only [PcOk] at hpc4; rw [hpc4]; simp only [retOf, hx30], ?_, ?_, hsv4⟩
    · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hk)]
      exact UInt64.toBitVec_inj.mp (hm4.regs .X0 _ hx0')
    · intro q hq
      rw [hd4, hd3, hd2]
      exact hs1 q fun h ↦ hq (inRange_frame_stack hn le_rfl h)
  -- `b3`: the phase's end within the slice.
  rename_i hc
  have hk : m0.regs.X1.toNat < openings.size := by
    sym_simp at hc
    simp only [Env.ofMachine_regs, hr20, BitVec.ult, hr0] at hc
    by_contra hk
    simp at hc
    rcases hc with h | h <;> exact hk h.1
  have hk8 : m0.regs.X1.toNat < 8 := by omega
  have hlen64 : a.len < 2 ^ 64 := by
    have := NativeRustcVm.Transcript.streamEnd_lt a.l; omega
  have hwf3 : (frameEnv m0 st3.data 32 [(dp, 24)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 32) hst le_rfl) hf3.kept, hfnw⟩,
      ⟨Mapped.keeps hmap hf3.kept, hnw⟩, trivial⟩ (List.pairwise_pair.mpr (Apart.symm' hapF))
  have h19' : st3.data.regs.X19 = m0.regs.X0 := (Match.reg_eq hm2 hm3 rfl hx19c).trans h19
  have h20' : st3.data.regs.X20 = m0.regs.X1 := (Match.reg_eq hm2 hm3 rfl hx20c).trans h20
  have hm3' : Match (frameEnv m0 st3.data 32 [(dp, 24)]) baseS st3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst le_rfl (by decide), rfl, nofun, trivial⟩
      (by rw [hf3.sp]; exact (eval_ptr rfl).symm)
      ⟨known_ptr rfl (by show st3.data.regs.X19.toBitVec = _; rw [h19']), trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf3
    (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.DecodedPhase.b3Offset) NativeRustcVmArm.Vm.DecodedPhase.label_2_at)) hm3' fun st4 hm4 hpc4 => ?_
  obtain ⟨hmid4, hmem4, hx8, hx19'⟩ := after_eq run_b3 ▸ ok_b3
  have hf4 : Frame m0 32 slots st4.data := Frame.of_block hf3 hwf3 hm4 hmid4 slots_le
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
  have hdf3 : DecFieldsAt st3.data.dmem dp a := by rw [hd3, hd2]; exact hdf1
  have hL : (frameEnv m0 st3.data 32 [(dp, 24)]).load 1 16 8 = a.l.toUInt64.toBitVec :=
    load_ofMachine (o := 16) rfl hdf3.2.2
  have hN : (frameEnv m0 st3.data 32 [(dp, 24)]).load 1 8 8 = a.len.toUInt64.toBitVec :=
    load_ofMachine (o := 8) rfl hdf3.2.1
  have hr20' : (st3.data.regs.getXReg .X20).toBitVec = m0.regs.X1.toBitVec := by
    show st3.data.regs.X20.toBitVec = _; rw [h20']
  have hse : NativeVm.streamEnd a.l ≤ 2 ^ 61 + 1 := by
    simp only [NativeVm.streamEnd, NativeVm.maxStream]; omega
  have hbase : (baseSym.eval (frameEnv m0 st3.data 32 [(dp, 24)])).toNat =
      NativeVm.streamEnd a.l + m0.regs.X1.toNat * 49411 := by
    simp only [baseSym]
    sym_simp
    rw [hL, Env.ofMachine_regs, hr20', BitVec.toNat_add, BitVec.toNat_mul, streamEnd_eval,
      toBitVec_toUInt64 hl64]
    simp only [BitVec.toNat_ofNat]
    have : m0.regs.X1.toBitVec.toNat = m0.regs.X1.toNat := rfl
    omega
  have hpb := phaseBase_add_le (L := a.l) (k := m0.regs.X1.toNat) hk8
  simp only [PcOk] at hpc4
  split at hpc4
  swap
  · rename_i hc
    exfalso
    apply hc
    simp only [SBool.eval, CmpOp.apply, low_W64]
    refine ult_or_eq_of_le ?_
    show (BinOp.apply .add .W64 (baseSym.eval (frameEnv m0 st3.data 32 [(dp, 24)]))
      (BitVec.ofNat 64 49412)).toNat ≤ _
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [BitVec.toNat_add, hbase]
    simp only [Sym.eval]
    rw [hN, toBitVec_toUInt64 hlen64]
    simp only [BitVec.toNat_ofNat, NativeVm.phaseBase, phaseWords_eq] at hpb ⊢
    omega
  -- `b5`: the base's address.
  have hwf4 : (frameEnv m0 st4.data 32 [(dp, 24)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 32) hst le_rfl) hf4.kept, hfnw⟩,
      ⟨Mapped.keeps hmap hf4.kept, hnw⟩, trivial⟩ (List.pairwise_pair.mpr (Apart.symm' hapF))
  have hm4' : Match (frameEnv m0 st4.data 32 [(dp, 24)]) someS st4.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst le_rfl (by decide), rfl, nofun, trivial⟩
      (by rw [hf4.sp]; exact (eval_ptr rfl).symm)
      ⟨known_ptr rfl (by
        show (st4.data.regs.getXReg .X19).toBitVec = _
        rw [hm4.regs .X19 _ hx19']; exact eval_ptr rfl), trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf4
    (hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.DecodedPhase.b5Offset) NativeRustcVmArm.Vm.DecodedPhase.label_4_at)) hm4' fun st5 hm5 hpc5 => ?_
  obtain ⟨hepi, hmem5, hx0'⟩ := after_eq run_b5 ▸ ok_b5
  obtain ⟨hsv5, hsl5⟩ := Frame.epilogue hf4 hwf4 hm5 hepi
  have hx30 : st5.data.regs.X30 = m0.regs.X30 := hsl5 (0, .X30) (List.mem_cons_self ..)
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf4 hmem5
  have hW : (frameEnv m0 st4.data 32 [(dp, 24)]).load 1 0 8 = a.words :=
    load_ofMachine (o := 0) rfl (by rw [hd4, off_zero]; exact hdf3.1)
  have hr8 : (st4.data.regs.getXReg .X8).toBitVec.toNat =
      NativeVm.streamEnd a.l + m0.regs.X1.toNat * 49411 := by
    rw [hm4.regs .X8 _ hx8, hbase]
  refine .done _ ⟨by simp only [PcOk] at hpc5; rw [hpc5]; simp only [retOf, hx30], ?_, ?_, hsv5⟩
  · simp only [hk, ↓reduceIte]
    apply UInt64.toBitVec_inj.mp
    show (st5.data.regs.getXReg .X0).toBitVec = _
    rw [hm5.regs .X0 _ hx0', toBitVec_ofBitVec]
    sym_simp
    rw [hW, Env.ofMachine_regs]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_add, hr8, BitVec.toNat_add,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    simp only [NativeVm.phaseBase, phaseWords_eq, MemWidth.bits]
    omega
  · intro q hq
    rw [hd5, hd4, hd3, hd2]
    exact hs1 q fun h ↦ hq (inRange_frame_stack hn le_rfl h)

end

end NativeRustcVmArm.Transcript.Phase
