module

public import NativeRustcVmX64.Transcript.Phase.Exec
public import NativeRustcVmX64.Transcript.Arith
public import NativeRustcVmX64.Code.Vm.DecodedPhase.Names
public import NativeRustcVmX64.Code.Vm.DecodedPhaseCount.Names

/-!
# `Decoded::phase` on x86-64

**`phase_spec`**: RAX becomes phase `k`'s address if `k` (RSI) is below the phase count, else `0`,
given `phase_count`'s contract. `b0` pushes R14, RBX and calls `phase_count`; `b1`, `b2` compare
`k` with `7` and the count: below both, `b3` compares the phase's end `phaseBase l k + phaseWords`
with the slice's length (always within, `decodedWords l ≤ len`) and `b6` returns the base's
address; otherwise `b5` returns `0`.
-/

namespace NativeRustcVmX64.Transcript.Phase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.DecodedPhase
open NativeRustcVm.Transcript NativeVm.Model

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 32 := by decide

theorem toBitVec_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

variable [Host] {k : Nat}

/-- **`Decoded::phase` meets its contract.** -/
theorem phase_spec (hp : Placed code k)
    (hcount : ∀ a stream openings, Spec (Labels.label NativeRustcVmX64.Vm.DecodedPhaseCount.entryLabel)
      (PhaseCountPre a stream openings) (PhaseCountPost openings))
    (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW)) :
    Spec (Labels.label NativeRustcVmX64.Vm.DecodedPhase.entryLabel) (PhasePre a stream openings) (PhasePost a openings) := by
  rintro m0 ⟨hst, hdf, hmap, hnw, hap, hapS, hreg, hapA, hdec⟩
  set dp := reg m0 .rdi with hdp
  have hn : phaseStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hnw' : dp.toNat + 24 ≤ 2 ^ 64 := hnw
  have hfnw := frame_noWrap (F := 32) hst le_rfl
  have hrn : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hreg.2
  have hapF : NativeRustcVm.Apart dp 24 (stackBelow m0 32) (32 + 8) := hapS
  have hapAF : NativeRustcVm.Apart a.words (8 * a.len) (stackBelow m0 32) (32 + 8) := hapA
  have hl64 := hdec.l_lt
  have hlen := hdec.len
  have hph := hdec.phases_le
  -- `b0`: the prologue, `call phase_count`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 32) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.DecodedPhase.b0Offset + b0.length)).toBitVec) ⟨frame_mapped hst le_rfl, hfnw⟩
    (by simp) (List.pairwise_singleton _ _)
  unfold NativeRustcVmX64.Vm.DecodedPhase.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.DecodedPhase.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hws, hx7, hx3, hx14⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 32 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 32) 32) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws
  have hX7 : reg st1.data .rdi = dp := hm1.regs .rdi _ hx7
  have hX3 : reg st1.data .rbx = dp := hm1.regs .rbx _ hx3
  have hX14 : reg st1.data .r14 = reg m0 .rsi := hm1.regs .r14 _ hx14
  have hsp1 : rspOf st1.data = stackBelow m0 32 := by rw [hf1.sp, off_zero]
  -- What the frame's writes keep: the `Decoded` and the area.
  have hAd : Agree m0.dmem st1.data.dmem dp 24 (fun _ ↦ False) :=
    agree_of_sameOutside hnw (fun q hq h ↦ not_inRange_of_apart hapF hnw hfnw h
      (inRange_mono hq (by decide))) (SameOutside.mono hs1 fun _ hq ↦ Or.inr hq)
  have hAa : Agree m0.dmem st1.data.dmem a.words (8 * a.len) (fun _ ↦ False) :=
    agree_of_sameOutside hreg.2 (fun q hq h ↦ not_inRange_of_apart hapAF hreg.2 hfnw h
      (inRange_mono hq (by decide))) (SameOutside.mono hs1 fun _ hq ↦ Or.inr hq)
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
    rw [hX7]
    exact ⟨stackOk_callee hst hf1.kept hsp1 (by decide), hdf1,
      Mapped.keeps hmap hf1.kept, hnw, hap, Region.Ok.keeps hreg hf1.kept, hdec1⟩
  refine call_then hpc1 (hcount a stream openings) hpre1
    fun st2 hpc2 hrsp2 ⟨hcnt, hs2, hsv2⟩ => ?_
  have hd2 : st2.data.dmem = st1.data.dmem :=
    Std.ExtHashMap.ext_getElem? fun q ↦ by
      rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
      exact hs2 q id
  have hf2 : Frame m0 32 slots 8 st2.data :=
    Frame.call hf1 hsv2 hrsp2 hs2 (fun _ h ↦ h.elim) hfnw slots_le
  have h3 : reg st2.data .rbx = dp := (hsv2.1 .rbx rfl).trans hX3
  have h14 : reg st2.data .r14 = reg m0 .rsi := (hsv2.1 .r14 rfl).trans hX14
  have hsz : openings.size ≤ 8 := hph
  have hr0 : (reg st2.data .rax).toNat = openings.size := by
    rw [hcnt, toBitVec_toUInt64 (by omega)]
  have hr14 : (st2.data.regs.get64 .r14).toNat = (reg m0 .rsi).toNat := by
    show (reg st2.data .r14).toNat = _; rw [h14]
  have hr0' : (st2.data.regs.get64 .rax).toNat = openings.size := hr0
  -- `b1` to `b6`, from one environment.
  have hwf2 := frame_wf (m0 := m0) (d := st2.data) (F := 32) (rest := [(dp, 24)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst le_rfl) hf2.kept, hfnw⟩
    (by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨Mapped.keeps hmap hf2.kept, hnw⟩)
    (List.pairwise_pair.mpr (Apart.symm' hapF))
  have hm2 : Match (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0) cmpS st2.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf2.rsp_eval, known_ptr rfl h3, trivial⟩ trivial trivial
      trivial
  obtain ⟨hm1e, hm2e, hm3e, hx3'⟩ := ok_b1
  have hd : ∀ {S : SState} {st : MachineState}, S.mem = [] →
      Match (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0) S st.data →
      st.data.dmem = st2.data.dmem := fun h hm ↦ hm.dmem_eq hwf2 h
  -- The end of a path: the frame restored, `ret`.
  have hfin : ∀ {S : SState} {v : Sym} {st : MachineState} {x : Int64},
      EndOk S v → Match (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0) S st.data →
      PcOk (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0) (.ret (.load 0 32 8)) x st →
      v.eval (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0) =
        (if (reg m0 .rsi).toNat < openings.size then
          a.word (NativeVm.phaseBase a.l (reg m0 .rsi).toNat) else 0) →
      Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
        rspOf st'.data = rspOf m0 + 8#64 ∧ PhasePost a openings m0 st'.data) st := by
    intro S v st x hE hm hpc hv
    obtain ⟨hepi, hmem, hrax⟩ := hE
    obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf2 hwf2 hm hepi
    simp only [PcOk] at hpc
    refine .done _ ⟨by rw [hpc]; exact hf2.load_ret hst le_rfl, hrsp,
      (hm.regs .rax _ hrax).trans hv, fun q hq ↦ ?_, hsv⟩
    rw [hd hmem hm, hd2]
    exact hs1 q hq
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf2 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.DecodedPhase.b0_next)) hm2 fun st3 hm3 hpc3 => ?_
  simp only [PcOk] at hpc3
  split at hpc3
  · -- `k > 7`: `None`.
    rename_i hc
    have hk : ¬ (reg m0 .rsi).toNat < openings.size := by
      intro hk
      sym_simp_at hc
      simp only [Env.ofMachine_regs, BitVec.ult, hr14] at hc
      simp at hc
      apply hc.2
      apply BitVec.eq_of_toNat_eq
      show (st2.data.regs.get64 .r14).toNat = 7
      have := hc.1
      omega
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after exit_b1 run_b5_1) hwf2
      nofun (hpc3.trans (hp.label NativeRustcVmX64.Vm.DecodedPhase.label_5_at)) hm3 fun st4 hm4 hpc4 => ?_
    exact hfin (after_eq run_b5_1 ▸ end_b5_1) hm4 hpc4 (by simp only [hk, ↓reduceIte]; rfl)
  rename_i hc1
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf2 nofun
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.DecodedPhase.b1_next)) hm3 fun st4 hm4 hpc4 => ?_
  simp only [PcOk] at hpc4
  split at hpc4
  · -- `k` not below the count: `None`.
    rename_i hc
    have hk : ¬ (reg m0 .rsi).toNat < openings.size := by
      sym_simp_at hc
      simp only [Env.ofMachine_regs, BitVec.ult, hr14, hr0'] at hc
      simpa using hc
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after exit_b2 run_b5_2) hwf2
      nofun (hpc4.trans (hp.label NativeRustcVmX64.Vm.DecodedPhase.label_5_at)) hm4 fun st5 hm5 hpc5 => ?_
    exact hfin (after_eq run_b5_2 ▸ end_b5_2) hm5 hpc5 (by simp only [hk, ↓reduceIte]; rfl)
  -- `b3`: the phase's end within the slice.
  rename_i hc
  have hk : (reg m0 .rsi).toNat < openings.size := by
    sym_simp_at hc
    simp only [Env.ofMachine_regs, BitVec.ult, hr14, hr0'] at hc
    simpa using hc
  have hk8 : (reg m0 .rsi).toNat < 8 := by omega
  have hlen64 : a.len < 2 ^ 64 := by
    have := NativeRustcVm.Transcript.streamEnd_lt a.l; omega
  have hdf2 : DecFieldsAt st2.data.dmem dp a := by rw [hd2]; exact hdf1
  have hL : (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0).load 1 16 8 =
      a.l.toUInt64.toBitVec := load_ofMachine (o := 16) rfl hdf2.2.2
  have hN : (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0).load 1 8 8 =
      a.len.toUInt64.toBitVec := load_ofMachine (o := 8) rfl hdf2.2.1
  have hW : (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0).load 1 0 8 = a.words :=
    load_ofMachine (o := 0) rfl (by rw [off_zero]; exact hdf2.1)
  have hse : NativeVm.streamEnd a.l ≤ 2 ^ 61 + 1 := by
    simp only [NativeVm.streamEnd, NativeVm.maxStream]; omega
  have hbase : (baseSym.eval (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0)).toNat =
      (reg m0 .rsi).toNat * 49411 + NativeVm.streamEnd a.l := by
    simp only [baseSym]
    sym_simp
    rw [hL, Env.ofMachine_regs, BitVec.toNat_add, BitVec.toNat_mul, hr14, streamEnd_eval,
      toBitVec_toUInt64 hl64]
    simp only [BitVec.toNat_ofNat]
    omega
  have hpb := phaseBase_add_le (L := a.l) (k := (reg m0 .rsi).toNat) hk8
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf2 nofun
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.DecodedPhase.b2_next)) hm4 fun st5 hm5 hpc5 => ?_
  simp only [PcOk] at hpc5
  split at hpc5
  swap
  · rename_i hc
    exfalso
    apply hc
    have hend : (endSym.eval (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0)).toNat ≤
        a.len := by
      simp only [endSym, Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [BitVec.toNat_add, hbase]
      simp only [BitVec.toNat_ofNat, NativeVm.phaseBase, phaseWords_eq] at hpb ⊢
      omega
    simp only [SBool.eval, CmpOp.apply, low_W64, Bool.or_eq_true, beq_iff_eq]
    rcases Nat.lt_or_eq_of_le hend with h | h
    · have : (endSym.eval (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0)).ult
          ((Sym.load 1 8 8).eval (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0)) = true := by
        simp only [BitVec.ult, Sym.eval, hN, toBitVec_toUInt64 hlen64, decide_eq_true_eq]
        exact h
      exact Or.inl this
    · have : endSym.eval (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0) =
          (Sym.load 1 8 8).eval (frameEnv m0 st2.data 32 [(dp, 24)] (fun _ ↦ 0) 0) :=
        BitVec.eq_of_toNat_eq (by rw [h]; simp only [Sym.eval, hN, toBitVec_toUInt64 hlen64])
      exact Or.inr this
  -- `b6`: the base's address.
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) (exec_after exit_b3 run_b6) hwf2 nofun
    (hpc5.trans (hp.label NativeRustcVmX64.Vm.DecodedPhase.label_4_at)) hm5 fun st6 hm6 hpc6 => ?_
  refine hfin (after_eq run_b6 ▸ end_b6) hm6 hpc6 ?_
  simp only [hk, ↓reduceIte]
  sym_simp
  rw [hW]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_add, hbase, toNat_off (by
    simp only [NativeVm.phaseBase, phaseWords_eq] at hpb ⊢; omega)]
  simp only [BitVec.toNat_ofNat, NativeVm.phaseBase, phaseWords_eq, shiftCount, low, Nat.shiftLeft_eq]
  rw [show ((BitVec.setWidth Width.W8.bits (3#64 : BitVec 64)).toNat &&& shiftMask Width.W64) = 3
    from rfl, show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
  simp only [NativeVm.phaseBase, phaseWords_eq] at hpb
  omega

end

end NativeRustcVmX64.Transcript.Phase
