module

public import NativeRustcVmArm.Code.Vm.DecodedPhase.Names
public import NativeRustcVmArm.Code.Vm.OpenPhase.Names
public import NativeRustcVmArm.Code.Vm.TStateQueryOpenings.Names
public import NativeRustcVmArm.Sumcheck.QueryOpenings.Open

/-!
# `TState::query_openings` on AArch64

**`queryOpenings_spec`**: `queryOpenings i positions`'s rows at the output, the `TState` at the next
phase, given `Decoded::phase`'s and `open_phase`'s contracts. `b0` saves X30, X24 to X19 and compares
the roots' count with `8` (never above, by `TStateAt`); `b1` compares `i` with the count (not below:
`b7`, `None`); `b2` calls `Decoded::phase` with the phase index; `b3` tests its address (`0`, no
such phase: `b7`); from `b4`, `open_spec`.
-/

namespace NativeRustcVmArm.Sumcheck.QueryOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateQueryOpenings
open NativeRustcVm.Transcript NativeVm NativeVm.Model NativeRustcArm NativeRustcVmArm.Transcript

public section

/-- The model without root `i`: `None`. -/
theorem run_no_root {s : TState} {i : Nat} {Q : Array UInt64} (hi : s.roots.size ≤ i) :
    (queryOpenings i Q).run s = none := by
  rw [NativeVm.Equiv.queryOpenings_run, Array.getElem?_eq_none hi]

/-- The model without phase `s.phase`: `None`. -/
theorem run_no_phase {s : TState} {i : Nat} {Q : Array UInt64} (hp : s.openings.size ≤ s.phase) :
    (queryOpenings i Q).run s = none := by
  rw [NativeVm.Equiv.queryOpenings_run, Array.getElem?_eq_none hp]
  rcases s.roots[i]? with _ | r <;> rfl

theorem ofInt_328 : BitVec.ofInt 64 328 = BitVec.ofNat 64 328 := rfl

variable [Host] {k : Nat}

/-- **`TState::query_openings` meets its contract.** -/
theorem queryOpenings_spec (hp : Placed code k)
    (hph : ∀ a stream openings, Spec (Labels.label NativeRustcVmArm.Vm.DecodedPhase.entryLabel) (PhasePre a stream openings)
      (PhasePost a openings))
    (hop : ∀ P R Q, Spec (Labels.label NativeRustcVmArm.Vm.OpenPhase.entryLabel) (OpenPhasePre P R Q) (OpenPhasePost P R Q))
    (a : DecArea) (s : TState) (Q : Array UInt64) :
    Spec (Labels.label NativeRustcVmArm.Vm.TStateQueryOpenings.entryLabel) (QueryOpeningsPre a s Q) (QueryOpeningsPost a s Q) := by
  intro m0 hpre
  have hst := hpre.1
  have hts0 := hpre.2.2.1
  have htok := hpre.2.2.2.1
  set t := m0.regs.X1.toBitVec with htdef
  set i := m0.regs.X2.toNat with hidef
  set fb := frameBase m0 96 with hfbdef
  have hC : queryOpeningsStack = 1184 := rfl
  have hn : queryOpeningsStack ≤ m0.regs.SP.toNat := hst.2.1
  have hSP := m0.regs.SP.toNat_lt
  have hfnw : fb.toNat + 96 ≤ 2 ^ 64 := frame_noWrap (by omega)
  have hfb : fb.toNat = m0.regs.SP.toNat - 96 := frameBase_toNat hn (by decide)
  have hS0 : (stackBelow m0 queryOpeningsStack).toNat = m0.regs.SP.toNat - queryOpeningsStack :=
    NativeRustcVmArm.Transcript.toNat_stackBelow hn
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, hTA⟩ := hts0.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hAn' : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hAn
  have hTA' : t.toNat + 760 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ t.toNat := hTA
  have htS : t.toNat + 760 ≤ (stackBelow m0 queryOpeningsStack).toNat ∨
      (stackBelow m0 queryOpeningsStack).toNat + queryOpeningsStack ≤ t.toNat := htok.1
  have haS : a.words.toNat + 8 * a.len ≤ (stackBelow m0 queryOpeningsStack).toNat ∨
      (stackBelow m0 queryOpeningsStack).toNat + queryOpeningsStack ≤ a.words.toNat := htok.2.1
  have hTF : t.toNat + 760 ≤ fb.toNat ∨ fb.toNat + 96 ≤ t.toNat := by omega
  have hfr : ∀ {d : MachineData}, Frame m0 96 slots d → (frameEnv m0 d 96 []).WF := fun hf ↦
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 96) hst (by decide)) hf.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hfrT : ∀ {d : MachineData}, Frame m0 96 slots d → (frameEnv m0 d 96 [(t, 760)]).WF :=
    fun hf ↦ Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 96) hst (by decide)) hf.kept, hfnw⟩,
      ⟨Mapped.keeps hTm hf.kept, hTn⟩, trivial⟩
      (List.pairwise_pair.mpr (by show fb.toNat + 96 ≤ t.toNat ∨ t.toNat + 760 ≤ fb.toNat; omega))
  set nr := s.roots.size with hnrdef
  have hnr8 : nr ≤ 8 := hts0.roots_le
  have hnr64 : nr.toUInt64.toBitVec.toNat = nr := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  -- `b0`: the prologue, the roots' count against `8`.
  have hwf0 : (frameEnv m0 m0 96 [(t, 760)]).WF :=
    Env.wf_of ⟨⟨frame_mapped (F := 96) hst (by decide), hfnw⟩, ⟨hTm, hTn⟩, trivial⟩
      (List.pairwise_pair.mpr (by show fb.toNat + 96 ≤ t.toNat ∨ t.toNat + 760 ≤ fb.toNat; omega))
  have hm0 : Match (frameEnv m0 m0 96 [(t, 760)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      frameBase_add.symm ⟨known_ptr rfl rfl, trivial⟩ trivial trivial trivial
  unfold NativeRustcVmArm.Vm.TStateQueryOpenings.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.TStateQueryOpenings.entryOffset) NativeRustcVmArm.Vm.TStateQueryOpenings.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hws1, hx8₁, hx19₁, hx1₁, hx2₁, hx3₁, hx4₁⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 96 slots st1.data := Frame.of_prologue hwf0 hm1 hpro slots_le
  have hs1 : SameOutside m0.dmem st1.data.dmem (Stk m0) := by
    intro q hq
    exact sameOutside_region hwf0 hm1 rfl hws1 q fun h ↦ hq (frame_stk hst h)
  have hcnt : (frameEnv m0 m0 96 [(t, 760)]).load 1 752 8 = nr.toUInt64.toBitVec :=
    load_ofMachine (o := 752) rfl hts0.n_roots
  have hX19₁ : st1.data.regs.X19 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ hx19₁)
  have hX8₁ : st1.data.regs.X8.toBitVec = nr.toUInt64.toBitVec := (hm1.regs .X8 _ hx8₁).trans hcnt
  have hX1₁ : st1.data.regs.X1.toBitVec = t := (hm1.regs .X1 _ hx1₁).trans (eval_ptr rfl)
  have hX2₁ : st1.data.regs.X2 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X2 _ hx2₁)
  have hX3₁ : st1.data.regs.X3 = m0.regs.X3 := UInt64.toBitVec_inj.mp (hm1.regs .X3 _ hx3₁)
  have hX4₁ : st1.data.regs.X4 = m0.regs.X4 := UInt64.toBitVec_inj.mp (hm1.regs .X4 _ hx4₁)
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [hcnt] at hpc1
  have hc1 : ((!nr.toUInt64.toBitVec.ult (BitVec.ofNat 64 8)) &&
      !(nr.toUInt64.toBitVec == BitVec.ofNat 64 8)) = false := by
    by_cases h8 : nr = 8
    · have : (nr.toUInt64.toBitVec == BitVec.ofNat 64 8) = true := by
        rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [hnr64, h8]; rfl
      rw [this]; simp
    · have : nr.toUInt64.toBitVec.ult (BitVec.ofNat 64 8) = true := by
        simp only [BitVec.ult, hnr64, BitVec.toNat_ofNat]; simp; omega
      rw [this]; simp
  rw [hc1] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b1`: `i` against the count.
  have hm1' : Match (frameEnv m0 st1.data 96 []) cmpS st1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf1.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 (hfr hf1)
    (hpc1.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.TStateQueryOpenings.b0Offset + NativeRustcVmArm.Vm.TStateQueryOpenings.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.TStateQueryOpenings.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateQueryOpenings.b0_next])) hm1' fun st2 hm2 hpc2 => ?_
  obtain ⟨hmid2, hmem2, hx24₂, hx1₂, hx3₂, hx4₂, hcs2⟩ := after_eq run_b1 ▸ ok_b1
  have hf2 : Frame m0 96 slots st2.data := Frame.of_block hf1 (hfr hf1) hm2 hmid2 slots_le
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq (hfr hf1) hmem2
  have hs2 : SameOutside m0.dmem st2.data.dmem (Stk m0) := by rw [hd2]; exact hs1
  have hX19₂ : st2.data.regs.X19 = m0.regs.X0 :=
    (Match.reg_eq hm1' hm2 rfl (hcs2 .X19 rfl (by decide))).trans hX19₁
  have hX24₂ : st2.data.regs.X24 = m0.regs.X2 :=
    (UInt64.toBitVec_inj.mp (hm2.regs .X24 _ hx24₂)).trans hX2₁
  have hX1₂ : st2.data.regs.X1.toBitVec = t := (hm2.regs .X1 _ hx1₂).trans hX1₁
  have hX3₂ : st2.data.regs.X3 = m0.regs.X3 :=
    (UInt64.toBitVec_inj.mp (hm2.regs .X3 _ hx3₂)).trans hX3₁
  have hX4₂ : st2.data.regs.X4 = m0.regs.X4 :=
    (UInt64.toBitVec_inj.mp (hm2.regs .X4 _ hx4₂)).trans hX4₁
  simp only [PcOk] at hpc2
  sym_simp at hpc2
  rw [Env.ofMachine_regs, Env.ofMachine_regs] at hpc2
  rw [show (st1.data.regs.getXReg .X2).toBitVec = m0.regs.X2.toBitVec from by
      show st1.data.regs.X2.toBitVec = _; rw [hX2₁],
    show (st1.data.regs.getXReg .X8).toBitVec = nr.toUInt64.toBitVec from hX8₁] at hpc2
  by_cases hi : i < nr
  swap
  · have hc : (!m0.regs.X2.toBitVec.ult nr.toUInt64.toBitVec) = true := by
      simp only [BitVec.ult, hnr64]
      simp
      show nr ≤ i
      omega
    rw [hc] at hpc2
    simp only [↓reduceIte] at hpc2
    exact finish_fail hp hpre (run_no_root (by omega)) (hpc2.trans (hp.label (j := NativeRustcVmArm.Vm.TStateQueryOpenings.b7Offset) NativeRustcVmArm.Vm.TStateQueryOpenings.label_5_at)) hf2
      hX19₂ (SameOutside.mono hs2 fun _ hq ↦ Or.inr (Or.inr hq))
  have hc : (!m0.regs.X2.toBitVec.ult nr.toUInt64.toBitVec) = false := by
    simp only [BitVec.ult, hnr64]
    simp
    exact hi
  rw [hc] at hpc2
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc2
  -- `b2`: the phase index, `bl phase`.
  have hts2 : TStateAt st2.data.dmem t a s := tstate_stk hpre hf2.kept hs2
  have hm2' : Match (frameEnv m0 st2.data 96 [(t, 760)]) phaseS st2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      (by rw [hf2.sp]; exact (eval_ptr rfl).symm) ⟨known_ptr rfl hX1₂, trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 (hfrT hf2)
    (hpc2.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateQueryOpenings.b1_next])) hm2' fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hmem3, hx0₃, hx1₃, hx20₃, hx21₃, hx22₃, hx23₃, hx19₃, hx24₃⟩ :=
    after_eq run_b2 ▸ ok_b2
  have hf3 : Frame m0 96 slots st3.data := Frame.of_block hf2 (hfrT hf2) hm3 hmid3 slots_le
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (hfrT hf2) hmem3
  have hs3 : SameOutside m0.dmem st3.data.dmem (Stk m0) := by rw [hd3]; exact hs2
  have hts3 : TStateAt st3.data.dmem t a s := by rw [hd3]; exact hts2
  have hphl : s.phase ≤ 8 := Nat.le_trans hts2.phase_le
    (by have := hts2.decoded.phases_le; simpa [LeanVM.Protocol.Compile.wireMaxPhases] using this)
  have hph64 : s.phase.toUInt64.toBitVec.toNat = s.phase := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hphase : (frameEnv m0 st2.data 96 [(t, 760)]).load 1 360 8 = s.phase.toUInt64.toBitVec :=
    load_ofMachine (o := 360) rfl hts2.phase
  have hX0₃ : st3.data.regs.X0.toBitVec = off t 328 := by
    refine (hm3.regs .X0 _ hx0₃).trans ?_
    show _ + BitVec.ofInt 64 328 = _
    rw [Env.base_ofMachine _ _ _ rfl, ofInt_328]
  have hX1₃ : st3.data.regs.X1.toNat = s.phase := by
    show (st3.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm3.regs .X1 _ hx1₃, Sym.eval, hphase, hph64]
  have hX20₃ : st3.data.regs.X20 = m0.regs.X1 :=
    UInt64.toBitVec_inj.mp ((hm3.regs .X20 _ hx20₃).trans (eval_ptr rfl))
  have hX21₃ : st3.data.regs.X21 = s.phase.toUInt64 :=
    UInt64.toBitVec_inj.mp ((hm3.regs .X21 _ hx21₃).trans hphase)
  have hX22₃ : st3.data.regs.X22 = m0.regs.X4 :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X22 _ hx22₃)).trans hX4₂
  have hX23₃ : st3.data.regs.X23 = m0.regs.X3 :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X23 _ hx23₃)).trans hX3₂
  have hX19₃ : st3.data.regs.X19 = m0.regs.X0 :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X19 _ hx19₃)).trans hX19₂
  have hX24₃ : st3.data.regs.X24 = m0.regs.X2 :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X24 _ hx24₃)).trans hX24₂
  have hsp3 : st3.data.regs.SP.toNat = m0.regs.SP.toNat - 96 := by
    rw [← UInt64.toNat_toBitVec, hf3.sp, hfb]
  have hS3 : (stackBelow st3.data phaseStack).toNat = m0.regs.SP.toNat - 128 := by
    rw [NativeRustcVmArm.Transcript.toNat_stackBelow (by rw [hsp3]; show 32 ≤ _; omega), hsp3]
    show _ - 32 = _
    omega
  have hdp : (off t 328).toNat = t.toNat + 328 := toNat_off (by omega)
  have hpre3 : PhasePre a s.stream s.openings st3.data := by
    simp only [PhasePre]
    rw [hX0₃]
    refine ⟨stackOk_callee hst hf3.kept hf3.sp (by decide) (by decide) (by decide), hts3.dec,
      mapped_off hts3.footprint.1.1 (by show 328 + 24 ≤ 760; omega), ?_, ?_, ?_,
      hts3.footprint.2.1, ?_, hts3.decoded⟩
    · show (off t 328).toNat + 24 ≤ 2 ^ 64; omega
    · show (off t 328).toNat + 24 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (off t 328).toNat
      omega
    · show (off t 328).toNat + 24 ≤ (stackBelow st3.data phaseStack).toNat ∨
        (stackBelow st3.data phaseStack).toNat + phaseStack ≤ (off t 328).toNat
      rw [hS3]; show _ ∨ _ + 32 ≤ _; omega
    · show a.words.toNat + 8 * a.len ≤ (stackBelow st3.data phaseStack).toNat ∨
        (stackBelow st3.data phaseStack).toNat + phaseStack ≤ a.words.toNat
      rw [hS3]; show _ ∨ _ + 32 ≤ _; omega
  refine call_then hpc3 (hph a s.stream s.openings) hpre3 fun st4 hpc4 ⟨hx0₄, hs4, hsv4⟩ => ?_
  rw [hX1₃] at hx0₄
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st3.data phaseStack) phaseStack q →
      Stk m0 q ∧ ¬ NativeRustcVm.InRange fb 96 q :=
    fun q hq ↦ inRange_callee hf3.sp hn (by decide) (by decide) hq
  have hf4 : Frame m0 96 slots st4.data :=
    Frame.call hf3 hsv4 hs4 (fun q hq ↦ (hcal q hq).2) hfnw slots_le
  have hs4' : SameOutside m0.dmem st4.data.dmem (Stk m0) := by
    intro q hq
    rw [hs4 q fun h ↦ hq (hcal q h).1]
    exact hs3 q hq
  -- `b3`: the phase's address against `0`.
  have hm4 : Match (frameEnv m0 st4.data 96 []) cmpS st4.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf4.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 (hfr hf4)
    (hpc4.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateQueryOpenings.b2_next])) hm4 fun st5 hm5 hpc5 => ?_
  obtain ⟨hmid5, hmem5, hx0₅, hcs5⟩ := after_eq run_b3 ▸ ok_b3
  have hf5 : Frame m0 96 slots st5.data := Frame.of_block hf4 (hfr hf4) hm5 hmid5 slots_le
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq (hfr hf4) hmem5
  have hs5 : SameOutside m0.dmem st5.data.dmem (Stk m0) := by rw [hd5]; exact hs4'
  have hk5 : ∀ r, calleeSaved r = true → st5.data.regs.getXReg r = st3.data.regs.getXReg r :=
    fun r hr ↦ (Match.reg_eq hm4 hm5 (by cases r <;> rfl) (hcs5 r hr)).trans (hsv4.1 r hr)
  have hX0₅ : st5.data.regs.X0 = st4.data.regs.X0 := Match.reg_eq hm4 hm5 rfl hx0₅
  simp only [PcOk] at hpc5
  sym_simp at hpc5
  rw [Env.ofMachine_regs] at hpc5
  by_cases hlt : s.phase < s.openings.size
  swap
  · simp only [hlt, ↓reduceIte] at hx0₄
    rw [show (st4.data.regs.getXReg .X0).toBitVec = 0#64 from by
      show st4.data.regs.X0.toBitVec = _; rw [hx0₄]; rfl] at hpc5
    simp only [beq_self_eq_true, ↓reduceIte] at hpc5
    exact finish_fail hp hpre (run_no_phase (by omega)) (hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.TStateQueryOpenings.b7Offset) NativeRustcVmArm.Vm.TStateQueryOpenings.label_5_at)) hf5
      ((hk5 .X19 rfl).trans hX19₃) (SameOutside.mono hs5 fun _ hq ↦ Or.inr (Or.inr hq))
  simp only [hlt, ↓reduceIte] at hx0₄
  have hbase : 0 < phaseBase a.l s.phase := by unfold phaseBase; omega
  have hphl' : phaseBase a.l s.phase + phaseWords ≤ a.len :=
    Nat.le_trans (phaseBase_add_le (Nat.lt_of_lt_of_le hlt hts3.decoded.phases_le))
      hts3.decoded.len
  have hw : (a.word (phaseBase a.l s.phase)).toNat = a.words.toNat + 8 * phaseBase a.l s.phase :=
    toNat_off (by have := phaseWords_eq; omega)
  have hne : (a.word (phaseBase a.l s.phase) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have := congrArg BitVec.toNat h
    rw [hw] at this
    simp at this
    omega
  rw [show (st4.data.regs.getXReg .X0).toBitVec = a.word (phaseBase a.l s.phase) from by
    show st4.data.regs.X0.toBitVec = _; rw [hx0₄], hne] at hpc5
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc5
  exact open_spec hp hop hpre hi hlt (hpc5.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateQueryOpenings.b3_next])) hf5 hs5
    (by rw [hX0₅, hx0₄]) ((hk5 .X19 rfl).trans hX19₃) ((hk5 .X20 rfl).trans hX20₃)
    ((hk5 .X21 rfl).trans hX21₃) ((hk5 .X22 rfl).trans hX22₃) ((hk5 .X23 rfl).trans hX23₃)
    ((hk5 .X24 rfl).trans hX24₃)

end

end NativeRustcVmArm.Sumcheck.QueryOpenings
