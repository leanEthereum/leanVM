module

public import NativeRustcVmArm.Code.Vm.OpenPhase.Names
public import NativeRustcVmArm.Sumcheck.QueryOpenings.Ok
public import NativeVm.Equiv.Transcript

/-!
# `TState::query_openings` from `b4`: `open_phase`, its result tested

`b4` (`k + NativeRustcVmArm.Vm.TStateQueryOpenings.b4Offset`, the phase's address in X0) calls `open_phase` with the frame's first 32 bytes as
its output, root `i` (`t + 368 + 48 i`, its height and width), the positions and the phase
(`open_pre`: its precondition); `b5` (`k + NativeRustcVmArm.Vm.TStateQueryOpenings.b5Offset`) tests the `Option<Rows>`'s first word: `0` goes
to `b7` (`finish_fail`), the rows to `b6` (`finish_ok`). `open_spec` runs it all.
-/

namespace NativeRustcVmArm.Sumcheck.QueryOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateQueryOpenings
open NativeRustcVm.Transcript NativeVm NativeVm.Model NativeRustcArm NativeRustcVmArm.Transcript
open NativeRustcVm.Sumcheck

public section

theorem ofInt_neg368 : (BitVec.ofInt 64 (-368)).toNat = 2 ^ 64 - 368 := by
  rw [BitVec.toNat_ofInt]; rfl

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h

/-- The model at root `i` and phase `s.phase`, both there: `openPhase`'s result, the phase
advanced. -/
theorem run_some {s : TState} {i : Nat} {Q : Array UInt64} (hi : i < s.roots.size)
    (hlt : s.phase < s.openings.size) :
    (queryOpenings i Q).run s = (openPhase s.roots[i].digest s.roots[i].height s.roots[i].width Q
      s.openings[s.phase]).map fun rows ↦ (rows, { s with phase := s.phase + 1 }) := by
  rw [NativeVm.Equiv.queryOpenings_run, Array.getElem?_eq_getElem hi,
    Array.getElem?_eq_getElem hlt]

variable [Host] {k : Nat}

/-- **`open_phase`'s precondition** at `b4`'s call. -/
theorem open_pre {a : DecArea} {s : TState} {Q : Array UInt64} {m0 : MachineData}
    (hpre : QueryOpeningsPre a s Q m0) (hi : m0.regs.X2.toNat < s.roots.size)
    (hlt : s.phase < s.openings.size) {d : MachineData} (hf : Frame m0 96 slots d)
    (hs : SameOutside m0.dmem d.dmem (Stk m0))
    (hx0 : d.regs.X0.toBitVec = frameBase m0 96)
    (hx1 : d.regs.X1.toBitVec = off m0.regs.X1.toBitVec (368 + 48 * m0.regs.X2.toNat))
    (hx4 : d.regs.X4 = m0.regs.X3) (hx5 : d.regs.X5 = m0.regs.X4)
    (hx6 : d.regs.X6.toBitVec = a.word (phaseBase a.l s.phase)) :
    OpenPhasePre s.openings[s.phase] s.roots[m0.regs.X2.toNat].digest Q d := by
  have hts := tstate_stk hpre hf.kept hs
  simp only [OpenPhasePre]
  rw [hx0, hx1, hx4, hx5, hx6]
  obtain ⟨hst, hrc, -, htok, hQn, hQw, hpnw, hpS, hpA, -, -⟩ := hpre
  set t := m0.regs.X1.toBitVec
  set i := m0.regs.X2.toNat
  set fb := frameBase m0 96
  set ph := a.word (phaseBase a.l s.phase)
  set rb := off t (368 + 48 * i)
  set pos := m0.regs.X3.toBitVec
  set n := m0.regs.X4.toNat
  have hC : queryOpeningsStack = 1184 := rfl
  have hO : openPhaseStack = 1088 := rfl
  have hTB : tstateBytes = 760 := rfl
  have hPW := phaseWords_eq
  have hn : queryOpeningsStack ≤ m0.regs.SP.toNat := hst.2.1
  have hSP := m0.regs.SP.toNat_lt
  have hfb : fb.toNat = m0.regs.SP.toNat - 96 := frameBase_toNat hn (by decide)
  have hsp : d.regs.SP.toNat = m0.regs.SP.toNat - 96 := by
    rw [← UInt64.toNat_toBitVec, hf.sp, hfb]
  have hS0 : (stackBelow m0 queryOpeningsStack).toNat = m0.regs.SP.toNat - queryOpeningsStack :=
    NativeRustcVmArm.Transcript.toNat_stackBelow hn
  have hS : (stackBelow d openPhaseStack).toNat = m0.regs.SP.toNat - 1184 := by
    rw [NativeRustcVmArm.Transcript.toNat_stackBelow (by rw [hsp, hO]; omega), hsp, hO]
    omega
  obtain ⟨⟨-, hTn⟩, ⟨hAm, hAn⟩, hTA⟩ := hts.footprint
  have hTn' : t.toNat + tstateBytes ≤ 2 ^ 64 := hTn
  have hAn' : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hAn
  have hTA' : t.toNat + tstateBytes ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ t.toNat := hTA
  have htS : t.toNat + tstateBytes ≤ (stackBelow m0 queryOpeningsStack).toNat ∨
      (stackBelow m0 queryOpeningsStack).toNat + queryOpeningsStack ≤ t.toNat := htok.1
  have haS : a.words.toNat + 8 * a.len ≤ (stackBelow m0 queryOpeningsStack).toNat ∨
      (stackBelow m0 queryOpeningsStack).toNat + queryOpeningsStack ≤ a.words.toNat := htok.2.1
  have hpnw' : pos.toNat + 8 * n ≤ 2 ^ 64 := hpnw
  have hpS' : pos.toNat + 8 * n ≤ (stackBelow m0 queryOpeningsStack).toNat ∨
      (stackBelow m0 queryOpeningsStack).toNat + queryOpeningsStack ≤ pos.toNat := hpS
  have hpA' : pos.toNat + 8 * n ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ pos.toNat := hpA
  have hrcN : rcAddr.toNat + 192 ≤ 2 ^ 64 := hrc.2.1
  have hrcS : rcAddr.toNat + 192 ≤ (stackBelow m0 queryOpeningsStack).toNat ∨
      (stackBelow m0 queryOpeningsStack).toNat + queryOpeningsStack ≤ rcAddr.toNat := hrc.2.2
  have hi8 : i < 8 := Nat.lt_of_lt_of_le hi hts.roots_le
  have hrb : rb.toNat = t.toNat + (368 + 48 * i) := toNat_off (by omega)
  have hphl : phaseBase a.l s.phase + phaseWords ≤ a.len :=
    Nat.le_trans (phaseBase_add_le (Nat.lt_of_lt_of_le hlt hts.decoded.phases_le)) hts.decoded.len
  have hph : ph.toNat = a.words.toNat + 8 * phaseBase a.l s.phase := toNat_off (by omega)
  have hrcd : ∀ q, Stk m0 q → ¬ NativeRustcVm.InRange rcAddr 192 q := fun q hq ↦
    not_inRange_of_apart (Apart.symm' hrc.2.2) (stk_noWrap hst) hrc.2.1 hq
  have hroot := hts.roots i hi
  refine ⟨stackOk_callee hst hf.kept hf.sp (by decide) (by decide) (by decide),
    RcAt.callee hrc (rc_keep hs hrcd) hn (by decide) hsp (by decide),
    hts.decoded.phases s.phase hlt, hroot.2.2.1, hQn,
    wordsAt_stk (ws := Q.toList) hst hs (by rw [Array.length_toList, hQn]; exact hpnw)
      (by rw [Array.length_toList, hQn]; exact hpS) hQw,
    mapped_off hAm (by show 8 * phaseBase a.l s.phase + 8 * phaseWords ≤ 8 * a.len; omega),
    ?_, ?_, ?_, fun j hj ↦ hf.kept _ (frame_mapped (F := 96) hst (by decide) j (by omega)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (show _ ≤ _; omega)
    | (show _ ∨ _; omega)

/-- **From `b4`**: `open_phase` called, its result tested, the function finished. -/
theorem open_spec (hp : Placed code k)
    (hop : ∀ P R Q, Spec (Labels.label NativeRustcVmArm.Vm.OpenPhase.entryLabel) (OpenPhasePre P R Q) (OpenPhasePost P R Q))
    {a : DecArea} {s : TState} {Q : Array UInt64} {m0 : MachineData}
    (hpre : QueryOpeningsPre a s Q m0) (hi : m0.regs.X2.toNat < s.roots.size)
    (hlt : s.phase < s.openings.size) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateQueryOpenings.b4Offset))
    (hf : Frame m0 96 slots st.data) (hs : SameOutside m0.dmem st.data.dmem (Stk m0))
    (hx0 : st.data.regs.X0.toBitVec = a.word (phaseBase a.l s.phase))
    (hx19 : st.data.regs.X19 = m0.regs.X0) (hx20 : st.data.regs.X20 = m0.regs.X1)
    (hx21 : st.data.regs.X21 = s.phase.toUInt64) (hx22 : st.data.regs.X22 = m0.regs.X4)
    (hx23 : st.data.regs.X23 = m0.regs.X3) (hx24 : st.data.regs.X24 = m0.regs.X2) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = retOf m0 ∧ QueryOpeningsPost a s Q m0 st'.data) st := by
  have hts := tstate_stk hpre hf.kept hs
  have hst := hpre.1
  set t := m0.regs.X1.toBitVec
  set i := m0.regs.X2.toNat
  set fb := frameBase m0 96
  set rb := off t (368 + 48 * i)
  set ph := a.word (phaseBase a.l s.phase)
  set r := s.roots[i]
  set P := s.openings[s.phase]
  have hn : queryOpeningsStack ≤ m0.regs.SP.toNat := hst.2.1
  have hfnw : fb.toNat + 96 ≤ 2 ^ 64 := frame_noWrap (by rw [stack_eq] at hn; omega)
  obtain ⟨⟨hTm, hTn⟩, -, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hTF : t.toNat + 760 ≤ fb.toNat ∨ fb.toNat + 96 ≤ t.toNat :=
    apart_frame hpre.2.2.2.1.1 hn (by decide)
  have hi8 : i < 8 := Nat.lt_of_lt_of_le hi hts.roots_le
  have hrb : rb.toNat = t.toNat + (368 + 48 * i) := toNat_off (by omega)
  have hroot : RootAt st.data.dmem rb r := hts.roots i hi
  have hfr : ∀ {d : MachineData}, Frame m0 96 slots d → (frameEnv m0 d 96 []).WF := fun hf ↦
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 96) hst (by decide)) hf.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  -- `b4`: the arguments, `bl open_phase`.
  have hwf : (frameEnv m0 st.data 96 [(rb, 48)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 96) hst (by decide)) hf.kept, hfnw⟩,
      ⟨mapped_off hTm (by show 368 + 48 * i + 48 ≤ 760; omega),
        by show rb.toNat + 48 ≤ 2 ^ 64; omega⟩, trivial⟩
      (List.pairwise_pair.mpr (by
        show fb.toNat + 96 ≤ rb.toNat ∨ rb.toNat + 48 ≤ fb.toNat; omega))
  have hX24 : (st.data.regs.getXReg .X24).toBitVec.toNat = i := by
    show st.data.regs.X24.toBitVec.toNat = _
    rw [hx24]; rfl
  have hX20 : (st.data.regs.getXReg .X20).toBitVec = t := by
    show st.data.regs.X20.toBitVec = _
    rw [hx20]
  have hm : Match (frameEnv m0 st.data 96 [(rb, 48)]) openS st.data := by
    refine match_ofMachine
      ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      (by rw [hf.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial ⟨?_, trivial⟩
    show Sym.eval _ rootSym = rb + BitVec.ofInt 64 (-368)
    simp only [rootSym]
    sym_simp
    rw [Env.ofMachine_regs, Env.ofMachine_regs, hX20]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_mul, hX24, BitVec.toNat_add, hrb, ofInt_neg368,
      BitVec.toNat_ofNat]
    simp only [MemWidth.bits]
    omega
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf hpc hm fun st1 hm1 hpc1 => ?_
  obtain ⟨hmid1, hmem1, hx0₁, hx1₁, hx2₁, hx3₁, hx4₁, hx5₁, hx6₁, hcs1⟩ := after_eq run_b4 ▸ ok_b4
  have hf1 : Frame m0 96 slots st1.data := Frame.of_block hf hwf hm1 hmid1 slots_le
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem1
  have hk1 : ∀ r, calleeSaved r = true → st1.data.regs.getXReg r = st.data.regs.getXReg r :=
    fun r hr ↦ Match.reg_eq hm hm1 (by cases r <;> rfl) (hcs1 r hr)
  have hs1 : SameOutside m0.dmem st1.data.dmem (Stk m0) := by rw [hd1]; exact hs
  have hX0₁ : st1.data.regs.X0.toBitVec = fb := (hm1.regs .X0 _ hx0₁).trans (eval_ptr rfl)
  have hX1₁ : st1.data.regs.X1.toBitVec = rb := by
    refine (hm1.regs .X1 _ hx1₁).trans ?_
    simp only [rootSym]
    sym_simp
    rw [Env.ofMachine_regs, Env.ofMachine_regs, hX20]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, hX24, hrb, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    simp only [MemWidth.bits]
    omega
  have hX2₁ : st1.data.regs.X2 = r.height.toUInt64 := UInt64.toBitVec_inj.mp
    ((hm1.regs .X2 _ hx2₁).trans (load_ofMachine (o := 32) rfl hroot.2.2.2.1))
  have hX3₁ : st1.data.regs.X3 = r.width.toUInt64 := UInt64.toBitVec_inj.mp
    ((hm1.regs .X3 _ hx3₁).trans (load_ofMachine (o := 40) rfl hroot.2.2.2.2))
  have hX4₁ : st1.data.regs.X4 = m0.regs.X3 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X4 _ hx4₁).trans (by
      show st.data.regs.X23.toBitVec = _; rw [hx23]))
  have hX5₁ : st1.data.regs.X5 = m0.regs.X4 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X5 _ hx5₁).trans (by
      show st.data.regs.X22.toBitVec = _; rw [hx22]))
  have hX6₁ : st1.data.regs.X6.toBitVec = ph := (hm1.regs .X6 _ hx6₁).trans hx0
  refine call_then hpc1 (hop P r.digest Q)
    (open_pre hpre hi hlt hf1 hs1 hX0₁ hX1₁ hX4₁ hX5₁ hX6₁) fun st2 hpc2 ⟨hout2, hs2, hsv2⟩ => ?_
  rw [hX0₁, hX6₁, hX2₁, hX3₁, toNat_toUInt64 hroot.1, toNat_toUInt64 hroot.2.1] at hout2
  rw [hX0₁] at hs2
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st1.data openPhaseStack) openPhaseStack q →
      Stk m0 q ∧ ¬ NativeRustcVm.InRange fb 96 q :=
    fun q hq ↦ inRange_callee hf1.sp hn (by decide) (by decide) hq
  have hf2 : Frame m0 96 slots st2.data := by
    refine Frame.call_slots hf1 hsv2 hs2 fun p hp j hj h ↦ ?_
    rcases h with h | h
    · rw [← off_zero fb] at h
      exact not_slot_out hfnw (by decide) slots_le (by decide) p hp j hj h
    · exact (hcal _ h).2 (inRange_off_self (by have := slots_le p hp; omega) (by omega))
  have hs2' : SameOutside m0.dmem st2.data.dmem (Stk m0) := by
    intro q hq
    rw [hs2 q (by
      rintro (h | h)
      · exact hq (frame_stk hst (inRange_mono h (by omega)))
      · exact hq (hcal q h).1)]
    exact hs1 q hq
  have h19₂ : st2.data.regs.X19 = m0.regs.X0 := ((hsv2.1 .X19 rfl).trans (hk1 .X19 rfl)).trans hx19
  have h20₂ : st2.data.regs.X20 = m0.regs.X1 := ((hsv2.1 .X20 rfl).trans (hk1 .X20 rfl)).trans hx20
  have h21₂ : st2.data.regs.X21 = s.phase.toUInt64 :=
    ((hsv2.1 .X21 rfl).trans (hk1 .X21 rfl)).trans hx21
  -- `b5`: the result's first word against `0`.
  have hm2 : Match (frameEnv m0 st2.data 96 []) cmpS st2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf2.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 (hfr hf2)
    (hpc2.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateQueryOpenings.b4_next])) hm2 fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hmem3, hcs3⟩ := after_eq run_b5 ▸ ok_b5
  have hf3 : Frame m0 96 slots st3.data := Frame.of_block hf2 (hfr hf2) hm3 hmid3 slots_le
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (hfr hf2) hmem3
  have hk3 : ∀ r, calleeSaved r = true → st3.data.regs.getXReg r = st2.data.regs.getXReg r :=
    fun r hr ↦ Match.reg_eq hm2 hm3 (by cases r <;> rfl) (hcs3 r hr)
  have hs3 : SameOutside m0.dmem st3.data.dmem (Stk m0) := by rw [hd3]; exact hs2'
  have hso3 : SameOutside m0.dmem st3.data.dmem (Out m0) :=
    SameOutside.mono hs3 fun _ hq ↦ Or.inr (Or.inr hq)
  have h19₃ : st3.data.regs.X19 = m0.regs.X0 := (hk3 .X19 rfl).trans h19₂
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  cases hop3 : openPhase r.digest r.height r.width Q P with
  | none =>
    rw [hop3] at hout2
    have h0 : NativeRustcVm.WordAt st2.data.dmem (off fb 0) 0 := by rw [off_zero]; exact hout2
    rw [load_ofMachine (o := 0) rfl h0] at hpc3
    simp (config := { decide := true }) only [↓reduceIte] at hpc3
    have hnone : (queryOpenings m0.regs.X2.toNat Q).run s = none := by
      rw [run_some hi hlt, hop3]; rfl
    exact finish_fail hp hpre hnone (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.TStateQueryOpenings.b7Offset) NativeRustcVmArm.Vm.TStateQueryOpenings.label_5_at)) hf3 h19₃ hso3
  | some rows =>
    rw [hop3] at hout2
    have hcp := hout2
    obtain ⟨hp0, -, w, -, hhdr, -⟩ := hcp
    have h0 := (wordsAt_cons.mp hhdr).1
    rw [← off_zero fb] at h0
    rw [load_ofMachine (o := 0) rfl h0] at hpc3
    simp only [beq_iff_eq] at hpc3
    have hp0' : ¬ (off ph 24 = 0#64) := hp0
    simp only [hp0', ↓reduceIte] at hpc3
    have hrun : (queryOpenings m0.regs.X2.toNat Q).run s =
        some (rows, { s with phase := s.phase + 1 }) := by
      rw [run_some hi hlt, hop3]; rfl
    exact finish_ok hp hpre hrun hlt (openPhase_some hop3)
      (hpc3.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateQueryOpenings.b5_next])) hf3 h19₃ ((hk3 .X20 rfl).trans h20₂)
      ((hk3 .X21 rfl).trans h21₂) (tstate_stk hpre hf3.kept hs3) (by rw [hd3]; exact hout2) hso3

end

end NativeRustcVmArm.Sumcheck.QueryOpenings
