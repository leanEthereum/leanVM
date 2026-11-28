module

public import NativeRustcVmArm.Code.Vm.DecodedPhaseCount.Names
public import NativeRustcVmArm.Top.Verify.Exit
public import NativeRustcVmArm.Top.Verify.Init

/-!
# `verify`: the end check

After the walk succeeded, with its last state `s` in the frame's `TState`: `b3`, `b4` read the
cursor and the stream's count (`words[0]`; the decoded area is never empty), `b5` returns `0`
when they differ (`check`); `b6` reads the phase and calls `phase_count`, `b7` compares them
(`checkPhase`): X0 `1` exactly when the stream and the openings are consumed.
-/

namespace NativeRustcVmArm.Top.Verify

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Verify NativeVm.Model
open NativeRustcVm.Transcript
open NativeRustcVm (WordAt WordsAt Region wordsOf wordOf)

public section

theorem beq_toUInt64 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (a.toUInt64.toBitVec == b.toUInt64.toBitVec) = decide (a = b) :=
  ofNat_beq ha hb

/-- A block without writes keeps a body. -/
theorem body_nomem [Labels] {m0 st st' : MachineData} {R : BitVec 64 → Prop} {env : Env}
    {S₀ S₁ : SState} (hB : Body m0 832 slots R st) (hs : 832 ≤ m0.regs.SP.toBitVec.toNat)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hk : keepsRegs S₀ S₁ calleeRegs = true) (hmem : S₁.mem = []) : Body m0 832 slots R st' :=
  hB.block slotsIn hs hm₀ hm hwf hd hk fun p ⟨w, hw, _⟩ ↦ by rw [hmem] at hw; cases hw

/-- The stream's count and the phase count fit a word. -/
theorem sizes_lt {d : Mem 64} {t : BitVec 64} {a : DecArea} {s : TState} (h : TStateAt d t a s) :
    s.cursor < 2 ^ 64 ∧ s.stream.size < 2 ^ 64 ∧ s.phase < 2 ^ 64 ∧ s.openings.size < 2 ^ 64 := by
  have h1 := h.decoded.stream_le
  have h2 := h.decoded.l_lt
  have h3 := h.cursor_le
  have h4 := h.decoded.phases_le
  have h5 := h.phase_le
  simp only [NativeVm.maxStream, LeanVM.Protocol.Compile.wireMaxPhases] at h1 h4
  omega

variable [Host] {k : Nat}

/-- **The phase check**, from `b6` with the walk's last state `s` in the `TState`. -/
theorem checkPhase (hp : Placed code k)
    (hpcnt : ∀ a stream openings, Spec (Labels.label NativeRustcVmArm.Vm.DecodedPhaseCount.entryLabel)
      (PhaseCountPre a stream openings) (PhaseCountPost openings))
    {a : DecArea} {m0 : MachineData} (g : Geo a m0) {R : BitVec 64 → Prop} {s : TState}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Verify.b6Offset)) (hB : Body m0 832 slots R st.data)
    (hx19 : st.data.regs.X19 = m0.regs.X3) (hts : TStateAt st.data.dmem (tOf m0) a s)
    (hdec : DecFieldsAt st.data.dmem m0.regs.X3.toBitVec a)
    (hdecM : Mapped st.data.dmem m0.regs.X3.toBitVec 24)
    (hFm : Mapped st.data.dmem (frameOf m0) 832) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      st'.data.regs.X0 = (if s.phase == s.openings.size then 1 else 0) ∧
      SameOutside m0.dmem st'.data.dmem R ∧ Saved m0 st'.data) st := by
  have hs := g.s
  have hsl := m0.regs.SP.toBitVec.isLt
  have hs832 : 832 ≤ m0.regs.SP.toBitVec.toNat := by omega
  have hal := g.al
  have hF := g.F
  obtain ⟨hwf, hm⟩ := frame_match hB hs832 hal hFm
  refine exec_at (hb6 hp) run_b6 hwf hpc hm fun st6 hm6 hpc6 ↦ ?_
  have hk6 := b6_keeps
  rw [after_eq run_b6] at hk6
  have hB6 : Body m0 832 slots R st6.data :=
    hB.block' slotsIn hs832 hm hm6 hwf rfl hk6.1 (fun _ hr hn ↦ nonslot hr hn)
      fun p ⟨w, hw, _⟩ ↦ by rw [hk6.2] at hw; cases hw
  have hd6 : st6.data.dmem = st.data.dmem := hm6.dmem_eq hwf hk6.2
  have hX20 : st6.data.regs.X20 = s.phase.toUInt64 := by
    apply UInt64.toBitVec_inj.mp
    show (st6.data.regs.getXReg .X20).toBitVec = _
    rw [hm6.regs .X20 _ rfl]
    refine load_wordAt (r := 0) (off := 368) ?_
    have := hts.phase
    rw [off_tOf] at this
    exact this
  have hX0 : st6.data.regs.X0 = m0.regs.X3 := by
    rw [← hx19]
    exact UInt64.toBitVec_inj.mp (hm6.regs .X0 _ rfl)
  have hfp := hts.footprint
  have hpre6 : PhaseCountPre a s.stream s.openings st6.data := by
    refine ⟨⟨?_, Nat.zero_le _, fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    · show st6.data.regs.SP.toBitVec.toNat % 16 = 0
      rw [show st6.data.regs.SP.toBitVec = frameOf m0 from hB6.sp, hF]; omega
    · show DecFieldsAt st6.data.dmem st6.data.regs.X0.toBitVec a
      rw [hX0, hd6]; exact hdec
    · show Mapped st6.data.dmem st6.data.regs.X0.toBitVec 24
      rw [hX0, hd6]; exact hdecM
    · show st6.data.regs.X0.toBitVec.toNat + 24 ≤ 2 ^ 64
      rw [hX0]; exact g.decN
    · show _ ∨ _
      rw [hX0]; exact g.decArea
    · rw [hd6]; exact hfp.2.1
    · rw [hd6]; exact hts.decoded
  refine call_then hpc6 (hpcnt a s.stream s.openings) hpre6 fun st7 hpc7 hpost ↦ ?_
  obtain ⟨hx0', hsame7, hsaved7⟩ := hpost
  have hB7 : Body m0 832 slots R st7.data :=
    hB6.call slotsIn hs832 hsame7 hsaved7 fun _ h ↦ h.elim
  have hd7 : st7.data.dmem = st6.data.dmem := by
    apply Std.ExtHashMap.ext_getElem?
    intro p
    rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
    exact hsame7 p id
  have hX20' : st7.data.regs.X20 = s.phase.toUInt64 := (hsaved7.1 .X20 rfl).trans hX20
  rw [show k + NativeRustcVmArm.Vm.Verify.b6Offset + b6.length = k + NativeRustcVmArm.Vm.Verify.b7Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Verify.b6_next]] at hpc7
  refine exec_at (hb7 hp) run_b7 (Env.wf_nil _) hpc7 (match_nil _) fun st8 hm8 hpc8 ↦ ?_
  have hk8 := b7_keeps
  rw [after_eq run_b7] at hk8
  have hB8 := body_nomem hB7 hs832 (match_nil _) hm8 (Env.wf_nil _) rfl hk8.1 hk8.2
  have hd8 : st8.data.dmem = st7.data.dmem := hm8.dmem_eq (Env.wf_nil _) hk8.2
  have hsz := sizes_lt hts
  have hX0_8 : st8.data.regs.X0 = (if s.phase == s.openings.size then 1 else 0) := by
    apply UInt64.toBitVec_inj.mp
    show (st8.data.regs.getXReg .X0).toBitVec = _
    rw [hm8.regs .X0 _ rfl]
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
    rw [show (st7.data.regs.getXReg .X20) = s.phase.toUInt64 from hX20',
      show (st7.data.regs.getXReg .X0) = s.openings.size.toUInt64 from hx0',
      beq_toUInt64 hsz.2.2.1 hsz.2.2.2]
    by_cases h : s.phase = s.openings.size <;> simp [h]
  rw [show k + NativeRustcVmArm.Vm.Verify.b7Offset + b7.length = k + NativeRustcVmArm.Vm.Verify.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Verify.b7_next]] at hpc8
  refine Eventually.mono (exit8 hp hs832 hal hpc8 hB8 (by rw [hd8, hd7, hd6]; exact hFm))
    fun st' ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, h2.trans hX0_8, h3, h4⟩

/-- **The end check**, from `b3` with the walk's last state `s` in the `TState`. -/
theorem check (hp : Placed code k)
    (hpcnt : ∀ a stream openings, Spec (Labels.label NativeRustcVmArm.Vm.DecodedPhaseCount.entryLabel)
      (PhaseCountPre a stream openings) (PhaseCountPost openings))
    {a : DecArea} {m0 : MachineData} (g : Geo a m0) {R : BitVec 64 → Prop} {s : TState}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Verify.b3Offset)) (hB : Body m0 832 slots R st.data)
    (hx19 : st.data.regs.X19 = m0.regs.X3) (hts : TStateAt st.data.dmem (tOf m0) a s)
    (hdec : DecFieldsAt st.data.dmem m0.regs.X3.toBitVec a)
    (hdecM : Mapped st.data.dmem m0.regs.X3.toBitVec 24)
    (hFm : Mapped st.data.dmem (frameOf m0) 832) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      st'.data.regs.X0 = (if (s.cursor == s.stream.size && s.phase == s.openings.size) then 1
        else 0) ∧ SameOutside m0.dmem st'.data.dmem R ∧ Saved m0 st'.data) st := by
  have hs := g.s
  have hsl := m0.regs.SP.toBitVec.isLt
  have hs832 : 832 ≤ m0.regs.SP.toBitVec.toNat := by omega
  have hal := g.al
  have hF := g.F
  have gdec := g.dec
  have gdecN := g.decN
  have gda := g.decArea
  have gaN := g.areaN
  have glen := g.len
  have hsz := sizes_lt hts
  -- `b3`: the cursor and the area's length.
  have hdF : (frameOf m0).toNat + 832 ≤ m0.regs.X3.toBitVec.toNat ∨
      m0.regs.X3.toBitVec.toNat + 24 ≤ (frameOf m0).toNat := by omega
  have hwf3 : (Env.ofMachine st.data [(frameOf m0, 832), (m0.regs.X3.toBitVec, 24)]).WF :=
    Env.wf_of ⟨⟨hFm, show (frameOf m0).toNat + 832 ≤ 2 ^ 64 by omega⟩, ⟨hdecM, gdecN⟩, trivial⟩
      (List.pairwise_pair.mpr hdF)
  have hm3 : Match (Env.ofMachine st.data [(frameOf m0, 832), (m0.regs.X3.toBitVec, 24)]) initS
      st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ show (frameOf m0).toNat % 16 = 0 by omega, rfl,
      fun h ↦ absurd h (by decide), trivial⟩
      (show st.data.regs.SP.toBitVec = frameOf m0 + BitVec.ofInt 64 0 by rw [hB.sp]; simp [frameOf])
      ⟨show (st.data.regs.getXReg .X19).toBitVec = m0.regs.X3.toBitVec + BitVec.ofInt 64 0 by
        show st.data.regs.X19.toBitVec = _
        rw [hx19]; simp, trivial⟩
      trivial trivial trivial
  refine exec_at (hb3 hp) run_b3 hwf3 hpc hm3 fun st3 hm3' hpc3 ↦ ?_
  have hk3 := b3_keeps
  rw [after_eq run_b3] at hk3
  have hB3 := body_nomem hB hs832 hm3 hm3' hwf3 rfl hk3.1 hk3.2
  have hd3 : st3.data.dmem = st.data.dmem := hm3'.dmem_eq hwf3 hk3.2
  have hX8 : st3.data.regs.X8 = s.cursor.toUInt64 := by
    apply UInt64.toBitVec_inj.mp
    show (st3.data.regs.getXReg .X8).toBitVec = _
    rw [hm3'.regs .X8 _ rfl]
    refine load_wordAt (r := 0) (off := 360) ?_
    have := hts.cursor
    rw [off_tOf] at this
    exact this
  have hX19 : st3.data.regs.X19 = m0.regs.X3 := by
    apply UInt64.toBitVec_inj.mp
    show (st3.data.regs.getXReg .X19).toBitVec = _
    rw [hm3'.regs .X19 _ rfl]
    show m0.regs.X3.toBitVec + BitVec.ofInt 64 0 = _
    simp
  have hlen : (Env.ofMachine st.data [(frameOf m0, 832), (m0.regs.X3.toBitVec, 24)]).load 1 8 8 =
      a.len.toUInt64.toBitVec := load_wordAt (r := 1) hdec.2.1
  have hc3 : (SBool.cmp .eq .W64 (.load 1 8 8) (.lit 0)).eval
      (Env.ofMachine st.data [(frameOf m0, 832), (m0.regs.X3.toBitVec, 24)]) = false := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64]
    rw [hlen, show BitVec.ofNat 64 0 = (0 : Nat).toUInt64.toBitVec from rfl,
      beq_toUInt64 (by omega) (by omega)]
    simp only [decide_eq_false_iff_not]
    omega
  simp only [PcOk, hc3, Bool.false_eq_true, ite_false,
    show k + NativeRustcVmArm.Vm.Verify.b3Offset + b3.length = k + NativeRustcVmArm.Vm.Verify.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Verify.b3_next]] at hpc3
  -- `b4`: the stream's count.
  have hFp := hts.footprint
  have haM : Mapped st3.data.dmem a.words 8 := by
    rw [hd3]; exact NativeRustcVm.Mapped.mono hFp.2.1.1 (show 8 ≤ 8 * a.len by omega)
  have hda : NativeRustcVm.Apart m0.regs.X3.toBitVec 24 a.words 8 := by
    unfold NativeRustcVm.Apart; omega
  have hwf4 : (Env.ofMachine st3.data [(m0.regs.X3.toBitVec, 24), (a.words, 8)]).WF :=
    Env.wf_of ⟨⟨show Mapped st3.data.dmem m0.regs.X3.toBitVec 24 by rw [hd3]; exact hdecM, gdecN⟩,
      ⟨haM, show a.words.toNat + 8 ≤ 2 ^ 64 by omega⟩, trivial⟩
      (List.pairwise_pair.mpr hda)
  have hm4 : Match (Env.ofMachine st3.data [(m0.regs.X3.toBitVec, 24), (a.words, 8)]) wordS
      st3.data :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩
      rfl
      ⟨show (st3.data.regs.getXReg .X19).toBitVec = m0.regs.X3.toBitVec + BitVec.ofInt 64 0 by
        show st3.data.regs.X19.toBitVec = _
        rw [hX19]; simp, trivial⟩
      trivial trivial
      ⟨show (Env.ofMachine st3.data [(m0.regs.X3.toBitVec, 24), (a.words, 8)]).load 0 0 8 =
          a.words + BitVec.ofInt 64 0 by
        rw [load_wordAt (r := 0) (off := 0) (w := UInt64.ofBitVec a.words)
          (show WordAt st3.data.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 0) _ by
            rw [hd3, NativeRustcVm.addr_add_zero]; exact hdec.1)]
        simp, trivial⟩
  refine exec_at (hb4 hp) run_b4 hwf4 hpc3 hm4 fun st4 hm4' hpc4 ↦ ?_
  have hk4 := b4_keeps
  rw [after_eq run_b4] at hk4
  have hB4 := body_nomem hB3 hs832 hm4 hm4' hwf4 rfl hk4.1 hk4.2
  have hd4 : st4.data.dmem = st3.data.dmem := hm4'.dmem_eq hwf4 hk4.2
  have hX8' : st4.data.regs.X8 = s.cursor.toUInt64 :=
    (UInt64.toBitVec_inj.mp (hm4'.regs .X8 _ rfl)).trans hX8
  have hX9 : st4.data.regs.X9 = s.stream.size.toUInt64 := by
    apply UInt64.toBitVec_inj.mp
    show (st4.data.regs.getXReg .X9).toBitVec = _
    rw [hm4'.regs .X9 _ rfl]
    refine load_wordAt (r := 1) (off := 0) ?_
    show WordAt st3.data.dmem (a.words + BitVec.ofNat 64 0) _
    rw [hd3]
    exact hts.decoded.stream_count
  have hX19' : st4.data.regs.X19 = m0.regs.X3 := by
    apply UInt64.toBitVec_inj.mp
    show (st4.data.regs.getXReg .X19).toBitVec = _
    rw [hm4'.regs .X19 _ rfl]
    show m0.regs.X3.toBitVec + BitVec.ofInt 64 0 = _
    simp
  simp only [PcOk, show k + NativeRustcVmArm.Vm.Verify.b4Offset + b4.length = k + NativeRustcVmArm.Vm.Verify.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Verify.b4_next]] at hpc4
  -- `b5`: cursor against count.
  refine exec_at (hb5 hp) run_b5 (Env.wf_nil _) hpc4 (match_nil _) fun st5 hm5 hpc5 ↦ ?_
  have hk5 := b5_keeps
  rw [after_eq run_b5] at hk5
  have hB5 := body_nomem hB4 hs832 (match_nil _) hm5 (Env.wf_nil _) rfl hk5.1 hk5.2
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq (Env.wf_nil _) hk5.2
  have hc5 : ((SBool.cmp .eq .W64 (.reg .X8) (.reg .X9)).not).eval
      (Env.ofMachine st4.data []) = !decide (s.cursor = s.stream.size) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
    rw [show st4.data.regs.getXReg .X8 = s.cursor.toUInt64 from hX8',
      show st4.data.regs.getXReg .X9 = s.stream.size.toUInt64 from hX9,
      beq_toUInt64 hsz.1 hsz.2.1]
  simp only [PcOk, hc5] at hpc5
  have hdm : st5.data.dmem = st.data.dmem := by rw [hd5, hd4, hd3]
  by_cases hcs : s.cursor = s.stream.size
  · simp only [hcs, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
      show k + NativeRustcVmArm.Vm.Verify.b5Offset + b5.length = k + NativeRustcVmArm.Vm.Verify.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Verify.b5_next]] at hpc5
    have hX19'' : st5.data.regs.X19 = m0.regs.X3 :=
      (UInt64.toBitVec_inj.mp (hm5.regs .X19 _ rfl)).trans hX19'
    refine Eventually.mono (checkPhase (s := s) hp hpcnt g hpc5 hB5 hX19''
      (by rw [hdm]; exact hts) (by rw [hdm]; exact hdec) (by rw [hdm]; exact hdecM)
      (by rw [hdm]; exact hFm)) fun st' h ↦ ⟨h.1, ?_, h.2.2⟩
    rw [h.2.1]
    simp [hcs]
  · simp only [hcs, decide_false, Bool.not_false, ite_true] at hpc5
    rw [lbl_6 hp] at hpc5
    refine Eventually.mono (exit9 hp hs832 hal hpc5 hB5 (by rw [hdm]; exact hFm))
      fun st' h ↦ ⟨h.1, ?_, h.2.2⟩
    rw [h.2.1]
    simp [hcs]

end

end NativeRustcVmArm.Top.Verify
