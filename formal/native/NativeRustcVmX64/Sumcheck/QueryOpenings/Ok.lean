module

public import NativeRustcVmX64.Sumcheck.QueryOpenings.Fail
public import NativeRustcVm.Sumcheck.PhaseUpdate

/-!
# `TState::query_openings`'s `Some` exit (x86-64)

`b5` (`k + NativeRustcVmX64.Vm.TStateQueryOpenings.b5Offset`) copies `open_phase`'s `Rows` (the frame's 32 bytes at `16`) to the output (R14),
stores the phase index plus one at `t + 360` (RBX, R15) and `b7` runs the epilogue: the rows,
read in the phase's openings, at the output and the `TState` at its next phase (`finish_ok`).
-/

namespace NativeRustcVmX64.Sumcheck.QueryOpenings

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateQueryOpenings
open NativeRustcVm.Transcript NativeVm NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck NativeRustcVm.Sumcheck

public section

theorem toUInt64_add_one {n : Nat} (h : n + 1 < 2 ^ 64) :
    UInt64.ofBitVec (n.toUInt64.toBitVec + BitVec.ofNat 64 1) = (n + 1).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have e : ∀ m, m < 2 ^ 64 → m.toUInt64.toNat = m := fun m hm ↦ by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hm
  rw [e _ h]
  show (n.toUInt64.toBitVec + BitVec.ofNat 64 1).toNat = _
  rw [BitVec.toNat_add, UInt64.toNat_toBitVec, e _ (by omega), BitVec.toNat_ofNat]
  omega

/-- `openPhase`'s rows are the phase's leaves. -/
theorem openPhase_some {R : LeanVM.Protocol.Digest} {h w : Nat} {Q : Array UInt64}
    {P : Array OpeningW} {rows : Array (Array UInt64)} (hr : openPhase R h w Q P = some rows) :
    rows = P.map (·.leaf) := by
  unfold openPhase at hr
  split at hr
  · split at hr
    · exact (Option.some.inj hr).symm
    · cases hr
  · cases hr

variable [Host] {k : Nat}

/-- **`b5`, `b7`**: the rows copied to the output, the phase advanced, the epilogue. -/
theorem finish_ok (hp : Placed code k) {a : DecArea} {s : TState} {Q : Array UInt64}
    {m0 : MachineData} (hpre : QueryOpeningsPre a s Q m0) {rows : Array (Array UInt64)}
    (hrun : (queryOpenings (reg m0 .rdx).toNat Q).run s =
      some (rows, { s with phase := s.phase + 1 }))
    (hlt : s.phase < s.openings.size) (hrowsP : rows = s.openings[s.phase].map (·.leaf))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b5Offset)) (hf : Frame m0 96 slots 8 st.data)
    (h14 : reg st.data .r14 = reg m0 .rdi) (h3 : reg st.data .rbx = reg m0 .rsi)
    (h15 : reg st.data .r15 = s.phase.toUInt64.toBitVec)
    (hts : TStateAt st.data.dmem (reg m0 .rsi) a s)
    (hrows : RowsAt st.data.dmem (off (stackBelow m0 96) 16)
      (off (a.word (phaseBase a.l s.phase)) 24) rows)
    (hso : NativeRustcVm.SameOutside m0.dmem st.data.dmem (Out m0)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ QueryOpeningsPost a s Q m0 st'.data) st := by
  have c := ctx hpre
  have hst := hpre.1
  have hout := hpre.2.2.2.2.2.2.2.2.2.1
  set out := reg m0 .rdi
  set t := reg m0 .rsi
  set fb := stackBelow m0 96
  have hn : queryOpeningsStack ≤ (rspOf m0).toNat := hst.1
  have hfnw : NativeRustcVm.NoWrap fb (96 + 8) := frame_noWrap hst (by decide)
  obtain ⟨⟨hTm, hTn⟩, ⟨-, hAn⟩, -⟩ := hts.footprint
  have hoF : NativeRustcVm.Apart out 32 fb (96 + 8) := apart_frame hout.2.2.2.2.1 hn (by decide)
  have hTF : NativeRustcVm.Apart t 760 fb (96 + 8) := apart_frame c.tok.1 hn (by decide)
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 96) (rest := [(out, 32), (t, 760)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩
    (rest2_ok ⟨Mapped.keeps hout.1 hf.kept, hout.2.1⟩ ⟨hTm, hTn⟩ fun _ h ↦ h)
    (pairwise3 (Apart.symm' hoF) (Apart.symm' hTF) hout.2.2.1)
  set env := frameEnv m0 st.data 96 [(out, 32), (t, 760)] (fun _ ↦ 0) 0 with henv
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf nofun hpc
    (match_ofMachine ⟨rfl, rfl, rfl, trivial⟩
      ⟨hf.rsp_eval, known_ptr rfl h14, known_ptr rfl h3, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 => ?_
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_b7o hwf nofun
    (hpc1.trans (hp.label NativeRustcVmX64.Vm.TStateQueryOpenings.label_5_at)) hm1 fun st2 hm2 hpc2 => ?_
  obtain ⟨hepi, hw0, hw1, hw2, hw3, hwp, hws⟩ := ok_ok
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf hwf hm2 hepi
  -- The header copied.
  obtain ⟨hp0, hsz, w, hwle, hhdr, hrow⟩ := hrows
  obtain ⟨h0, hhdr⟩ := wordsAt_cons.mp hhdr
  obtain ⟨h1, hhdr⟩ := wordsAt_cons.mp hhdr
  obtain ⟨h2, hhdr⟩ := wordsAt_cons.mp hhdr
  obtain ⟨h3', -⟩ := wordsAt_cons.mp hhdr
  rw [off_off] at h1
  rw [off_off, off_off] at h2
  rw [off_off, off_off, off_off] at h3'
  have v0 := wordAt_write hm2 (r := 1) (o := 0) (b := out) (sz := 32) rfl (by decide) hw0
  have v1 := wordAt_write hm2 (r := 1) (o := 8) (b := out) (sz := 32) rfl (by decide) hw1
  have v2 := wordAt_write hm2 (r := 1) (o := 16) (b := out) (sz := 32) rfl (by decide) hw2
  have v3 := wordAt_write hm2 (r := 1) (o := 24) (b := out) (sz := 32) rfl (by decide) hw3
  rw [show (Sym.load 0 16 8).eval env = _ from load_ofMachine (o := 16) rfl h0, off_zero] at v0
  rw [show (Sym.load 0 24 8).eval env = _ from load_ofMachine (o := 24) rfl h1] at v1
  rw [show (Sym.load 0 32 8).eval env = _ from load_ofMachine (o := 32) rfl h2] at v2
  rw [show (Sym.load 0 40 8).eval env = _ from load_ofMachine (o := 40) rfl h3'] at v3
  have hhdr' : NativeRustcVm.WordsAt st2.data.dmem out [UInt64.ofBitVec
      (off (a.word (phaseBase a.l s.phase)) 24), openingsWords.toUInt64, rows.size.toUInt64,
      w.toUInt64] := by
    refine wordsAt_cons.mpr ⟨v0, wordsAt_cons.mpr ⟨v1, ?_⟩⟩
    rw [off_off]
    refine wordsAt_cons.mpr ⟨v2, wordsAt_cons.mpr ⟨?_, wordsAt_nil _ _⟩⟩
    rw [off_off]; exact v3
  -- The phase advanced.
  have hlt8 : s.phase + 1 < 2 ^ 64 := by
    have := hts.decoded.phases_le
    simp only [LeanVM.Protocol.Compile.wireMaxPhases] at this
    omega
  have vp := wordAt_write hm2 (r := 2) (o := 360) (b := t) (sz := 760) rfl (by decide) hwp
  rw [show (Sym.bin .add .W64 (.reg .r15) (.lit 1)).eval env =
      s.phase.toUInt64.toBitVec + BitVec.ofNat 64 1 from by
    sym_simp
    rw [Env.ofMachine_regs]
    show reg st.data .r15 + _ = _
    rw [h15], toUInt64_add_one hlt8] at vp
  have hs2 : NativeRustcVm.SameOutside st.data.dmem st2.data.dmem (fun q ↦
      Touch t tstateBytes (fun j ↦ 360 ≤ j ∧ j < 368) q ∨ NativeRustcVm.InRange out 32 q) := by
    intro q hq
    refine hm2.get?_mem0 hwf fun hW ↦ hq ?_
    rcases touch_of_written2 hwf (r := 1) (r' := 2) (W := fun _ ↦ True)
      (W' := fun j ↦ 360 ≤ j ∧ j < 368) rfl rfl (fun w hw ↦ by
        rcases hws w hw with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · exact .inl ⟨h1, h2, fun _ _ _ ↦ trivial⟩
        · exact .inr ⟨h1, by omega, fun _ h4 h5 ↦ ⟨by omega, by omega⟩⟩) hW with h | h
    · exact Or.inr (inRange_of_touch hout.2.1 h)
    · exact Or.inl h
  have hts2 : TStateAt st2.data.dmem t a { s with phase := s.phase + 1 } :=
    hts.with_phase (hm2.kept hwf) (fun q hq ↦ c.out_not_t hout hq) hs2 hlt vp
  -- The rows, read in the phase's openings.
  have hrows2 : RowsAt st2.data.dmem out (off (a.word (phaseBase a.l s.phase)) 24) rows := by
    refine ⟨hp0, hsz, w, hwle, hhdr', fun j hj ↦ ⟨(hrow j hj).1, ?_⟩⟩
    obtain ⟨hh, ww, -, -, -, -, -, -, hops⟩ := hts2.decoded.phases s.phase hlt
    subst hrowsP
    have hj' : j < s.openings[s.phase].size := by rw [Array.size_map] at hj; exact hj
    obtain ⟨-, -, -, -, hleaf, -⟩ := hops j hj'
    rw [Array.getElem_map]
    rw [off_off, off_off] at hleaf ⊢
    rw [show 24 + 8 * (1 + j * openingWords) = 8 * (3 + j * openingWords) + 8 by omega]
    exact hleaf
  simp only [PcOk] at hpc2
  refine .done _ ⟨by rw [hpc2]; exact hf.load_ret hst (by decide), hrsp, ?_, ?_, ?_, hsv⟩
  · rw [hrun]
    exact hrows2
  · intro x s' h
    rw [hrun] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hts2
  · intro q hq
    rw [hs2 q (by
      rintro (⟨j, hj, -, rfl⟩ | h)
      · exact hq (Or.inr (Or.inl (inRange_off_self hj (by simp only [tstateBytes]; omega))))
      · exact hq (Or.inl h))]
    exact hso q hq

end

end NativeRustcVmX64.Sumcheck.QueryOpenings
