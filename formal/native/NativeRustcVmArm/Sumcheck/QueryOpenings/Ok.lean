module

public import NativeRustcVmArm.Sumcheck.QueryOpenings.Fail
public import NativeRustcVm.Sumcheck.PhaseUpdate

/-!
# `TState::query_openings`'s `Some` exit

`b6` (`k + NativeRustcVmArm.Vm.TStateQueryOpenings.b6Offset`) copies `open_phase`'s `Rows` (the frame's first 32 bytes) to the output (X19),
stores the phase index plus one at `t + 360` (X20) and runs the epilogue: the rows, read in the
phase's openings, at the output and the `TState` at its next phase (`finish_ok`).
-/

namespace NativeRustcVmArm.Sumcheck.QueryOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateQueryOpenings
open NativeRustcVm.Transcript NativeVm NativeVm.Model NativeRustcArm NativeRustcVmArm.Transcript
open NativeRustcVm.Sumcheck

public section

theorem ofInt_neg360 : (BitVec.ofInt 64 (-360)).toNat = 2 ^ 64 - 360 := by
  rw [BitVec.toNat_ofInt]; rfl

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

/-- **`b6`**: the rows copied to the output, the phase advanced, the epilogue. -/
theorem finish_ok (hp : Placed code k) {a : DecArea} {s : TState} {Q : Array UInt64}
    {m0 : MachineData} (hpre : QueryOpeningsPre a s Q m0) {rows : Array (Array UInt64)}
    (hrun : (queryOpenings m0.regs.X2.toNat Q).run s =
      some (rows, { s with phase := s.phase + 1 }))
    (hlt : s.phase < s.openings.size) (hrowsP : rows = s.openings[s.phase].map (·.leaf))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateQueryOpenings.b6Offset)) (hf : Frame m0 96 slots st.data)
    (hx19 : st.data.regs.X19 = m0.regs.X0) (hx20 : st.data.regs.X20 = m0.regs.X1)
    (hx21 : st.data.regs.X21 = s.phase.toUInt64)
    (hts : TStateAt st.data.dmem m0.regs.X1.toBitVec a s)
    (hrows : RowsAt st.data.dmem (frameBase m0 96) (off (a.word (phaseBase a.l s.phase)) 24) rows)
    (hso : SameOutside m0.dmem st.data.dmem (Out m0)) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = retOf m0 ∧ QueryOpeningsPost a s Q m0 st'.data) st := by
  obtain ⟨hst, -, -, htok, -, -, -, -, -, hout, -⟩ := hpre
  set out := m0.regs.X0.toBitVec
  set t := m0.regs.X1.toBitVec
  set fb := frameBase m0 96
  set pw := off t 360
  have hn : queryOpeningsStack ≤ m0.regs.SP.toNat := hst.2.1
  have hfnw : fb.toNat + 96 ≤ 2 ^ 64 := frame_noWrap (by rw [stack_eq] at hn; omega)
  obtain ⟨⟨hTm, hTn⟩, ⟨-, hAn⟩, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hTF : t.toNat + 760 ≤ fb.toNat ∨ fb.toNat + 96 ≤ t.toNat :=
    apart_frame htok.1 hn (by decide)
  have hOF : out.toNat + 32 ≤ fb.toNat ∨ fb.toNat + 96 ≤ out.toNat :=
    apart_frame hout.2.2.2.2.1 hn (by decide)
  have hOT : out.toNat + 32 ≤ t.toNat ∨ t.toNat + 760 ≤ out.toNat := hout.2.2.1
  have hon : out.toNat + 32 ≤ 2 ^ 64 := hout.2.1
  have hpw : pw.toNat = t.toNat + 360 := toNat_off (by omega)
  have hwf : (frameEnv m0 st.data 96 [(out, 32), (pw, 8)]).WF := by
    refine Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 96) hst (by decide)) hf.kept, hfnw⟩,
      ⟨Mapped.keeps hout.1 hf.kept, hon⟩,
      ⟨mapped_off hTm (by show 360 + 8 ≤ 760; omega), by show pw.toNat + 8 ≤ 2 ^ 64; omega⟩,
      trivial⟩ (pairwise3 ?_ ?_ ?_)
    · show fb.toNat + 96 ≤ out.toNat ∨ out.toNat + 32 ≤ fb.toNat; omega
    · show fb.toNat + 96 ≤ pw.toNat ∨ pw.toNat + 8 ≤ fb.toNat; omega
    · show out.toNat + 32 ≤ pw.toNat ∨ pw.toNat + 8 ≤ out.toNat; omega
  have hm : Match (frameEnv m0 st.data 96 [(out, 32), (pw, 8)]) okS st.data := by
    refine match_ofMachine
      ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, rfl, nofun, trivial⟩
      (by rw [hf.sp]; exact (eval_ptr rfl).symm)
      ⟨known_ptr rfl (by show st.data.regs.X19.toBitVec = _; rw [hx19]), trivial⟩ trivial trivial
      ⟨?_, trivial⟩
    show (st.data.regs.getXReg .X20).toBitVec = pw + BitVec.ofInt 64 (-360)
    show st.data.regs.X20.toBitVec = _
    rw [hx20]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hpw, ofInt_neg360]
    show t.toNat = _
    omega
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf hpc hm fun st1 hm1 hpc1 => ?_
  obtain ⟨hepi, hw0, hw1, hw2, hw3, hwp, hws⟩ := after_eq run_b6 ▸ ok_b6
  obtain ⟨hsv, hsl⟩ := Frame.epilogue hf hwf hm1 hepi
  have hx30 : st1.data.regs.X30 = m0.regs.X30 := hsl (32, .X30) (List.mem_cons_self ..)
  set env := frameEnv m0 st.data 96 [(out, 32), (pw, 8)]
  -- The header copied.
  obtain ⟨hp0, hsz, w, hwle, hhdr, hrow⟩ := hrows
  obtain ⟨h0, hhdr⟩ := wordsAt_cons.mp hhdr
  obtain ⟨h1, hhdr⟩ := wordsAt_cons.mp hhdr
  obtain ⟨h2, hhdr⟩ := wordsAt_cons.mp hhdr
  obtain ⟨h3, -⟩ := wordsAt_cons.mp hhdr
  rw [← off_zero fb] at h0
  rw [off_off] at h2
  rw [off_off, off_off] at h3
  have v0 := wordAt_write hm1 (r := 1) (o := 0) (b := out) (sz := 32) rfl (by decide) hw0
  have v1 := wordAt_write hm1 (r := 1) (o := 8) (b := out) (sz := 32) rfl (by decide) hw1
  have v2 := wordAt_write hm1 (r := 1) (o := 16) (b := out) (sz := 32) rfl (by decide) hw2
  have v3 := wordAt_write hm1 (r := 1) (o := 24) (b := out) (sz := 32) rfl (by decide) hw3
  rw [show (Sym.load 0 0 8).eval env = _ from load_ofMachine (o := 0) rfl h0, off_zero] at v0
  rw [show (Sym.load 0 8 8).eval env = _ from load_ofMachine (o := 8) rfl h1] at v1
  rw [show (Sym.load 0 16 8).eval env = _ from load_ofMachine (o := 16) rfl h2] at v2
  rw [show (Sym.load 0 24 8).eval env = _ from load_ofMachine (o := 24) rfl h3] at v3
  have hhdr' : NativeRustcVm.WordsAt st1.data.dmem out [UInt64.ofBitVec
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
  have vp := wordAt_write hm1 (r := 2) (o := 0) (b := pw) (sz := 8) rfl (by decide) hwp
  rw [off_zero, show (Sym.bin .add .W64 (.reg .X21) (.lit 1)).eval env =
      s.phase.toUInt64.toBitVec + BitVec.ofNat 64 1 from by
    sym_simp
    rw [Env.ofMachine_regs]
    show st.data.regs.X21.toBitVec + _ = _
    rw [hx21], toUInt64_add_one hlt8] at vp
  have hs1 : SameOutside st.data.dmem st1.data.dmem (fun q ↦
      Touch t tstateBytes (fun j ↦ 360 ≤ j ∧ j < 368) q ∨ NativeRustcVm.InRange out 32 q) := by
    intro q hq
    refine hm1.get?_mem0 hwf fun hW ↦ hq ?_
    rcases touch_of_written2 hwf (r := 1) (r' := 2) rfl rfl (by decide) hws hW with h | h
    · exact Or.inr (inRange_of_touch hon h)
    · exact Or.inl (touch_of_inRange hTn (by show 360 + 8 ≤ 760; omega) h)
  have hts1 : TStateAt st1.data.dmem t a { s with phase := s.phase + 1 } :=
    hts.with_phase (hm1.kept hwf)
      (fun q hq ↦ ⟨not_inRange_of_apart hout.2.2.1 hout.2.1 hTn hq,
        not_inRange_of_apart hout.2.2.2.1 hout.2.1 hAn hq⟩) hs1 hlt vp
  -- The rows, read in the phase's openings.
  have hrows1 : RowsAt st1.data.dmem out (off (a.word (phaseBase a.l s.phase)) 24) rows := by
    refine ⟨hp0, hsz, w, hwle, hhdr', fun j hj ↦ ⟨(hrow j hj).1, ?_⟩⟩
    obtain ⟨hh, ww, -, -, -, -, -, -, hops⟩ := hts1.decoded.phases s.phase hlt
    subst hrowsP
    have hj' : j < s.openings[s.phase].size := by rw [Array.size_map] at hj; exact hj
    obtain ⟨-, -, -, -, hleaf, -⟩ := hops j hj'
    rw [Array.getElem_map]
    rw [off_off, off_off] at hleaf ⊢
    rw [show 24 + 8 * (1 + j * openingWords) = 8 * (3 + j * openingWords) + 8 by omega]
    exact hleaf
  refine .done _ ⟨by simp only [PcOk] at hpc1; rw [hpc1]; simp only [retOf, hx30], ?_, ?_, ?_, hsv⟩
  · rw [hrun]
    exact hrows1
  · intro x s' h
    rw [hrun] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hts1
  · intro q hq
    rw [hs1 q (by
      rintro (⟨j, hj, -, rfl⟩ | h)
      · exact hq (Or.inr (Or.inl (inRange_off_self hj (by simp only [tstateBytes]; omega))))
      · exact hq (Or.inl h))]
    exact hso q hq

end

end NativeRustcVmArm.Sumcheck.QueryOpenings
