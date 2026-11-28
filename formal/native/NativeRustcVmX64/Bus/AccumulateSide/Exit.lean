module

public import NativeRustcVmX64.Bus.AccumulateSide.TableLoop

/-! # `accumulate_side`: output and return (x86-64) -/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

abbrev totalA (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block)
    (Fm : Array (Array FormW)) (SL : BusLayoutW) (m0 : MachineData) : EW :=
  treeA m0 + knA SL m0 (cA SL m0) + onesT SL (ptA m0) bl.length +
    (stA L rows bl Fm SL m0 bl.length).2

end

public section

 theorem track_end : trackOk [12040] (after b28 fS) DT DT = true ∧
    trackOk [12040, 24] (after b30 outS) DT [(Lw 80, 0)] = true := by
  rw [after_eq run_b28, after_eq run_b30]; decide +kernel

theorem tag_write : ∀ i < 8, findWrite 0 (32 + i) (after b30 outS).mem = some (.lit 1, i) := by
  rw [after_eq run_b30]; decide +kernel

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

 theorem finish (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    {m : MachineData} (hth : TH L rows bl Fm SL m0 bl.length m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧
      rspOf st.data = rspOf m0 + 8#64 ∧ AccumulateSidePost L rows bl Fm SL m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b28Offset)⟩ := by
  obtain ⟨hst, hG⟩ := hth
  obtain ⟨hmid28, hw28, _⟩ := ok_b28
  refine St.run h (rest := []) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b28_in_code (by simp [b28]) hp) exit_b28 nofun hst.fr hst.same
    (hst.hd.reg0 (by decide) rfl) (by decide) (wf0 h hst.fr.kept)
    (St.mt hst ⟨rfl, trivial⟩ trivial trivial trivial) hmid28 (by rw [hw28]; rfl)
    (by decide) track_end.1 fun st1 hm1 hpc1 hs1 _ ↦ ?_
  have hG1 : FormsAt st1.data.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 bl.length).1 :=
    FormsAt.of_same hG fun i _ ↦ hm1.get?_mem0 (wf0 h hst.fr.kept) fun hw ↦ by
      obtain ⟨w, hw, _⟩ := hw
      rw [hw28] at hw
      contradiction
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b30Offset) := hpc1.trans (hp.label NativeRustcVmX64.Vm.AccumulateSide.label_12_at)
  obtain ⟨d1, pc1⟩ := st1
  simp only at hpc1' hs1 hG1
  subst hpc1'
  let out := reg m0 .rdi
  let env := frameEnv m0 d1 F [(out, 24)] (fun _ ↦ 0) 0
  have hin : In m0 out 24 := In.of_inOk h.out h.outF
  have hwf : env.WF := wf1 h hs1.fr.kept hin
  have g80 : env.load 0 80 8 = out := hs1.hd.load (r := 0) (o := 80) (i := 0) (by decide)
  have hm : Match env outS d1 := St.mt hs1 ⟨rfl, rfl, trivial⟩ trivial trivial
    ⟨by change env.load 0 80 8 = out + 0#64
        rw [BitVec.add_zero]; exact g80, trivial⟩
  obtain ⟨hmid30, hw30, _, h32, h8, h16⟩ := ok_b30
  refine exec_then (infix_of b30_in_code (by simp [b30]) hp) exit_b30 hwf nofun hm
    fun st2 hm2 hpc2 ↦ ?_
  have hfr2 := Frame.of_block hs1.fr hwf hm2 hmid30 slots_le
  have hhd2 := Holds.after (show ((fb m0, F + 8) :: [(out, 24)]).map Prod.snd = [12040, 24] from rfl)
    (hs1.hd.reg0 (rs' := [(fb m0, F + 8), (out, 24)]) (by decide) rfl) (by decide) hm2 track_end.2
  have hso2 : NativeRustcVm.SameOutside d1.dmem st2.data.dmem
      (fun q ↦ NativeRustcVm.InRange (fb m0) F q ∨ NativeRustcVm.InRange out 24 q) :=
    fun q hq ↦ hm2.get?_mem0 hwf fun hW ↦ hq
      (NativeRustcVmX64.Sumcheck.written_frame2 hm2 (writesIn_of_mid hmid30)
        (belowRet_of_mid hmid30) h.out.1.2 h.frame_nw hW)
  have hword32 : NativeRustcVm.WordAt st2.data.dmem (off (fb m0) 32) 1 := by
    apply wordAt_write_eq hm2 (r := 0) (b := fb m0) (o := 32) (sz := F + 8) rfl (by decide) (.lit 1)
    · exact tag_write
    · rfl
  have hval0 : (Sym.bin .xor .W64 (.bin .xor .W64 (.load 0 64 8) (.reg .r14)) (.reg .rsi)).eval env =
      (totalA L rows bl Fm SL m0).c0.toBitVec := by
    change BinOp.apply .xor .W64 (BinOp.apply .xor .W64
      ((Env.ofMachine d1 [(fb m0, F + 8)]).load 0 64 8) (d1.regs.get64 .r14)) (d1.regs.get64 .rsi) = _
    rw [xor64, xor64, hs1.hd.load (r := 0) (o := 64) (i := 20) (by decide),
      hs1.hd.reg (r := .r14) (i := 35) (by decide), hs1.hd.reg (r := .rsi) (i := 33) (by decide)]
    simp only [totalA, add_c0, UInt64.toBitVec_xor]; rfl
  have hval1 : (Sym.bin .xor .W64 (.bin .xor .W64 (.load 0 72 8) (.reg .r15)) (.reg .rdx)).eval env =
      (totalA L rows bl Fm SL m0).c1.toBitVec := by
    change BinOp.apply .xor .W64 (BinOp.apply .xor .W64
      ((Env.ofMachine d1 [(fb m0, F + 8)]).load 0 72 8) (d1.regs.get64 .r15)) (d1.regs.get64 .rdx) = _
    rw [xor64, xor64, hs1.hd.load (r := 0) (o := 72) (i := 21) (by decide),
      hs1.hd.reg (r := .r15) (i := 36) (by decide), hs1.hd.reg (r := .rdx) (i := 34) (by decide)]
    simp only [totalA, add_c1, UInt64.toBitVec_xor]; rfl
  have hout0 := wordAt_write_eq hm2 (b := out) (o := 8) rfl (by decide) _ h8 hval0
  have hout1 := wordAt_write_eq hm2 (b := out) (o := 16) rfl (by decide) _ h16 hval1
  have hsameForms2 : Same d1.dmem st2.data.dmem (reg m0 .rsi) formsBytes := fun i hi ↦
    hso2 _ fun hq ↦ hq.elim
      (fun hq ↦ (forms_out h hi).1 (Ring.inRange_le hq (by omega)))
      (fun hq ↦ NativeRustcVm.Apart.not_inRange_add (Apart.symm' h.outF) h.forms_nw h.out.1.2 hi hq)
  have hG2 := FormsAt.of_same hG1 hsameForms2
  let env3 := frameEnv m0 st2.data F [(out, 24)] (fun _ ↦ 0) 0
  have hwf3 : env3.WF := wf1 h hfr2.kept hin
  have g80' : env3.load 0 80 8 = out := hhd2.load (r := 0) (o := 80) (i := 0) (by decide)
  have hm3 : Match env3 outS st2.data := match_ofMachine ⟨rfl, rfl, trivial⟩
    ⟨hfr2.rsp_eval, trivial⟩ trivial trivial ⟨by
      change env3.load 0 80 8 = out + 0#64
      rw [BitVec.add_zero]; exact g80', trivial⟩
  refine exec_at (infix_of b31_in_code (by simp [b31]) hp) exit_b31 hwf3 nofun hpc2 hm3
    fun st3 hm3' hpc3 ↦ ?_
  obtain ⟨hepi, h0, hw31⟩ := ok_b31
  obtain ⟨hsv, hsp⟩ := Frame.epilogue hfr2 hwf3 hm3' hepi
  have hso3 : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem (NativeRustcVm.InRange out 8) :=
    sameOutside_low hwf3 hm3' (r := 1) (N := 24) rfl (by decide) fun w hw ↦ by
      have hw' := List.all_eq_true.mp hw31 w hw
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw'
      exact hw'
  have htag : NativeRustcVm.WordAt st3.data.dmem out 1 := by
    have hx := wordAt_write_eq hm3' (r := 1) (b := out) (o := 0) (sz := 24) rfl (by decide)
      (.load 0 32 8) (by simpa only [Nat.zero_add] using h0)
      (load_ofMachine (r := 0) rfl hword32)
    simpa only [off_zero] using hx
  have hwkeep {o : Nat} {w : UInt64} (ho : 8 ≤ o) (hon : o + 8 ≤ 24)
      (hx : NativeRustcVm.WordAt st2.data.dmem (off out o) w) :
      NativeRustcVm.WordAt st3.data.dmem (off out o) w := by
    apply bytesAt_congr hx
    intro i hi
    have hi' : i < 8 := by simpa only [NativeRustcVm.length_wordBytes] using hi
    rw [off_add]
    apply hso3
    have hnw : out.toNat + 24 ≤ 2 ^ 64 := h.out.1.2
    have he := inRange_off_iff (b := out) (o := 0) (n := 8) (j := o + i) (by omega) (by omega)
    rw [off_zero] at he
    rw [he]
    omega
  have hG3 := FormsAt.of_same hG2 (fun i hi ↦ hso3 _ fun hq ↦
    NativeRustcVm.Apart.not_inRange_add (Apart.symm' h.outF) h.forms_nw h.out.1.2 hi
      (Ring.inRange_le hq (by decide)))
  have hmodel : accumulateSide Fm (reg m0 .rdx).toNat (BA L rows bl) SL (fpsA m0) (wA m0)
      (betaA m0) (ptA m0) (treeA m0) =
      ((stA L rows bl Fm SL m0 bl.length).1, totalA L rows bl Fm SL m0) := by
    rw [accumulateSide_eq _ _ _ _ _ _ _ _ _ (by rw [BA_size]; exact h.sl_size), BA_size]
    have hfps : (fpsA m0).size = nA m0 := by simp [fpsA, NativeRustcVm.ewsOf]
    rw [hfps, Nat.min_comm]
  refine .done _ ⟨?_, hsp, ?_⟩
  · change st3.pc = Int64.ofBitVec (env3.load 0 12032 8) at hpc3
    rw [hpc3]; exact hfr2.load_ret h.stack le_F
  · change OptEWAt st3.data.dmem out (some (accumulateSide Fm (reg m0 .rdx).toNat (BA L rows bl)
      SL (fpsA m0) (wA m0) (betaA m0) (ptA m0) (treeA m0)).2) ∧
      FormsAt st3.data.dmem (reg m0 .rsi) (accumulateSide Fm (reg m0 .rdx).toNat (BA L rows bl)
      SL (fpsA m0) (wA m0) (betaA m0) (ptA m0) (treeA m0)).1 ∧ _
    rw [hmodel]
    refine ⟨⟨htag, ?_⟩, hG3, ?_, hsv⟩
    · exact ewAt_iff.mpr ⟨hwkeep (by decide) (by decide) hout0, by
        rw [off_off]; exact hwkeep (by decide) (by decide) hout1⟩
    · intro q hq
      have ho : ¬ NativeRustcVm.InRange out 24 q := fun hq' ↦ hq (.inl hq')
      have hf : ¬ outs m0 q := fun hq' ↦ hq (.inr (.inl hq'))
      have hs : ¬ NativeRustcVm.InRange (stackBelow m0 N) N q := fun hq' ↦ hq (.inr (.inr hq'))
      exact (hso3 q (fun hx ↦ ho (Ring.inRange_le hx (by decide)))).trans
        ((hso2 q (fun hx ↦ hx.elim (fun hx ↦ hs (inRange_frame_stack h.sp8 h.spN le_F hx)) ho)).trans
          (hs1.same q (fun hx ↦ hx.elim hf hs)))

end

end NativeRustcVmX64.Bus.AccumulateSide
