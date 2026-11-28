module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Bus.AccumulateSide.Loop1
public import NativeRustcVmArm.Tables.Common

/-!
# `accumulate_side`: the normal exit

After the table loop's last turn (`b37` falls through at `b38`): `b38` jumps to `b40`, which
sums the tree's value and the known part, the ones and the padding rows (frame words `32`, `24`;
`136`, `144`; X22, X21) into the output's element and sets X8 to `1`; `b42` stores that tag, restores
the registers and returns (`exit_spec`): `accumulateSide` (`accumulateSide_eq`), its forms at X1,
its total at X0.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVm.Transcript (OptEWAt)

public section

/-! ## The blocks' writes -/

theorem ok_b40 : (∀ w ∈ (after b40 sO).mem, w.r = 1 ∧ w.off + w.n ≤ 24) ∧
    (after b40 sO).sp = sO.sp := by
  rw [after_eq run_b40]; decide

theorem ok_b42 : ∀ w ∈ (after b42 sE).mem, w.r = 1 ∧ w.off + w.n ≤ 24 := by
  rw [after_eq run_b42]; decide

section
variable [Labels] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

/-- The output's 24 bytes and the frame. -/
abbrev rsO (m0 : MachineData) : List (BitVec 64 × Nat) :=
  [(base m0 F, F + 0), (m0.regs.X0.toBitVec, 24)]

omit [Labels] in
/-- The frame between the prologue and the epilogue, the output among its outputs. -/
theorem fr_outsO {m : MachineData} (hfr : Fr m0 F N slots keep (outs m0) m) :
    Fr m0 F N slots keep (outsO m0) m :=
  ⟨hfr.sp, hfr.keep, hfr.slots,
    NativeRustcVm.SameOutside.mono hfr.same fun _ hq ↦ hq.elim Or.inl fun h ↦ Or.inr (Or.inr h),
    hfr.kept⟩

/-- **A word after a block**: its symbolic load's value. -/
theorem wordAt_load {env : Env} {S : SState} {m' : MachineData} (hm : Match env S m')
    (hwf : env.WF) {r o : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    (hle : o + 8 ≤ sz) {v : Sym} (hv : loadSym S.mem r o 8 = v) :
    NativeRustcVm.WordAt m'.dmem (b + BitVec.ofNat 64 o) (UInt64.ofBitVec (v.eval env)) := by
  have hmp : NativeRustcVm.Mapped m'.dmem (b + BitVec.ofNat 64 o) 8 := fun i hi ↦ by
    rw [NativeRustcVm.addr_add_add]
    exact hm.kept hwf _ (hwf.mapped r b sz hb _ (by omega))
  have := NativeRustcVm.wordAt_of_mapped hmp
  rwa [show NativeRustcVm.wordOf m'.dmem (b + BitVec.ofNat 64 o) = UInt64.ofBitVec (v.eval env) from
    UInt64.toBitVec_inj.mp (by rw [Tables.match_wordOf hm hwf hb hle, hv])] at this

/-- The forms through bytes changed only in the output. -/
theorem forms_out (h : Pre L rows bl Fm SL m0) {d d' : DataMem}
    (hs : SameOutside d d' (InRange m0.regs.X0.toBitVec 24)) {G : Array (Array FormW)}
    (hG : FormsAt d m0.regs.X1.toBitVec G) : FormsAt d' m0.regs.X1.toBitVec G :=
  FormsAt.of_same hG (Same.of_sameOutside hs fun _ hj ↦
    not_inRange_of_apart (NativeRustcVm.Apart.symm h.outF) h.formsOk.1.2 h.out.1.2 hj)

/-- A block writing only the output (region `1`) changes only its bytes. -/
theorem same_out (h : Pre L rows bl Fm SL m0) {m m' : MachineData} {S : SState}
    (hm : Match (Env.ofMachine m (rsO m0)) S m') (hwf : (Env.ofMachine m (rsO m0)).WF)
    (hw : ∀ w ∈ S.mem, w.r = 1 ∧ w.off + w.n ≤ 24) :
    SameOutside m.dmem m'.dmem (InRange m0.regs.X0.toBitVec 24) :=
  NativeRustcVm.SameOutside.mono (hm.sameOutside hwf) fun _ hq ↦
    Written.inRange (r := 1) rfl h.out.1.2 hw hq

/-- The output and the frame: a well-formed environment. -/
theorem wfO (h : Pre L rows bl Fm SL m0) {m : MachineData} (hk : Kept m0.dmem m.dmem) :
    (Env.ofMachine m (rsO m0)).WF :=
  wf1 h hk (ROk.whole h.out (by decide))

/-- `b40`'s start: the output at the frame word `16`. -/
theorem matchO (h : Pre L rows bl Fm SL m0) {m : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 F)
    (h16 : (Sym.load 0 16 8).eval (Env.ofMachine m (rsO m0)) = m0.regs.X0.toBitVec) :
    Match (Env.ofMachine m (rsO m0)) sO m :=
  match_ofMachine (sregions := [(F + 0, true), (24, false)]) (regions := rsO m0)
    ⟨rfl, fun _ ↦ Bus.base_aligned h.stack (by decide) rfl, rfl, nofun, trivial⟩
    (sp_eval hsp _ _) trivial trivial trivial
    ⟨by show (Sym.load 0 16 8).eval _ = _; rw [h16]; simp, trivial⟩

/-- `b42`'s start: the output at X10. -/
theorem matchReturn (h : Pre L rows bl Fm SL m0) {m : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 F) (h10 : (m.regs.getXReg .X10).toBitVec = m0.regs.X0.toBitVec) :
    Match (Env.ofMachine m (rsO m0)) sE m :=
  match_ofMachine (sregions := [(F + 0, true), (24, false)]) (regions := rsO m0)
    ⟨rfl, fun _ ↦ Bus.base_aligned h.stack (by decide) rfl, rfl, nofun, trivial⟩
    (sp_eval hsp _ _)
    ⟨by show (m.regs.getXReg .X10).toBitVec = _; rw [h10]; simp [Sym.eval], trivial⟩
    trivial trivial trivial

end

/-! ## The exit -/

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

/-- The model's total: the tree's value and the known part, the ones, the padding rows. -/
theorem total_eq (h : Pre L rows bl Fm SL m0) :
    accumulateSide Fm m0.regs.X2.toNat (BA L rows bl) SL (fpsA m0) (wA m0) (betaA m0) (ptA m0)
        (treeA m0) =
      ((sta SL m0 (BA L rows bl) Fm bl.length).1,
        tk SL m0 + onesT SL (ptA m0) bl.length + (sta SL m0 (BA L rows bl) Fm bl.length).2) := by
  have hfs : (fpsA m0).size = nA m0 := by simp [fpsA]
  have e := accumulateSide_eq Fm m0.regs.X2.toNat (BA L rows bl) SL (fpsA m0) (wA m0) (betaA m0)
    (ptA m0) (treeA m0) (by rw [h.sl_size, BA_size])
  rw [hfs, BA_size] at e
  exact e

/-- The postcondition from the total's limbs at the output, the forms, the bytes changed, the
registers kept. -/
theorem post_of (h : Pre L rows bl Fm SL m0) {m' : MachineData}
    (H : OptEWAt m'.dmem m0.regs.X0.toBitVec
        (some (tk SL m0 + onesT SL (ptA m0) bl.length + (sta SL m0 (BA L rows bl) Fm bl.length).2)) ∧
      FormsAt m'.dmem m0.regs.X1.toBitVec (sta SL m0 (BA L rows bl) Fm bl.length).1 ∧
      SameOutside m0.dmem m'.dmem (fun q ↦ InRange m0.regs.X0.toBitVec 24 q ∨
        InRange m0.regs.X1.toBitVec formsBytes q ∨
        InRange (stackBelow m0 accumulateSideStack) accumulateSideStack q) ∧ Saved m0 m') :
    AccumulateSidePost L rows bl Fm SL m0 m' := by
  have e := total_eq h
  unfold AccumulateSidePost
  show OptEWAt m'.dmem m0.regs.X0.toBitVec (some (accumulateSide Fm m0.regs.X2.toNat
      (BA L rows bl) SL (fpsA m0) (wA m0) (betaA m0) (ptA m0) (treeA m0)).2) ∧
    FormsAt m'.dmem m0.regs.X1.toBitVec (accumulateSide Fm m0.regs.X2.toNat (BA L rows bl) SL
      (fpsA m0) (wA m0) (betaA m0) (ptA m0) (treeA m0)).1 ∧ _ ∧ _
  rw [e]
  exact H

/-- **`accumulate_side`'s normal exit**: from the table loop's end (`b38`), the output's
`Some` of the total, the forms, the registers restored, the return. -/
theorem exit_spec (hp : Placed code k) (h : Pre L rows bl Fm SL m0) {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm bl.length) DL m)
    (hG : FormsAt m.dmem m0.regs.X1.toBitVec (sta SL m0 (BA L rows bl) Fm bl.length).1) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ AccumulateSidePost L rows bl Fm SL m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b38Offset)⟩ := by
  -- `b38`: the jump to `b40`.
  have hwf0 := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b38_in_code.trans hp.1 (by simp [b38])) run_b38 hst.fr (St.lift (D := DL) hst (by decide) 0 [])
    hwf0 (matchF h hst.fr.sp) rfl (by decide) (D' := DL) (E := []) (by decide) (by decide)
    (fun _ _ ↦ holds_nil _ _ _) fun st1 hm1 hpc1 hst1 ↦ ?_
  have hG1 := forms_wrOk h (.inl rfl) hm1 hwf0 (by decide) hG
  simp only [PcOk] at hpc1
  rw [hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b40Offset) NativeRustcVmArm.Vm.AccumulateSide.label_22_at] at hpc1
  refine Gkr.at_pc hpc1 ?_
  -- `b40`: the total's limbs at the output, X8 the tag.
  have hH1 : Holds (rsO m0) (TT SL m0 L rows bl Fm bl.length) DL st1.data :=
    Holds.sub (D' := DL) (St.lift hst1 (by decide) 0 [(m0.regs.X0.toBitVec, 24)]) (by decide)
  have h16 : (Sym.load 0 16 8).eval (Env.ofMachine st1.data (rsO m0)) = m0.regs.X0.toBitVec := by
    rw [Holds.evc hH1 (s := .load 0 16 8) (i := 0) (by decide)]
    rfl
  have hwf1 := wfO h hst1.fr.kept
  have hm1O := matchO h hst1.fr.sp h16
  refine exec_then (b40_in_code.trans hp.1 (by simp [b40])) run_b40 hwf1 hm1O
    fun st2 hm2 hpc2 ↦ ?_
  have hm2' : Match (Env.ofMachine st1.data (rsO m0)) (after b40 sO) st2.data := by
    rw [after_eq run_b40]; exact hm2
  obtain ⟨hw40, hsp40⟩ := ok_b40
  have hfr2 : Fr m0 F N slots keep (outsO m0) st2.data :=
    Fr.ofBlockW (fr_outsO hst1.fr) hm1O hm2' hwf1 rfl hsp40 (fun _ hr ↦ nomatch hr) rfl
      (by decide) h.stack.2.1 slots_le fun w hw ↦ by
        obtain ⟨hr, hn⟩ := hw40 w hw
        refine Or.inr ⟨by omega, fun b sz hb ↦ ?_⟩
        rw [hr] at hb
        cases hb
        exact ⟨hn, fun i hi ↦ Or.inl (NativeRustcVm.inRange_add hi (by decide))⟩
  have hG2 := forms_out h (same_out h hm2' hwf1 hw40) hG1
  have hc0 : UInt64.ofBitVec ((Sym.bin .eor .W64 (.bin .eor .W64 (.load 0 32 8) (.load 0 136 8))
      (.reg .X22)).eval (Env.ofMachine st1.data (rsO m0))) =
      (tk SL m0 + onesT SL (ptA m0) bl.length + (sta SL m0 (BA L rows bl) Fm bl.length).2).c0 := by
    rw [ofBitVec_eor, ofBitVec_eor, Holds.evc hH1 (s := .load 0 32 8) (i := 80) (by decide),
      Holds.evc hH1 (s := .load 0 136 8) (i := 90) (by decide),
      Holds.evc hH1 (s := .reg .X22) (i := 92) (by decide)]
    rfl
  have hc1 : UInt64.ofBitVec ((Sym.bin .eor .W64 (.bin .eor .W64 (.load 0 24 8) (.load 0 144 8))
      (.reg .X21)).eval (Env.ofMachine st1.data (rsO m0))) =
      (tk SL m0 + onesT SL (ptA m0) bl.length + (sta SL m0 (BA L rows bl) Fm bl.length).2).c1 := by
    rw [ofBitVec_eor, ofBitVec_eor, Holds.evc hH1 (s := .load 0 24 8) (i := 81) (by decide),
      Holds.evc hH1 (s := .load 0 144 8) (i := 91) (by decide),
      Holds.evc hH1 (s := .reg .X21) (i := 93) (by decide)]
    rfl
  have e8 := wordAt_load hm2 hwf1 (r := 1) (o := 8) rfl (by omega)
    (v := .bin .eor .W64 (.bin .eor .W64 (.load 0 32 8) (.load 0 136 8)) (.reg .X22)) rfl
  rw [hc0] at e8
  have e16 := wordAt_load hm2 hwf1 (r := 1) (o := 16) rfl (by omega)
    (v := .bin .eor .W64 (.bin .eor .W64 (.load 0 24 8) (.load 0 144 8)) (.reg .X21)) rfl
  rw [hc1] at e16
  have hx8 : UInt64.ofBitVec ((Sym.reg .X8).eval (Env.ofMachine st2.data (rsO m0))) = 1 := by
    show UInt64.ofBitVec (st2.data.regs.getXReg .X8).toBitVec = 1
    rw [hm2.regs .X8 _ rfl]
    rfl
  have h10 : (st2.data.regs.getXReg .X10).toBitVec = m0.regs.X0.toBitVec :=
    (hm2.regs .X10 _ rfl).trans h16
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b42Offset) := by
    rw [← hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b42Offset) NativeRustcVmArm.Vm.AccumulateSide.label_24_at]
    exact hpc2
  -- `b42`: the tag, the registers restored, `ret`.
  have hwf2 := wfO h hfr2.kept
  refine exec_at (b42_in_code.trans hp.1 (by simp [b42])) run_b42 hwf2 hpc2'
    (matchReturn h hfr2.sp h10) fun st3 hm3 hpc3 ↦ Eventually.done _ ?_
  have hm3' : Match (Env.ofMachine st2.data (rsO m0)) (after b42 sE) st3.data := by
    rw [after_eq run_b42]; exact hm3
  obtain ⟨hret, hsv⟩ := Fr.exit hfr2 hm3 hwf2 (by decide)
  have hs3 := same_out h hm3' hwf2 ok_b42
  have t0 := wordAt_load hm3 hwf2 (r := 1) (o := 0) rfl (by omega) (v := .reg .X8) rfl
  rw [hx8, NativeRustcVm.addr_add_zero] at t0
  have t8 := wordAt_keep hm3 (r := 1) (o := 8) rfl (by omega) (by decide) e8
  have t16 := wordAt_keep hm3 (r := 1) (o := 16) rfl (by omega) (by decide) e16
  refine ⟨Eq.trans hpc3 hret, post_of h ⟨⟨t0, ?_⟩, forms_out h hs3 hG2, ?_, hsv⟩⟩
  · rw [NativeRustcVm.ewAt_iff]
    refine ⟨t8, ?_⟩
    show NativeRustcVm.WordAt _ (m0.regs.X0.toBitVec + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) _
    rw [NativeRustcVm.addr_add_add]
    exact t16
  · exact NativeRustcVm.SameOutside.mono (NativeRustcVm.SameOutside.trans hfr2.same hs3)
      fun q hq ↦ hq.elim (fun h1 ↦ h1.elim (fun hs ↦ Or.inr (Or.inr hs))
        fun ho ↦ Or.elim ho Or.inl fun hf ↦ Or.inr (Or.inl hf)) Or.inl

end

end NativeRustcVmArm.Bus.AccumulateSide
