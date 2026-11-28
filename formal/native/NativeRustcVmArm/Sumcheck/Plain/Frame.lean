module

public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.Sumcheck.Plain.Exec
public import NativeRustcVmArm.Sumcheck.Loop

/-!
# `sumcheck` with `sumcheck_plain`'s closure: the frame, the entry, the exits

The 160-byte frame (`FrP`, `Ring.Fr`): the saved X30, X23, …, X19 at `112` (`slotsP`), X24 to X29
kept. The loop's head `.L2` after `i < n` rounds (`Inv`: X19 the output, X20 slot `i`, X21 the
count, X22 the `TState`, X23 the slots' end, X2, X3 the claim, `Rounds`); `.L4` after the last
(`Done`). `entry_spec`: `b0`, `b1` to the head, or to `.L4` without slots; `exit_done` (`b7`):
the claim at the output; `exit_fail` (`b8`): `None`.
-/

namespace NativeRustcVmArm.Sumcheck.Plain

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck

@[expose] public section

/-- The saved registers' slots. -/
def slotsP : List (Nat × XReg) :=
  [(112, .X30), (120, .X23), (128, .X22), (136, .X21), (144, .X20), (152, .X19)]

/-- The callee-saved registers the function keeps. -/
def keepP : List XReg := [.X24, .X25, .X26, .X27, .X28, .X29]

/-- The `TState`, the output, the slots, their count, the count, the claim: X1, X0, X5, X6, X4,
X2 and X3 at the entry. -/
abbrev tP (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
abbrev outP (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
abbrev slP (m0 : MachineData) : BitVec 64 := m0.regs.X5.toBitVec
abbrev nP (m0 : MachineData) : Nat := m0.regs.X6.toNat
abbrev cntP (m0 : MachineData) : Nat := m0.regs.X4.toNat
abbrev claimP (m0 : MachineData) : EW := ⟨m0.regs.X2, m0.regs.X3⟩

/-- The frame. -/
abbrev FrP [Labels] (m0 m : MachineData) : Prop :=
  Fr m0 160 sumcheckPlainStack slotsP keepP (outsOf (tP m0) (outP m0) (slP m0) (nP m0)) m

/-- The model's run after `i` rounds. -/
abbrev RoundsP (a : DecArea) (s : TState) (m0 : MachineData) (d : Mem 64) (i : Nat) (c : EW) :
    Prop :=
  Rounds d (tP m0) a (slP m0) (claimP m0) (cntP m0) (fun _ ↦ none) s i c

/-- **The loop's invariant** at `.L2`, `i < n` rounds done. -/
structure Inv [Labels] (a : DecArea) (s : TState) (m0 : MachineData) (i : Nat) (m : MachineData) :
    Prop where
  fr : FrP m0 m
  lt : i < nP m0
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  x20 : (m.regs.getXReg .X20).toBitVec = slP m0 + BitVec.ofNat 64 (16 * i)
  x21 : m.regs.getXReg .X21 = m0.regs.X4
  x22 : m.regs.getXReg .X22 = m0.regs.X1
  x23 : (m.regs.getXReg .X23).toBitVec = slP m0 + BitVec.ofNat 64 (16 * nP m0)
  run : RoundsP a s m0 m.dmem i ⟨m.regs.X2, m.regs.X3⟩

/-- At `.L4`: every round done. -/
structure Done [Labels] (a : DecArea) (s : TState) (m0 : MachineData) (m : MachineData) : Prop where
  fr : FrP m0 m
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  run : RoundsP a s m0 m.dmem (nP m0) ⟨m.regs.X2, m.regs.X3⟩

end

public section

variable [Host] {a : DecArea} {s : TState} {m0 : MachineData} {k : Nat}

theorem geo (h : SumcheckPlainPre a s m0) :
    Geo a s m0 (tP m0) (outP m0) (slP m0) (cntP m0) (nP m0) sumcheckPlainStack 160 slotsP
      (outsOf (tP m0) (outP m0) (slP m0) (nP m0)) :=
  ⟨h, fun _ h ↦ h, fun _ h ↦ .inr (.inr h), fun _ h ↦ .inr (.inl h), by decide, by decide,
    by decide, by decide⟩

omit [Host] in
theorem keepP_saved : ∀ r ∈ keepP, calleeSaved r = true := by decide

omit [Host] in
theorem slotsP8 : ∀ p ∈ slotsP, p.1 + 8 ≤ 160 := by decide

/-- **The exits' common part**: from the frame at `.L4` or `.L5`, `b7`/`b8` from `outS`. -/
theorem exit_of (hpre : SumcheckPlainPre a s m0) {m : MachineData} (hf : FrP m0 m)
    (hx19 : m.regs.getXReg .X19 = m0.regs.X0) {ds : List Directive} {j : Nat} {S' : SState}
    (hk : ds.IsInfixAt Host.prog j) (hx : exec ds outS = some (S', .ret))
    (hok : exitOk S' 160 slotsP keepP = true) (hW : ∀ w ∈ S'.mem, w.r = 1 ∧ w.off + w.n ≤ 24)
    {r : Option ((Array EW × EW) × TState)}
    (hr : r = (sumcheckPlain (claimP m0) (cntP m0) (nP m0)).run s)
    (hxs : ∀ xs c s', r = some ((xs, c), s') →
      xs.toList.length ≤ nP m0 ∧ NativeRustcVm.EWsAt m.dmem (slP m0) xs.toList)
    (hts : NextAt m.dmem (tP m0) a r)
    (hout : ∀ st : MachineState,
      Match (Env.ofMachine m [(base m0 160, 160), (outP m0, 24)]) S' st.data →
      OptEWAt st.data.dmem (outP m0) (r.map (·.1.2))) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ SumcheckPlainPost a s m0 st.data) ⟨m, Host.addrOf j⟩ := by
  have g := geo hpre
  have hS := hpre.1
  have hwf : (Env.ofMachine m [(base m0 160, 160), (outP m0, 24)]).WF :=
    Bus.wf_frame2 hS (by decide) hf.kept ⟨g.outOk.1, g.outOk.2.1⟩ g.outOk.2.2.2.2.1
  have hm : Match (Env.ofMachine m [(base m0 160, 160), (outP m0, 24)]) outS m := by
    have := Bus.match_frame2 (r := .X19) (n := 24) hS (by decide) (by decide) hf.sp
    rwa [hx19] at this
  refine exec_then hk hx hwf hm fun st hm' hpc ↦ Eventually.done _ ?_
  obtain ⟨hret, hsv⟩ := Fr.exit hf hm' hwf hok
  have hwr : ∀ q, Written (Env.ofMachine m [(base m0 160, 160), (outP m0, 24)]) S' q →
      InRange (outP m0) 24 q := fun q hq ↦ Written.inRange (r := 1) rfl g.outOk.2.1 hW hq
  have hs := hm'.sameOutside hwf
  refine ⟨hpc.trans hret, ?_, ?_, hsv⟩
  · rw [← hr]
    refine ⟨hout st hm', fun xs c s' h ↦ g.sl_keep hs (fun q hq ↦ .inr (.inr (hwr q hq)))
      (hxs xs c s' h).1 (hxs xs c s' h).2, fun x s' h ↦
        g.t_keep hs (hm'.kept hwf) (fun q hq ↦ .inr (.inr (hwr q hq))) (hts x s' h)⟩
  · refine NativeRustcVm.SameOutside.mono (NativeRustcVm.SameOutside.trans hf.same hs)
      fun q hq ↦ ?_
    rcases hq with (hq | hq | hq | hq) | hq
    · exact .inr (.inr (.inr hq))
    · exact .inl hq
    · exact .inr (.inl hq)
    · exact .inr (.inr (.inl hq))
    · exact .inl (hwr q hq)

/-- **`b7`**: every round done, the claim into the output, the exit. -/
theorem exit_done (hp : Placed code k) (hpre : SumcheckPlainPre a s m0) {m : MachineData}
    (hd : Done a s m0 m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ SumcheckPlainPost a s m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b7Offset)⟩ := by
  obtain ⟨xs, sn, hrun, hsz, hxs, hts⟩ := hd.run
  have hk7 : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b7Offset) := b7_in_code.trans hp.1 (by simp [b7])
  have hr : (sumcheckPlain (claimP m0) (cntP m0) (nP m0)).run s =
      some ((xs, ⟨m.regs.X2, m.regs.X3⟩), sn) := by
    rw [← sumcheckFn_none]; exact hrun
  refine exit_of hpre hd.fr hd.x19 hk7 run_b7 (by decide) (by decide) hr.symm
    (fun xs' c s' h ↦ by cases h; exact ⟨by simp [hsz], hxs⟩) (fun x s' h ↦ by cases h; exact hts)
    fun st hm' ↦ ?_
  have w0 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 1) (o := 0) rfl (by decide)
    (v := .lit 1) (by decide +kernel)
  have w8 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 1) (o := 8) rfl (by decide)
    (v := .reg .X2) (by decide +kernel)
  have w16 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 1) (o := 16) rfl (by decide)
    (v := .reg .X3) (by decide +kernel)
  rw [NativeRustcVm.addr_add_zero] at w0
  refine ⟨w0, ?_⟩
  rw [NativeRustcVm.ewAt_iff]
  refine ⟨w8, ?_⟩
  rw [NativeRustcVm.addr_add_add]
  exact w16

/-- **`b8`**: a rejected round, `None` into the output, the exit. -/
theorem exit_fail (hp : Placed code k) (hpre : SumcheckPlainPre a s m0) {m : MachineData}
    (hf : FrP m0 m) (hx19 : m.regs.getXReg .X19 = m0.regs.X0)
    (hnone : (sumcheckFn (claimP m0) (cntP m0) (fun _ ↦ none) (nP m0)).run s = none) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ SumcheckPlainPost a s m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b8Offset)⟩ := by
  have hk8 : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b8Offset) := b8_in_code.trans hp.1 (by simp [b8])
  refine exit_of hpre hf hx19 hk8 run_b8 (by decide) (by decide) (r := none)
    (by rw [← sumcheckFn_none]; exact hnone.symm) (fun _ _ _ h ↦ (nomatch h))
    (fun _ _ h ↦ (nomatch h)) fun st hm' ↦ ?_
  have w0 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 1) (o := 0) rfl (by decide)
    (v := .lit 0) (by decide +kernel)
  rw [NativeRustcVm.addr_add_zero] at w0
  exact w0

omit [Host] in
/-- `x <<< 4` is `16 x`. -/
theorem shl4 (x : BitVec 64) : x <<< 4 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq]
  congr 1
  omega

/-- **The entry**: `b0` saves the registers; without slots at `.L4`, else `b1` and the loop's
head with no round done. -/
theorem entry_spec (hp : Placed code k) (hpre : SumcheckPlainPre a s m0) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b7Offset) ∧ Done a s m0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b2Offset) ∧ Inv a s m0 0 st.data))
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b0Offset)⟩ := by
  have g := geo hpre
  have hS := hpre.1
  have hwf : (Bus.env0 m0 160).WF := Bus.wf_env0 hS (by decide)
  have hm : Match (Bus.env0 m0 160) entryS m0 := Bus.match_entry hS (by decide) (by decide)
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b0Offset) := b0_in_code.trans hp.1 (by simp [b0])
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b1Offset) := b1_in_code.trans hp.1 (by simp [b1])
  have hl4 : Labels.label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b7Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b7Offset) NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.label_4_at
  have hts0 := g.ok.2.2.1
  -- The frame and the `TState` after the prologue's writes.
  have hpro : ∀ {S : SState} {st : MachineState}, Match (Bus.env0 m0 160) S st.data →
      S.mem = (after b0 entryS).mem → S.sp = .ptr 0 0 →
      (∀ r ∈ keepP, S.reg r = some (.reg r)) →
      FrP m0 st.data ∧ TStateAt st.data.dmem (tP m0) a s := by
    intro S st hmS hmem hsp hkeep
    have hW : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 160 := by
      rw [hmem, after_eq run_b0]; decide +kernel
    refine ⟨Fr.ofPrologue (F := 160) (rs := []) g.hN (by decide) hmS hwf hsp
      (by rw [show slotsOk S slotsP = slotsOk (after b0 entryS) slotsP from by
            simp only [slotsOk, hmem]]
          rw [after_eq run_b0]; decide +kernel) (by decide) hW hkeep, ?_⟩
    refine g.t_keep (hmS.sameOutside hwf) (hmS.kept hwf) (fun q hq ↦ .inl ?_) hts0
    exact g.ctx.inRange_frame
      (Written.inRange rfl (base_noWrap (le_trans (by decide) g.hN)) hW hq)
  refine exec_then hk0 run_b0 hwf hm fun st hm' hpc ↦ ?_
  have hm0 : Match (Bus.env0 m0 160) (after b0 entryS) st.data := by
    rw [after_eq run_b0]; exact hm'
  obtain ⟨hfr, hts⟩ := hpro hm0 rfl (by rw [after_eq run_b0])
    (by rw [after_eq run_b0]; decide +kernel)
  have hc : (SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X6) (.lit 0)).eval (Bus.env0 m0 160) =
      (m0.regs.X6.toBitVec == 0#64) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]; rfl
  simp only [PcOk] at hpc
  rw [hc] at hpc
  have hx2 : st.data.regs.X2 = m0.regs.X2 := UInt64.toBitVec_inj.mp ((hm'.regs .X2 _ rfl).trans rfl)
  have hx3 : st.data.regs.X3 = m0.regs.X3 := UInt64.toBitVec_inj.mp ((hm'.regs .X3 _ rfl).trans rfl)
  by_cases h0 : m0.regs.X6 = 0
  · have h0' : (m0.regs.X6.toBitVec == 0#64) = true := by rw [h0]; rfl
    simp only [h0', ↓reduceIte] at hpc
    refine Eventually.done _ (Or.inl ⟨hpc.trans hl4, hfr,
      UInt64.toBitVec_inj.mp ((hm'.regs .X19 _ rfl).trans rfl), ?_⟩)
    rw [hx2, hx3, show nP m0 = 0 by simp [nP, h0]]
    exact rounds_zero hts
  · have h0' : (m0.regs.X6.toBitVec == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun h ↦ h0 (UInt64.toBitVec_inj.mp h)
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at hpc
    refine exec_at hk1 run_b1 hwf hpc hm0 fun st1 hm1 hpc1 ↦ ?_
    have hm1' : Match (Bus.env0 m0 160) (after b1 (after b0 entryS)) st1.data := by
      rw [after_eq run_b1]; exact hm1
    obtain ⟨hfr1, hts1⟩ := hpro hm1' (by rw [after_eq run_b1, after_eq run_b0])
      (by rw [after_eq run_b1]) (by rw [after_eq run_b1]; decide +kernel)
    have hn : 0 < nP m0 := Nat.pos_of_ne_zero fun h ↦ h0 (UInt64.toNat_inj.mp (by simpa using h))
    refine Eventually.done _ (Or.inr ⟨hpc1, hfr1, hn, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · exact UInt64.toBitVec_inj.mp ((hm1.regs .X19 _ rfl).trans rfl)
    · rw [hm1.regs .X20 _ rfl]; simp [Sym.eval, Bus.env0]; rfl
    · exact UInt64.toBitVec_inj.mp ((hm1.regs .X21 _ rfl).trans rfl)
    · exact UInt64.toBitVec_inj.mp ((hm1.regs .X22 _ rfl).trans rfl)
    · rw [hm1.regs .X23 _ rfl]
      simp only [Sym.eval, BinOp.apply, UnOp.apply, Sym.low_W64, Sym.ext_W64]
      show m0.regs.X5.toBitVec + m0.regs.X6.toBitVec <<< 4 = _
      rw [shl4]
      rfl
    · have hx2' : st1.data.regs.X2 = m0.regs.X2 :=
        UInt64.toBitVec_inj.mp ((hm1.regs .X2 _ rfl).trans rfl)
      have hx3' : st1.data.regs.X3 = m0.regs.X3 :=
        UInt64.toBitVec_inj.mp ((hm1.regs .X3 _ rfl).trans rfl)
      rw [hx2', hx3']
      exact rounds_zero hts1

end

end NativeRustcVmArm.Sumcheck.Plain
