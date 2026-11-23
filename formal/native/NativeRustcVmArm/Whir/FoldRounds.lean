module

public import NativeRustcVmArm.Code.Vm.FoldRound.Names
public import NativeRustcVmArm.Code.Vm.FoldRounds.Names
public import NativeRustcVmArm.Whir.FoldRounds.Round

/-!
# `fold_rounds` on AArch64

**`foldRounds_spec`**: X0 becomes `foldRounds n`'s `Some`/`None`, the state at X2, the rounds'
buffer at X3 and the `TState` at X0 its values, given `fold_round`'s contract. `b0` zeroes the
buffer's count and returns `1` for `n = 0` (`b9`). Otherwise `b1` saves X30, X23 to X19 and calls
`fold_round`; rustc unrolled the (at most `6`) rounds, each a call, its tag tested and its `α`, `β`
stored (`round`, `step`), then compared with `n`: equal, `b7`, `b8` return `1`; a rejected round
returns `0` (`b23`).
-/

namespace NativeRustcVmArm.Whir.FoldRounds

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FoldRounds NativeRustcVmArm.Transcript
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm NativeRustcVm.Whir NativeRustcVmArm.Whir

public section

theorem beq_ofNat {x : UInt64} {j : Nat} (hj : j < 2 ^ 64) :
    (x.toBitVec == BitVec.ofNat 64 j) = decide (x.toNat = j) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  have e : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hj
  constructor
  · intro h; have := congrArg BitVec.toNat h; rw [e] at this; exact this
  · intro h; apply BitVec.eq_of_toNat_eq; rw [e]; exact h

variable [Host] {k : Nat}

omit [Host] in
/-- The rounds done: `1`. -/
theorem goal_of_inv [Labels] {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData}
    {d d' : MachineData} (hI : Inv m0 a s w m0.regs.X1.toNat d) (hx0 : d'.regs.X0 = 1)
    (hd : d'.dmem = d.dmem) (hsv : Saved m0 d') : FoldRoundsPost a s w m0 d' := by
  obtain ⟨-, -, -, -, -, -, ⟨w1, rs, s1, hrun, -, -, hws, hbr, hts⟩, hsame⟩ := hI
  refine ⟨by rw [hrun, hx0]; rfl, fun w' rs' s' h ↦ ?_, fun q hq ↦ by rw [hd]; exact hsame q hq,
    hsv⟩
  rw [hrun] at h
  cases h
  exact ⟨hd ▸ hws, hd ▸ hbr, hd ▸ hts⟩

/-- **A round after the first**: its call block (`C`), then `round`. -/
theorem step (hp : Placed code k)
    (hfr : ∀ a s w, Spec (Labels.label NativeRustcVmArm.Vm.FoldRound.entryLabel) (FoldRoundPre a s w) (FoldRoundPost a s w))
    {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData} (hpre : FoldRoundsPre a s w m0)
    {C T S : List Directive} {kc i : Nat} {SC ST SS : SState} {cT : SBool} {xS : Exit}
    (hC : C.IsInfixAt code kc) (hCne : C ≠ [])
    (hrunC : exec C callS = some (SC, .call NativeRustcVmArm.Vm.FoldRound.entryLabel))
    (hokC : CallOk SC)
    (hT : T.IsInfixAt code (kc + C.length)) (hTne : T ≠ [])
    (hrunT : exec T tagS = some (ST, .cond cT NativeRustcVmArm.Vm.FoldRounds.label_17)) (hokT : TagOk ST)
    (hc0 : ∀ d : MachineData, NativeRustcVm.WordAt d.dmem (off (frameBase m0 160) 40) 0 →
      cT.eval (frameEnv m0 d 160 []) = true)
    (hc1 : ∀ d : MachineData, NativeRustcVm.WordAt d.dmem (off (frameBase m0 160) 40) 1 →
      cT.eval (frameEnv m0 d 160 []) = false)
    (hS : S.IsInfixAt code (kc + C.length + T.length)) (hSne : S ≠ [])
    (hrunS : exec S storeS = some (SS, xS)) (hokS : StoreOk (i + 1) SS)
    (hi : i < m0.regs.X1.toNat) {st : MachineState} (hpc : st.pc = Host.addrOf (k + kc))
    (hI : Inv m0 a s w i st.data)
    (cont : ∀ st' : MachineState, Inv m0 a s w (i + 1) st'.data →
      (∃ env : Env, env.regs .X22 = m0.regs.X1.toBitVec ∧
        PcOk env xS (Host.addrOf (k + (kc + C.length + T.length) + S.length)) st' ∧
        ∀ v, SS.reg .X0 = some v → st'.data.regs.X0.toBitVec = v.eval env) →
      Eventually (step1 Host.exe) (Goal a s w m0) st') :
    Eventually (step1 Host.exe) (Goal a s w m0) st := by
  have hst : StackOk m0 foldRoundsStack := hpre.1.1
  have hfnw := frame_noWrap (m := m0) (F := 160) (by have := hst.2.1; rw [stack_eq] at this; omega)
  have hwf : (frameEnv m0 st.data 160 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 160) hst (by decide)) hI.frame.kept, hfnw⟩,
      trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 160 []) callS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hI.frame.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of hC hCne hp) hrunC hwf hpc hm fun st1 hm1 hpc1 => ?_
  obtain ⟨hmid, hmem, c0, c1, c2, c19, c20, c21, c22, c23⟩ := hokC
  have hf1 : Frame m0 160 slots st1.data := Frame.of_block hI.frame hwf hm1 hmid slots_le
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem
  have e19 : st1.data.regs.X19 = st.data.regs.X19 := Match.reg_eq hm hm1 rfl c19
  have e20 : st1.data.regs.X20 = st.data.regs.X20 := Match.reg_eq hm hm1 rfl c20
  have e21 : st1.data.regs.X21 = st.data.regs.X21 := Match.reg_eq hm hm1 rfl c21
  have e22 : st1.data.regs.X22 = st.data.regs.X22 := Match.reg_eq hm hm1 rfl c22
  have e23 : st1.data.regs.X23 = st.data.regs.X23 := Match.reg_eq hm hm1 rfl c23
  obtain ⟨-, h19, h20, h21, h22, h23, hrun, hsame⟩ := hI
  refine round hp hfr hpre hT hTne hrunT hokT hc0 hc1 hS hSne hrunS hokS hi
    ⟨hpc1.1, hpc1.2.trans (by rw [Nat.add_assoc])⟩
    ⟨hf1, by rw [e19]; exact h19, by rw [e20]; exact h20, by rw [e21]; exact h21,
      by rw [e22]; exact h22, by rw [e23]; exact h23, by rw [hd1]; exact hrun,
      by intro q hq; rw [hd1]; exact hsame q hq⟩
    (by show (st1.data.regs.getXReg .X0).toBitVec = _; rw [hm1.regs .X0 _ c0]; rfl)
    (by show (st1.data.regs.getXReg .X1).toBitVec = _; rw [hm1.regs .X1 _ c1]; exact h20)
    (by show (st1.data.regs.getXReg .X2).toBitVec = _; rw [hm1.regs .X2 _ c2]; exact h19) cont


/-- How a round's store block ends: `n` against the rounds done. -/
theorem exit_eq {env : Env} {m0 : MachineData} {j : Nat} (hj : j < 2 ^ 64)
    (hx : env.regs .X22 = m0.regs.X1.toBitVec) :
    (SBool.cmp .eq .W64 (.reg .X22) (.lit j)).eval env = decide (m0.regs.X1.toNat = j) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, hx]
  exact beq_ofNat hj

theorem exit_ne {env : Env} {m0 : MachineData} {j : Nat} (hj : j < 2 ^ 64)
    (hx : env.regs .X22 = m0.regs.X1.toBitVec) :
    (SBool.cmp .eq .W64 (.reg .X22) (.lit j)).not.eval env = !decide (m0.regs.X1.toNat = j) := by
  rw [SBool.eval, exit_eq hj hx]

theorem tag_bit0 {m0 d : MachineData} (h : NativeRustcVm.WordAt d.dmem (off (frameBase m0 160) 40) 0) :
    (SBool.bit .W32 (.load 0 40 4) 0).not.eval (frameEnv m0 d 160 []) = true := by
  simp only [SBool.eval, Sym.eval]
  rw [load4_of_tag (Or.inl rfl) h]; rfl

theorem tag_bit1 {m0 d : MachineData} (h : NativeRustcVm.WordAt d.dmem (off (frameBase m0 160) 40) 1) :
    (SBool.bit .W32 (.load 0 40 4) 0).not.eval (frameEnv m0 d 160 []) = false := by
  simp only [SBool.eval, Sym.eval]
  rw [load4_of_tag (Or.inr rfl) h]; rfl

theorem tag_eq0 {m0 d : MachineData} (h : NativeRustcVm.WordAt d.dmem (off (frameBase m0 160) 40) 0) :
    (SBool.cmp .eq .W64 (.load 0 40 8) (.lit 0)).eval (frameEnv m0 d 160 []) = true := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64]
  rw [load_of_wordAt h]; rfl

theorem tag_eq1 {m0 d : MachineData} (h : NativeRustcVm.WordAt d.dmem (off (frameBase m0 160) 40) 1) :
    (SBool.cmp .eq .W64 (.load 0 40 8) (.lit 0)).eval (frameEnv m0 d 160 []) = false := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64]
  rw [load_of_wordAt h]; rfl

/-- The last round done, at `b7`. -/
theorem fin7 (hp : Placed code k) {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData}
    (hst : StackOk m0 foldRoundsStack) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRounds.b7Offset))
    (hI : Inv m0 a s w m0.regs.X1.toNat st.data) :
    Eventually (step1 Host.exe) (Goal a s w m0) st :=
  Eventually.mono (done7 hp hst hpc hI.frame) fun _ ⟨h1, h2, h3, h4⟩ ↦
    ⟨h1, goal_of_inv hI h2 h3 h4⟩

/-- **`fold_rounds` meets its contract.** -/
theorem foldRounds_spec (hp : Placed code k)
    (hfr : ∀ a s w, Spec (Labels.label NativeRustcVmArm.Vm.FoldRound.entryLabel) (FoldRoundPre a s w) (FoldRoundPost a s w))
    (a : DecArea) (s : TState) (w : WhirStateW) :
    Spec (Labels.label NativeRustcVmArm.Vm.FoldRounds.entryLabel) (FoldRoundsPre a s w) (FoldRoundsPost a s w) := by
  intro m0 hpre
  have hpre' := hpre
  obtain ⟨⟨hst, hrc, hrod, htok, hrt⟩, hts, hws, hn6, hal, ⟨hpo, hpr⟩, ⟨hro, hrr⟩, hrp⟩ := hpre'
  have g := geo hpre
  set t := m0.regs.X0.toBitVec with htdef
  set p := m0.regs.X2.toBitVec with hpdef
  set r := m0.regs.X3.toBitVec with hrdef
  set n := m0.regs.X1.toNat with hndef
  set fb := frameBase m0 160 with hfbdef
  have hn : 960 ≤ m0.regs.SP.toNat := hst.2.1
  have hlt := m0.regs.SP.toNat_lt
  have hfnw : fb.toNat + 160 ≤ 2 ^ 64 := frame_noWrap (m := m0) (F := 160) (by omega)
  have hfb : fb.toNat = m0.regs.SP.toNat - 160 := frameBase_toNat (n := 960) hn (by decide)
  have hTn : t.toNat + 760 ≤ 2 ^ 64 := hts.footprint.1.2
  have hAn : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hts.footprint.2.1.2
  have hpn : p.toNat + 61152 ≤ 2 ^ 64 := hpo.2.1
  have hrn : r.toNat + 200 ≤ 2 ^ 64 := hro.2.1
  have hr8 : r.toNat + 8 ≤ 2 ^ 64 := by omega
  -- `b0`: the count zeroed; `n = 0`?
  have hwf0 : (Env.ofMachine m0 [(r, 8)]).WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hro.1 i (by simp [roundBytes, roundCap]; omega), hr8⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm0 : Match (Env.ofMachine m0 [(r, 8)]) entryS m0 :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨known_ptr rfl rfl, trivial⟩ trivial trivial trivial
  unfold NativeRustcVmArm.Vm.FoldRounds.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.FoldRounds.entryOffset) NativeRustcVmArm.Vm.FoldRounds.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 => ?_
  obtain ⟨hk1, hw1, hws1⟩ := after_eq run_b0 ▸ ok_b0
  have hsv1 : Saved m0 st1.data := Match.saved hm0 hm1 hwf0 rfl hk1
  have hs1 : SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange r 8) :=
    sameOutside_region hwf0 hm1 rfl hws1
  have hc1 := wordAt_write hm1 (r := 0) (o := 0) (b := r) (sz := 8) rfl le_rfl hw1
  rw [off_zero, show UInt64.ofBitVec ((Sym.lit 0).eval (Env.ofMachine m0 [(r, 8)])) = 0 from rfl]
    at hc1
  have hbr1 : BufRoundsAt st1.data.dmem r ([] : List FoldRoundW) :=
    ⟨by simp [roundCap], hc1, NativeRustcVm.Transcript.ewsAt_nil _ _⟩
  have hR1 : ∀ q, NativeRustcVm.InRange r 8 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q := by
    intro q hq
    have := inR hr8 hq; have := g.aRT; have := g.aRA
    exact ⟨fun h ↦ by have := inR hTn h; omega, fun h ↦ by have := inR hAn h; omega⟩
  have hts1 : TStateAt st1.data.dmem t a s := hts.frame hsv1.2.2 hR1 hs1
  have hws1' : WhirStateAt st1.data.dmem p w :=
    hws.agree (NativeRustcVmArm.Whir.agree_of_sameOutside hs1 fun j hj _ h ↦ by
      have hj' : (off p j).toNat = p.toNat + j := toNat_off (by simp only [stateBytes] at hj; omega)
      generalize off p j = q at h hj'
      have := inR hr8 h; have := g.aRP; simp only [stateBytes] at hj; omega)
  have hso1 : ChangesIn m0 st1.data foldRoundsStack (outs m0) := fun q hq ↦ hs1 q fun h ↦
    hq (Or.inl (outs_iff.mpr (Or.inl (inRange_sub hrn (le_refl _) (by omega) h))))
  have hX0 : st1.data.regs.X0 = m0.regs.X0 := Match.reg_eq (r := .X0) hm0 hm1 rfl rfl
  have hX1 : st1.data.regs.X1 = m0.regs.X1 := Match.reg_eq (r := .X1) hm0 hm1 rfl rfl
  have hX2 : st1.data.regs.X2 = m0.regs.X2 := Match.reg_eq (r := .X2) hm0 hm1 rfl rfl
  have hX3 : st1.data.regs.X3.toBitVec = r := by
    show (st1.data.regs.getXReg .X3).toBitVec = _; rw [hm1.regs .X3 _ rfl]; exact eval_ptr rfl
  have hX30 : st1.data.regs.X30 = m0.regs.X30 := Match.reg_eq (r := .X30) hm0 hm1 rfl rfl
  simp only [PcOk] at hpc1
  split at hpc1
  · -- `n = 0`: `1`.
    rename_i hc
    have hn0 : n = 0 := by
      sym_simp at hc
      simp only [Env.ofMachine_regs, beq_iff_eq] at hc
      exact (congrArg BitVec.toNat hc).trans rfl
    refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 (Env.wf_nil _)
      (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.FoldRounds.b9Offset) NativeRustcVmArm.Vm.FoldRounds.label_7_at)) (match_nil _) fun st2 hm2 hpc2 => ?_
    obtain ⟨hmem2, hk2, h30, hx0⟩ := after_eq run_b9 ▸ ok_b9
    have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq (Env.wf_nil _) hmem2
    have hx30 : st2.data.regs.X30 = m0.regs.X30 :=
      (Match.reg_eq (match_nil _) hm2 rfl h30).trans hX30
    have hrun : (foldRounds n w).run s = some ((w, #[]), s) := by rw [hn0]; rfl
    refine .done _ ⟨by simp only [PcOk] at hpc2; rw [hpc2]; simp only [retOf, hx30], ?_, ?_,
      fun q hq ↦ by rw [hd2]; exact hso1 q hq,
      hsv1.trans (Match.saved (match_nil _) hm2 (Env.wf_nil _) rfl hk2)⟩
    · show st2.data.regs.X0 = okWord ((foldRounds n w).run s).isSome
      rw [hrun]; exact UInt64.toBitVec_inj.mp (hm2.regs .X0 _ hx0)
    · intro w' rs s' h
      rw [hrun] at h
      cases h
      exact ⟨hd2 ▸ hws1', hd2 ▸ hbr1, hd2 ▸ hts1⟩
  rename_i hc
  have hn0 : n ≠ 0 := by
    intro h0; apply hc
    sym_simp
    simp only [Env.ofMachine_regs, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    exact h0
  -- `b1`: the prologue, the first call.
  have hwf1 : (frameEnv m0 st1.data 160 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 160) hst (by decide)) hsv1.2.2, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm1' : Match (frameEnv m0 st1.data 160 []) proS st1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [show st1.data.regs.SP = m0.regs.SP from hsv1.2.1]; exact frameBase_add.symm)
      trivial trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1
    (hpc1.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.FoldRounds.b0Offset + NativeRustcVmArm.Vm.FoldRounds.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRounds.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.FoldRounds.b0_next])) hm1' fun st2 hm2 hpc2 => ?_
  obtain ⟨hpro, hws2, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hx23⟩ := after_eq run_b1 ▸ ok_b1
  have hf2 : Frame m0 160 slots st2.data :=
    Frame.of_prologue_from hsv1 (fun p hp ↦ by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hX30
      all_goals exact hsv1.1 _ rfl) hwf1 hm2 hpro slots_le
  have hs2 : SameOutside st1.data.dmem st2.data.dmem (NativeRustcVm.InRange fb 160) :=
    sameOutside_region hwf1 hm2 rfl hws2
  have hR2 : ∀ q, NativeRustcVm.InRange fb 160 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q := by
    intro q hq
    have := inR hfnw hq; have := g.aTS; have := g.aAS
    exact ⟨fun h ↦ by have := inR hTn h; omega, fun h ↦ by have := inR hAn h; omega⟩
  have hrv : ∀ x : XReg, (st1.data.regs.getXReg x).toBitVec =
      (Sym.reg x).eval (frameEnv m0 st1.data 160 []) := fun _ ↦ rfl
  have hInv : Inv m0 a s w 0 st2.data := by
    refine ⟨hf2, ?_, ?_, ?_, ?_, ?_, ⟨w, #[], s, rfl, rfl, rfl, ?_, ?_, ?_⟩, ?_⟩
    · show (st2.data.regs.getXReg .X19).toBitVec = _
      rw [hm2.regs .X19 _ hx19]; show st1.data.regs.X2.toBitVec = _; rw [hX2]
    · show (st2.data.regs.getXReg .X20).toBitVec = _
      rw [hm2.regs .X20 _ hx20]; show st1.data.regs.X0.toBitVec = _; rw [hX0]
    · show (st2.data.regs.getXReg .X21).toBitVec = _
      rw [hm2.regs .X21 _ hx21]; exact hX3
    · exact UInt64.toBitVec_inj.mp ((hm2.regs .X22 _ hx22).trans (by
        show st1.data.regs.X1.toBitVec = _; rw [hX1]))
    · show (st2.data.regs.getXReg .X23).toBitVec = _
      rw [hm2.regs .X23 _ hx23]; rfl
    · exact hws1'.agree (NativeRustcVmArm.Whir.agree_of_sameOutside hs2 fun j hj _ h ↦ by
        have hj' : (off p j).toNat = p.toNat + j :=
          toNat_off (by simp only [stateBytes] at hj; omega)
        generalize off p j = q at h hj'
        have := inR hfnw h; have := g.aPS; simp only [stateBytes] at hj; omega)
    · exact bufRoundsAt_agree hbr1 (NativeRustcVmArm.Whir.agree_of_sameOutside hs2 fun j hj _ h ↦ by
        have hj' : (off r j).toNat = r.toNat + j := toNat_off (by omega)
        generalize off r j = q at h hj'
        have := inR hfnw h; have := g.aRS; omega)
    · exact hts1.frame (hm2.kept hwf1) hR2 hs2
    · intro q hq
      rw [hs2 q fun h ↦ hq (Or.inr (by rw [stack_eq]; exact inRange_frame_stack hn (by decide) h))]
      exact hso1 q hq
  have hn6' : n ≤ 6 := hn6
  -- Round 1.
  refine round hp hfr hpre b2_in_code (by simp [b2]) run_b2 ok_b2 (fun d h ↦ tag_bit0 h)
    (fun d h ↦ tag_bit1 h) (by rw [NativeRustcVmArm.Vm.FoldRounds.b2_next]; exact b3_in_code) (by simp [b3])
    run_b3 ok_b3 (by omega) ⟨hpc2.1, hpc2.2.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FoldRounds.b1_next])⟩ hInv
    (by show (st2.data.regs.getXReg .X0).toBitVec = _; rw [hm2.regs .X0 _ hx0]; rfl)
    (by show (st2.data.regs.getXReg .X1).toBitVec = _; rw [hm2.regs .X1 _ hx1]
        show st1.data.regs.X0.toBitVec = _; rw [hX0])
    (by show (st2.data.regs.getXReg .X2).toBitVec = _; rw [hm2.regs .X2 _ hx2]
        show st1.data.regs.X2.toBitVec = _; rw [hX2])
    fun st3 hI3 ⟨env3, h22, hpc3, hx03⟩ ↦ ?_
  simp only [PcOk] at hpc3
  rw [exit_eq (by decide) h22] at hpc3
  by_cases e1 : n = 1
  · simp only [show m0.regs.X1.toNat = 1 from e1, decide_true, ↓reduceIte] at hpc3
    have hI' : Inv m0 a s w m0.regs.X1.toNat st3.data := by
      rw [show m0.regs.X1.toNat = 0 + 1 from e1]; exact hI3
    have hx : st3.data.regs.X0 = 1 := UInt64.toBitVec_inj.mp (hx03 _ ok_b3_x0)
    exact Eventually.mono (done hp hst (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.FoldRounds.b8Offset) NativeRustcVmArm.Vm.FoldRounds.label_6_at)) hI3.frame)
      fun _ ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, goal_of_inv hI' (h2.trans hx) h3 h4⟩
  simp only [show ¬ m0.regs.X1.toNat = 1 from e1, decide_false, Bool.false_eq_true, ↓reduceIte]
    at hpc3
  -- Round 2.
  refine step hp hfr hpre (kc := NativeRustcVmArm.Vm.FoldRounds.b4Offset) b4_in_code (by simp [b4]) run_b4 ok_b4
    (by rw [NativeRustcVmArm.Vm.FoldRounds.b4_next]; exact b5_in_code) (by simp [b5]) run_b5 ok_b5
    (fun d h ↦ tag_eq0 h) (fun d h ↦ tag_eq1 h)
    (by rw [NativeRustcVmArm.Vm.FoldRounds.b4_next, NativeRustcVmArm.Vm.FoldRounds.b5_next]; exact b6_in_code)
    (by simp [b6]) run_b6 ok_b6 (by omega) (hpc3.trans (by simp only [NativeRustcVmArm.Vm.FoldRounds.b2_next, NativeRustcVmArm.Vm.FoldRounds.b3_next, Nat.add_assoc]))
    hI3 fun st4 hI4 ⟨env4, h22, hpc4, _⟩ ↦ ?_
  simp only [PcOk] at hpc4
  rw [exit_ne (by decide) h22] at hpc4
  by_cases e2 : n = 2
  · simp only [show m0.regs.X1.toNat = 2 from e2, decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at hpc4
    refine fin7 hp hst (hpc4.trans (by simp only [NativeRustcVmArm.Vm.FoldRounds.b4_next, NativeRustcVmArm.Vm.FoldRounds.b5_next, NativeRustcVmArm.Vm.FoldRounds.b6_next, Nat.add_assoc])) ?_
    rw [show m0.regs.X1.toNat = 1 + 1 from e2]; exact hI4
  simp only [show ¬ m0.regs.X1.toNat = 2 from e2, decide_false, Bool.not_false, ↓reduceIte]
    at hpc4
  -- Round 3.
  refine step hp hfr hpre (kc := NativeRustcVmArm.Vm.FoldRounds.b10Offset) b10_in_code (by simp [b10]) run_b10 ok_b10
    (by rw [NativeRustcVmArm.Vm.FoldRounds.b10_next]; exact b11_in_code) (by simp [b11]) run_b11 ok_b11
    (fun d h ↦ tag_eq0 h) (fun d h ↦ tag_eq1 h)
    (by rw [NativeRustcVmArm.Vm.FoldRounds.b10_next, NativeRustcVmArm.Vm.FoldRounds.b11_next]; exact b12_in_code)
    (by simp [b12]) run_b12 ok_b12 (by omega) (hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.FoldRounds.b10Offset) NativeRustcVmArm.Vm.FoldRounds.label_8_at))
    hI4 fun st5 hI5 ⟨env5, h22, hpc5, _⟩ ↦ ?_
  simp only [PcOk] at hpc5
  rw [exit_eq (by decide) h22] at hpc5
  by_cases e3 : n = 3
  · simp only [show m0.regs.X1.toNat = 3 from e3, decide_true, ↓reduceIte] at hpc5
    refine fin7 hp hst (hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.FoldRounds.b7Offset) NativeRustcVmArm.Vm.FoldRounds.label_5_at)) ?_
    rw [show m0.regs.X1.toNat = 2 + 1 from e3]; exact hI5
  simp only [show ¬ m0.regs.X1.toNat = 3 from e3, decide_false, Bool.false_eq_true, ↓reduceIte]
    at hpc5
  -- Round 4.
  refine step hp hfr hpre (kc := NativeRustcVmArm.Vm.FoldRounds.b13Offset) b13_in_code (by simp [b13]) run_b13 ok_b13
    (by rw [NativeRustcVmArm.Vm.FoldRounds.b13_next]; exact b14_in_code) (by simp [b14]) run_b14 ok_b14
    (fun d h ↦ tag_eq0 h) (fun d h ↦ tag_eq1 h)
    (by rw [NativeRustcVmArm.Vm.FoldRounds.b13_next, NativeRustcVmArm.Vm.FoldRounds.b14_next]; exact b15_in_code)
    (by simp [b15]) run_b15 ok_b15 (by omega)
    (hpc5.trans (by simp only [NativeRustcVmArm.Vm.FoldRounds.b10_next, NativeRustcVmArm.Vm.FoldRounds.b11_next, NativeRustcVmArm.Vm.FoldRounds.b12_next, Nat.add_assoc]))
    hI5 fun st6 hI6 ⟨env6, h22, hpc6, _⟩ ↦ ?_
  simp only [PcOk] at hpc6
  rw [exit_eq (by decide) h22] at hpc6
  by_cases e4 : n = 4
  · simp only [show m0.regs.X1.toNat = 4 from e4, decide_true, ↓reduceIte] at hpc6
    refine fin7 hp hst (hpc6.trans (hp.label (j := NativeRustcVmArm.Vm.FoldRounds.b7Offset) NativeRustcVmArm.Vm.FoldRounds.label_5_at)) ?_
    rw [show m0.regs.X1.toNat = 3 + 1 from e4]; exact hI6
  simp only [show ¬ m0.regs.X1.toNat = 4 from e4, decide_false, Bool.false_eq_true, ↓reduceIte]
    at hpc6
  -- Round 5.
  refine step hp hfr hpre (kc := NativeRustcVmArm.Vm.FoldRounds.b16Offset) b16_in_code (by simp [b16]) run_b16 ok_b16
    (by rw [NativeRustcVmArm.Vm.FoldRounds.b16_next]; exact b17_in_code) (by simp [b17]) run_b17 ok_b17
    (fun d h ↦ tag_eq0 h) (fun d h ↦ tag_eq1 h)
    (by rw [NativeRustcVmArm.Vm.FoldRounds.b16_next, NativeRustcVmArm.Vm.FoldRounds.b17_next]; exact b18_in_code)
    (by simp [b18]) run_b18 ok_b18 (by omega)
    (hpc6.trans (by simp only [NativeRustcVmArm.Vm.FoldRounds.b13_next, NativeRustcVmArm.Vm.FoldRounds.b14_next, NativeRustcVmArm.Vm.FoldRounds.b15_next, Nat.add_assoc]))
    hI6 fun st7 hI7 ⟨env7, h22, hpc7, _⟩ ↦ ?_
  simp only [PcOk] at hpc7
  rw [exit_eq (by decide) h22] at hpc7
  by_cases e5 : n = 5
  · simp only [show m0.regs.X1.toNat = 5 from e5, decide_true, ↓reduceIte] at hpc7
    refine fin7 hp hst (hpc7.trans (hp.label (j := NativeRustcVmArm.Vm.FoldRounds.b7Offset) NativeRustcVmArm.Vm.FoldRounds.label_5_at)) ?_
    rw [show m0.regs.X1.toNat = 4 + 1 from e5]; exact hI7
  simp only [show ¬ m0.regs.X1.toNat = 5 from e5, decide_false, Bool.false_eq_true, ↓reduceIte]
    at hpc7
  -- Round 6.
  refine step hp hfr hpre (kc := NativeRustcVmArm.Vm.FoldRounds.b19Offset) b19_in_code (by simp [b19]) run_b19 ok_b19
    (by rw [NativeRustcVmArm.Vm.FoldRounds.b19_next]; exact b20_in_code) (by simp [b20]) run_b20 ok_b20
    (fun d h ↦ tag_eq0 h) (fun d h ↦ tag_eq1 h)
    (by rw [NativeRustcVmArm.Vm.FoldRounds.b19_next, NativeRustcVmArm.Vm.FoldRounds.b20_next]; exact b21_in_code)
    (by simp [b21]) run_b21 ok_b21 (by omega)
    (hpc7.trans (by simp only [NativeRustcVmArm.Vm.FoldRounds.b16_next, NativeRustcVmArm.Vm.FoldRounds.b17_next, NativeRustcVmArm.Vm.FoldRounds.b18_next, Nat.add_assoc]))
    hI7 fun st8 hI8 ⟨env8, h22, hpc8, _⟩ ↦ ?_
  simp only [PcOk] at hpc8
  rw [exit_eq (by decide) h22] at hpc8
  have e6 : n = 6 := by omega
  simp only [show m0.regs.X1.toNat = 6 from e6, decide_true, ↓reduceIte] at hpc8
  refine fin7 hp hst (hpc8.trans (hp.label (j := NativeRustcVmArm.Vm.FoldRounds.b7Offset) NativeRustcVmArm.Vm.FoldRounds.label_5_at)) ?_
  rw [show m0.regs.X1.toNat = 5 + 1 from e6]; exact hI8

end

end NativeRustcVmArm.Whir.FoldRounds
