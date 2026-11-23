module

public import NativeRustcVmArm.Code.Vm.CommitStack.Names
public import NativeRustcVmArm.Code.Vm.Ladder.Names
public import NativeRustcVmArm.Code.Vm.TStateReadCommitment.Names
public import NativeRustcVmArm.Layout.CommitStack.Exec
public import NativeRustcVmArm.Layout.Ladder.Table
public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Transcript.Callee
public import NativeRustcVm.Transcript.Update
public import NativeRustcVmArm.Sumcheck.Common

/-!
# `commit_stack`

`b0` saves X30, X20, X19 and calls `ladder` on the frame. Outside the window the ladder is `None`:
`b1` branches to `b3`, which returns `0` (`commitStack` rejects, `run_none`). Inside, `b2` checks the
level count, and `b4` reads level `0`'s fold (`6`) and rate (`r`), restores the registers and
tail-calls `read_commitment` with the shape `(μ - 6 + r, 64)` (`run_some`).
-/

namespace NativeRustcVmArm.Layout.CommitStack

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.CommitStack
open NativeRustcVmArm.Transcript NativeRustcVm.Transcript NativeVm.Model LeanVM.Parameters
open NativeRustcVmArm.Layout.Ladder (nOf ladderW ladder_eq ladder_none admissible_iff nOf_le
  foldAt qAt)

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 192 := by decide

theorem stack_eq : commitStackStack = 624 := rfl

/-- `commitStack` in the window: the root at level `0`'s shape. -/
theorem run_some {μ r : Nat} (h : Whir.Admissible μ r) (s : TState) :
    (commitStack μ r).run s = (readCommitment (μ - 6 + r) 64).run s := by
  have hn := nOf_le μ
  obtain ⟨n, hn'⟩ : ∃ n, nOf μ = n + 1 := ⟨nOf μ - 1, by omega⟩
  simp only [commitStack, ladder_eq h, ladderW, hn', List.range_succ_eq_map, List.map_cons,
    liftOpt, pure_bind, levelShape, foldAt, ↓reduceIte]
  rfl

/-- `commitStack` outside the window: rejected. -/
theorem run_none {μ r : Nat} (h : ¬Whir.Admissible μ r) (s : TState) :
    (commitStack μ r).run s = none := by
  simp only [commitStack, ladder_none h, liftOpt, StateT.run_bind]
  rfl

/-- `ladder`'s count check in `b2`: the count is `1` to `6`. -/
theorem count_ok (n : Nat) (h1 : 1 ≤ n) (h6 : n ≤ 6) :
    CmpOp.apply .addC .W64 (BinOp.apply .sub .W64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 7))
      (BitVec.ofNat 64 6) = true := by
  interval_cases n <;> decide

/-- `b4`'s height: `μ - 6`, saturating, plus `r`. -/
theorem height_eq (μ r : Nat) (hμ : μ < 2 ^ 32) (hr : r < 2 ^ 32) :
    (BinOp.apply .add .W64 (if (BitVec.ofNat 64 μ).ult (BitVec.ofNat 64 6) then BitVec.ofNat 64 0
      else BinOp.apply .sub .W64 (BitVec.ofNat 64 μ) (BitVec.ofNat 64 6)) (BitVec.ofNat 64 r)).toNat =
      μ - 6 + r := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.ult]
  split
  · rename_i h
    simp only [BitVec.toNat_ofNat, decide_eq_true_eq] at h
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rename_i h
    simp only [BitVec.toNat_ofNat, decide_eq_true_eq] at h
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega

variable [Host] {k : Nat}

/-- **`commit_stack`'s contract.** -/
theorem commitStack_spec (hp : Placed code k)
    (hlad : Spec (Labels.label NativeRustcVmArm.Vm.Ladder.entryLabel) LadderPre LadderPost)
    (hrc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadCommitment.entryLabel) (ReadCommitmentPre a s)
      (ReadCommitmentPost a s))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmArm.Vm.CommitStack.entryLabel) (CommitStackPre a s) (CommitStackPost a s) := by
  intro m0 ⟨hst, hrcA, hro, hts, htok, hroots⟩
  rw [stack_eq] at hst hrcA hro htok
  set t := m0.regs.X0.toBitVec with ht
  set fb := frameBase m0 192 with hfb
  have hn : 624 ≤ m0.regs.SP.toNat := hst.2.1
  have hlt := m0.regs.SP.toNat_lt
  have hfbN : fb.toNat = m0.regs.SP.toNat - 192 := frameBase_toNat hn (by decide)
  have hsbN : (stackBelow m0 624).toNat = m0.regs.SP.toNat - 624 := toNat_stackBelow hn
  have hfnw : NativeRustcVm.NoWrap fb 192 := by unfold NativeRustcVm.NoWrap; omega
  have hsnw : NativeRustcVm.NoWrap (stackBelow m0 624) 624 := by
    unfold NativeRustcVm.NoWrap; omega
  have hfm : Mapped m0.dmem fb 192 := frame_mapped hst (by decide)
  -- Frame bytes are stack bytes, apart from the `TState`, its area, the constants, the data.
  have hfs : ∀ q, NativeRustcVm.InRange fb 192 q →
      NativeRustcVm.InRange (stackBelow m0 624) 624 q :=
    fun q h ↦ inRange_frame_stack hn (by decide) h
  have hTn := hts.footprint.1.2
  have hAn := hts.footprint.2.1.2
  have hfT : ∀ q, NativeRustcVm.InRange fb 192 q →
      ¬NativeRustcVm.InRange t tstateBytes q ∧ ¬NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q h ↦ ⟨NativeRustcVm.Apart.not_inRange (apart_frame htok.1 hn (by decide)).symm hfnw hTn h,
      NativeRustcVm.Apart.not_inRange (apart_frame htok.2.1 hn (by decide)).symm hfnw hAn h⟩
  -- The prologue and the call of `ladder`.
  let env0 := frameEnv m0 m0 192 []
  have hwf0 : env0.WF := Env.wf_of ⟨⟨hfm, hfnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (show _ = fb + BitVec.ofInt 64 ((192 : Nat) : Int) from frameBase_add.symm)
      trivial trivial trivial trivial
  rw [show Labels.label NativeRustcVmArm.Vm.CommitStack.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.CommitStack.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.CommitStack.entryOffset) NativeRustcVmArm.Vm.CommitStack.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st0 hm1 hpc1 ↦ ?_
  obtain ⟨okp, okw, ok0, ok1, ok2, ok19, ok20⟩ := ok_b0
  rw [← after_eq run_b0] at hm1
  have hf0 : Frame m0 192 slots st0.data := Frame.of_prologue hwf0 hm1 okp slots_le
  have hso0 : NativeRustcVm.SameOutside m0.dmem st0.data.dmem (NativeRustcVm.InRange fb 192) :=
    NativeRustcVm.SameOutside.mono (Layout.Match.sameOutside_regions hm1 hwf0 (by decide))
      fun q ⟨e, he, h⟩ ↦ by obtain rfl := List.mem_singleton.mp he; exact h
  have hX0 : st0.data.regs.X0.toBitVec = fb := (hm1.regs .X0 _ ok0).trans (eval_ptr00 _ rfl)
  have hX1 : st0.data.regs.X1 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X1 _ ok1)
  have hX2 : st0.data.regs.X2 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X2 _ ok2)
  have hX19 : st0.data.regs.getXReg .X19 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ ok19)
  have hX20 : st0.data.regs.getXReg .X20 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X20 _ ok20)
  have hsp0 : st0.data.regs.SP.toNat = m0.regs.SP.toNat - 192 := by
    rw [← UInt64.toNat_toBitVec, hf0.sp, hfbN]
  have hpre : LadderPre st0.data := by
    refine ⟨?_, ?_, ?_⟩
    · refine RodataAt.mono hro (hso0.mono fun q h ↦ hfs q h) hsnw ?_ ?_
      · rw [show ladderStack = 0 from rfl, toNat_stackBelow (m := st0.data) (n := 0) (by omega), hsbN]
        omega
      · rw [show ladderStack = 0 from rfl, toNat_stackBelow (m := st0.data) (n := 0) (by omega), hsbN]
        omega
    · show Mapped _ st0.data.regs.X0.toBitVec 160 ∧ NativeRustcVm.NoWrap _ 160
      rw [hX0]
      exact ⟨fun i hi ↦ hf0.kept _ (hfm i (by omega)), by unfold NativeRustcVm.NoWrap; omega⟩
    · intro it
      show NativeRustcVm.Apart st0.data.regs.X0.toBitVec 160 _ _
      rw [hX0]
      have h := (hro.apart it).symm
      unfold NativeRustcVm.Apart at h ⊢
      rw [hsbN] at h
      omega
  refine call_then hpc1 hlad hpre fun st1 hpc2 ⟨hL, hch, hsv⟩ ↦ ?_
  rw [hX0, hX1, hX2] at hL
  have hch' : NativeRustcVm.SameOutside st0.data.dmem st1.data.dmem (NativeRustcVm.InRange fb 160) :=
    fun q hq ↦ hch q fun h ↦ h.elim (fun h' ↦ hq (by rw [hX0] at h'; exact h'))
      fun h' ↦ absurd h' (Nat.not_lt_zero _)
  have hf1 : Frame m0 192 slots st1.data := by
    refine Frame.call_slots hf0 hsv hch' fun p hp i hi h ↦ ?_
    refine not_slot_out (o := 0) (n := 160) hfnw (by decide) slots_le (by decide) p hp i hi ?_
    rw [show off (frameBase m0 192) 0 = fb from NativeRustcVm.addr_add_zero _]
    exact h
  have hso1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange fb 192) :=
    (hso0.trans hch').mono fun q h ↦ h.elim id fun h' ↦ by
      unfold NativeRustcVm.InRange at h' ⊢; omega
  have hY19 : st1.data.regs.getXReg .X19 = m0.regs.X0 := (hsv.1 .X19 rfl).trans hX19
  have hY20 : st1.data.regs.getXReg .X20 = m0.regs.X1 := (hsv.1 .X20 rfl).trans hX20
  -- From the return.
  let env1 := frameEnv m0 st1.data 192 []
  have hwf1 : env1.WF := Env.wf_of ⟨⟨fun i hi ↦ hf1.kept _ (hfm i hi), hfnw⟩, trivial⟩
    (List.pairwise_singleton _ _)
  have hm2 : Match env1 retS st1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      ((congrArg id hf1.sp).trans (eval_ptr00 _ rfl).symm) trivial trivial trivial trivial
  have hpc2' : st1.pc = Host.addrOf (k + NativeRustcVmArm.Vm.CommitStack.b1Offset) := hpc2
  have hd1 : env1.mem0 = st1.data.dmem := rfl
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1 hpc2' hm2
    fun st2 hm3 hpc3 ↦ ?_
  obtain ⟨okm1, okmem1, okr1⟩ := ok_b1
  rw [← after_eq run_b1] at hm3
  have hd2 : st2.data.dmem = st1.data.dmem := hm3.dmem_eq hwf1 okmem1
  have hf2 : Frame m0 192 slots st2.data := Frame.of_block hf1 hwf1 hm3 okm1 slots_le
  have hst4 : ∀ {st4 : MachineData}, Saved m0 st4 → st4.dmem = st1.data.dmem →
      StackOk st4 624 ∧ st4.regs.SP = m0.regs.SP := fun {st4} hs hd ↦ by
    refine ⟨⟨by rw [hs.2.1]; exact hst.1, by rw [hs.2.1]; exact hst.2.1, fun i hi ↦ ?_⟩, hs.2.1⟩
    rw [show st4.regs.SP = m0.regs.SP from hs.2.1]
    exact hs.2.2 _ (hst.2.2 i hi)
  -- The final memory: the frame changed.
  have hout : ∀ {d : Mem 64}, NativeRustcVm.SameOutside st1.data.dmem d (fun _ ↦ False) →
      NativeRustcVm.SameOutside m0.dmem d (fun q ↦ NativeRustcVm.InRange t tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow m0 commitStackStack) commitStackStack q) :=
    fun hd ↦ (hso1.trans hd).mono fun q h ↦ h.elim (fun h' ↦ .inr (by rw [stack_eq]; exact hfs q h'))
      False.elim
  simp only [PcOk] at hpc3
  have hdone : ∀ {st5 : MachineData}, Saved m0 st5 → st5.dmem = st1.data.dmem →
      st5.regs.X30 = m0.regs.X30 → retOf st5 = retOf m0 ∧ NativeRustcVm.SameOutside m0.dmem
        st5.dmem (fun q ↦ NativeRustcVm.InRange t tstateBytes q ∨
          NativeRustcVm.InRange (stackBelow m0 commitStackStack) commitStackStack q) :=
    fun _ hd h30 ↦ ⟨by simp only [retOf, h30], by rw [hd]; exact hout fun _ _ ↦ rfl⟩
  by_cases hadm : Whir.Admissible m0.regs.X1.toNat m0.regs.X2.toNat
  · -- Inside the window: the count, level `0`, the tail call.
    have hb := admissible_iff.mp hadm
    rw [ladder_eq hadm] at hL
    obtain ⟨htag, -, hcnt, hlev⟩ := hL
    have hl0 : env1.load 0 0 8 = (1 : UInt64).toBitVec :=
      Layout.load_word (by rw [NativeRustcVm.addr_add_zero]; exact htag)
    simp only [SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, hl0] at hpc3
    simp only [show ((1 : UInt64).toBitVec == BitVec.ofNat 64 0) = false by decide,
      Bool.false_eq_true, ↓reduceIte] at hpc3
    rw [NativeRustcVmArm.Vm.CommitStack.b1_length, NativeRustcVmArm.Vm.CommitStack.b1Length] at hpc3
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) (exec_after run_b1 run_b2) hwf1 hpc3 hm3
      fun st3 hm4 hpc4 ↦ ?_
    rw [← after_eq (exec_after run_b1 run_b2)] at hm4
    have hn3 := nOf_le m0.regs.X1.toNat
    have hlen : (ladderW m0.regs.X1.toNat m0.regs.X2.toNat).length = nOf m0.regs.X1.toNat :=
      Ladder.length_ladderW _ _
    rw [hlen] at hcnt
    have hlc : env1.load 0 152 8 = BitVec.ofNat 64 (nOf m0.regs.X1.toNat) := Layout.load_word hcnt
    simp only [PcOk, SBool.eval, Sym.eval, hlc, count_ok _ (by omega) hn3.2, ↓reduceIte] at hpc4
    rw [hp.label (j := NativeRustcVmArm.Vm.CommitStack.b4Offset) NativeRustcVmArm.Vm.CommitStack.label_3_at] at hpc4
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp)
      (exec_after (exec_after run_b1 run_b2) run_b4) hwf1 hpc4 hm4 fun st5 hm5 hpc5 ↦ ?_
    obtain ⟨oke, okmem, okx0, okx1, okx2⟩ := ok_b4
    rw [← after_eq (exec_after (exec_after run_b1 run_b2) run_b4)] at hm5
    obtain ⟨hs5, hsl5⟩ := Frame.epilogue hf1 hwf1 hm5 oke
    have hd5 : st5.data.dmem = st1.data.dmem := hm5.dmem_eq hwf1 okmem
    have h30 : st5.data.regs.X30 = m0.regs.X30 := hsl5 (160, .X30) (by simp [slots])
    simp only [PcOk] at hpc5
    -- Level `0`: fold `6`, rate `r`.
    have hz : 0 < (ladderW m0.regs.X1.toNat m0.regs.X2.toNat).length := by rw [hlen]; omega
    obtain ⟨-, -, -, hw⟩ := hlev 0 hz
    have hl0' : (ladderW m0.regs.X1.toNat m0.regs.X2.toNat)[0] =
        ⟨6, m0.regs.X2.toNat, qAt m0.regs.X1.toNat m0.regs.X2.toNat 0⟩ := by
      simp [ladderW, foldAt]
    rw [hl0'] at hw
    rw [NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.wordsAt_cons_iff] at hw
    obtain ⟨hwf, hwr, -⟩ := hw
    have e8 : off (off fb 8) (NativeRustcVm.Whir.levelBytes * 0) = fb + BitVec.ofNat 64 8 := by
      rw [Nat.mul_zero]; exact NativeRustcVm.addr_add_zero _
    rw [e8] at hwf hwr
    rw [NativeRustcVm.addr_add_add] at hwr
    have hlf : env1.load 0 8 8 = BitVec.ofNat 64 6 :=
      Layout.load_word (env := env1) (r := 0) (off := 8) (v := (6 : Nat).toUInt64) hwf
    have hlr : env1.load 0 16 8 = BitVec.ofNat 64 m0.regs.X2.toNat :=
      Layout.load_word (env := env1) (r := 0) (off := 16) (v := m0.regs.X2.toNat.toUInt64) hwr
    have hy0 : st5.data.regs.X0 = m0.regs.X0 := by
      apply UInt64.toBitVec_inj.mp
      rw [show st5.data.regs.X0 = st5.data.regs.getXReg .X0 from rfl, hm5.regs _ _ okx0]
      exact congrArg UInt64.toBitVec hY19
    have hy1 : st5.data.regs.X1.toNat = m0.regs.X1.toNat - 6 + m0.regs.X2.toNat := by
      show (st5.data.regs.getXReg .X1).toBitVec.toNat = _
      rw [hm5.regs _ _ okx1]
      simp only [Sym.eval, SBool.eval, CmpOp.apply, Sym.low_W64, hlf, hlr]
      rw [show env1.regs .X20 = BitVec.ofNat 64 m0.regs.X1.toNat by
        show (st1.data.regs.getXReg .X20).toBitVec = _
        rw [hY20]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt m0.regs.X1.toNat_lt]
        rfl]
      exact height_eq _ _ (by omega) (by omega)
    have hy2 : st5.data.regs.X2.toNat = 64 := by
      show (st5.data.regs.getXReg .X2).toBitVec.toNat = _
      rw [hm5.regs _ _ okx2]
      simp only [Sym.eval, hlf]
      decide
    -- `read_commitment`'s precondition.
    obtain ⟨hst5, hsp5⟩ := hst4 hs5 hd5
    have hsb5 : stackBelow st5.data 624 = stackBelow m0 624 := by unfold stackBelow; rw [hsp5]
    have hso5 : NativeRustcVm.SameOutside m0.dmem st5.data.dmem (NativeRustcVm.InRange fb 192) := by
      rw [hd5]; exact hso1
    have hpre5 : ReadCommitmentPre a s st5.data := by
      show StackOk _ _ ∧ RcAt _ _ ∧ TStateAt _ st5.data.regs.X0.toBitVec a s ∧
        TStateOk _ st5.data.regs.X0.toBitVec a _ ∧ _
      rw [hy0, show readCommitmentStack = 624 from rfl]
      refine ⟨hst5, ?_, TStateAt.frame hts hs5.2.2 hfT hso5, ?_, hroots⟩
      · refine Sumcheck.RcAt.sub hrcA (f := 0) (by rw [hsp5]; simp) (by omega) hn fun q hq ↦ ?_
        exact hso5 q fun hf ↦ NativeRustcVm.Apart.not_inRange hrcA.2.2 hrcA.2.1 hsnw hq (hfs q hf)
      · unfold TStateOk; rw [hsb5]; exact htok
    refine Eventually.mono (Spec.apply (hrc a s) hpc5 hpre5) fun st6 ⟨hpc6, hok, hnext, hso6, hsv6⟩ ↦
      ⟨?_, ?_, ?_, ?_, hs5.trans hsv6⟩
    · rw [hpc6]; simp only [retOf, h30]
    · rw [hok, hy1, hy2, run_some hadm]
    · rw [← hy0]; rw [hy1, hy2, ← run_some hadm] at hnext; exact hnext
    · intro q hq
      rw [hso6 q fun h ↦ hq (h.elim (fun h' ↦ .inl (by rw [hy0] at h'; exact h'))
        fun h' ↦ .inr (by rw [stack_eq, ← hsb5]; exact h'))]
      exact (hdone hs5 hd5 h30).2 q hq
  · -- Outside the window: `None`, `b3` returns `0`.
    rw [ladder_none hadm] at hL
    have hl0 : env1.load 0 0 8 = (0 : UInt64).toBitVec :=
      Layout.load_word (by rw [NativeRustcVm.addr_add_zero]; exact hL)
    simp only [SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, hl0] at hpc3
    simp only [show ((0 : UInt64).toBitVec == BitVec.ofNat 64 0) = true by decide,
      ↓reduceIte] at hpc3
    rw [hp.label (j := NativeRustcVmArm.Vm.CommitStack.b3Offset) NativeRustcVmArm.Vm.CommitStack.label_2_at] at hpc3
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) (exec_after run_b1 run_b3) hwf1 hpc3 hm3
      fun st5 hm5 hpc5 ↦ ?_
    obtain ⟨oke, okmem, okx0⟩ := ok_b3
    rw [← after_eq (exec_after run_b1 run_b3)] at hm5
    obtain ⟨hs5, hsl5⟩ := Frame.epilogue hf1 hwf1 hm5 oke
    have hd5 : st5.data.dmem = st1.data.dmem := hm5.dmem_eq hwf1 okmem
    have h30 : st5.data.regs.X30 = m0.regs.X30 := hsl5 (160, .X30) (by simp [slots])
    obtain ⟨hret, hso⟩ := hdone hs5 hd5 h30
    simp only [PcOk] at hpc5
    refine .done _ ⟨hpc5.trans hret, ?_, ?_, hso, hs5⟩
    · rw [run_none hadm]
      exact UInt64.toBitVec_inj.mp (hm5.regs .X0 _ okx0)
    · rw [run_none hadm]; intro _ _ h; cases h

end

end NativeRustcVmArm.Layout.CommitStack
