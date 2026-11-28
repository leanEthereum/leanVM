module

public import NativeRustcVmX64.Arrays.MultilinearEvalByOfMultilinearEval.Exec
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names

/-!
# `multilinear_eval_by` (`multilinear_eval`'s closure) on x86-64

**`mleOfMultilinearEval_spec`**: rustc's `multilinear_eval_by(n, |i| mle[i], point)`, placed
anywhere in the program, meets `MleOfMultilinearEvalPre`/`MleOfMultilinearEvalPost` given
`EW::mul`'s contract. The prologue (`b0`) pushes RBP, R15, R14, R13, R12, RBX, reserves 1160
bytes, stores `point`; the loop `b1` zeroes the pending entries, `b2` the flags; `n = 0` returns
`0` (`b20`), `|point| = 0` returns `mle[0]` (`b18`, `b19`); otherwise `b4` stores the arguments
and the loops (`MleFrame.loops`: `outer` loads `mle[i]`, `MleFrame.inner_turn` carries it) stream
the entries (`NativeRustcVm.Mle.stream`, `= multilinearEval` by `stream_eq`); the epilogue `b21`
returns the value.
-/

namespace NativeRustcVmX64.Arrays.MleOfMultilinearEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval
  NativeVm.Model NativeRustcVmX64.Field NativeRustcVmX64.Arrays.MleFrame
open NativeRustcVm (wordOf ewOf ewsOf)
open NativeRustcVm.Mle (stream cont setP)

public section

/-- The entries. -/
abbrev ents (m0 : MachineData) : List EW := ewsOf m0.dmem (reg m0 .rsi) (reg m0 .rdx).toNat

theorem pc_len [Host] {s : MachineState} {a b n : Nat} {L : List Directive}
    (h : s.pc = Host.addrOf (a + L.length)) (hL : L.length = n) (e : a + n = b) :
    s.pc = Host.addrOf b := by
  rw [h, hL, e]

/-- The postcondition, from the streamed value. -/
theorem post_of {m0 : MachineData} {s : MachineState}
    (h : s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧
      ewRet s.data = stream (pts m0) (ents m0) (fun _ ↦ none) ∧ Changes m0 s.data mleStack 0 0 ∧
      Saved m0 s.data) :
    s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ MleOfMultilinearEvalPost m0 s.data :=
  ⟨h.1, h.2.1, h.2.2.1.trans (NativeRustcVm.Mle.stream_eq _ _), h.2.2.2⟩

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b9Offset) :=
  b9_in_code.trans hp.1 (by simp [b9])
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b10Offset) :=
  b10_in_code.trans hp.1 (by simp [b10])
theorem hb11 (hp : Placed code k) : s11a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b11Offset) ∧
    s11b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b11Offset + s11a.length) := by
  have h := b11_in_code.trans hp.1 (by simp [b11])
  rw [← List.take_append_drop 9 b11] at h
  exact h.append
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b12Offset) :=
  b12_in_code.trans hp.1 (by simp [b12])
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b13Offset) :=
  b13_in_code.trans hp.1 (by simp [b13])
theorem hb14 (hp : Placed code k) : b14.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b14Offset) :=
  b14_in_code.trans hp.1 (by simp [b14])
theorem hb16 (hp : Placed code k) : b16.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b16Offset) :=
  b16_in_code.trans hp.1 (by simp [b16])
theorem hb17 (hp : Placed code k) : b17.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b17Offset) :=
  b17_in_code.trans hp.1 (by simp [b17])
theorem hb18 (hp : Placed code k) : b18.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b18Offset) :=
  b18_in_code.trans hp.1 (by simp [b18])
theorem hb19 (hp : Placed code k) : b19.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b19Offset) :=
  b19_in_code.trans hp.1 (by simp [b19])
theorem hb20 (hp : Placed code k) : b20.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b20Offset) :=
  b20_in_code.trans hp.1 (by simp [b20])
theorem hb21 (hp : Placed code k) : b21.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b21Offset) :=
  b21_in_code.trans hp.1 (by simp [b21])

theorem lbl_entry (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b0Offset) := hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entry_at
theorem lbl_1 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b1Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_1_at
theorem lbl_3 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b20Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_3_at
theorem lbl_6 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_6 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b5Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_6_at
theorem lbl_9 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_9 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b9Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_9_at
theorem lbl_10 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_10 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b10Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_10_at
theorem lbl_11 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_11 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b16Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_11_at
theorem lbl_13 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_13 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b18Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_13_at
theorem lbl_15 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_15 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b21Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.label_15_at

/-- **The outer loop's set-up** (`b5`, `b6`, `b9`): `mle[i]` at level `0`. -/
theorem outer (hp : Placed code k) {m0 : MachineData} (hpre : MleOfMultilinearEvalPre m0)
    {i : Nat} {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b5Offset))
    (hO : Outer (ents m0) m0 i s.data) :
    Eventually (step1 Host.exe)
      (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b10Offset) ∧ Inner (ents m0) R1 m0 i 0 s'.data) s := by
  obtain ⟨hS, h02, h64, hrM, hrP⟩ := hpre
  have hi := hO.hi
  have hiN : i < 2 ^ 64 := by have := (reg m0 .rdx).isLt; simp only [nn] at hi; omega
  have hwf := hO.fr.body.wf (vars := fun _ ↦ 0) (ret := 0) hS (by decide)
  refine exec_at (hb5 hp) run_b5 hwf (by intro l h; cases h) hpc hO.fr.body.mid_match
    fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨hO1, -⟩ := Outer.of_keeps hO hS hO.fr.body.mid_match hm1 hwf rfl
    (after_eq run_b5 ▸ b5_ok).1
  have hrdx : reg s1.data .rdx = BitVec.ofNat 64 i := by
    show s1.data.regs.get64 .rdx = _
    rw [hm1.regs .rdx _ (after_eq run_b5 ▸ b5_ok).2, eval_load]
    exact val_load (env := frameEnv m0 s.data 1216) (r := 0) hO.wi (by simp)
  simp only [PcOk] at hpc1
  have hpc1' := (pc_cond hpc1).2 (by
    show ¬(!(CmpOp.apply .ult .W64 ((frameEnv m0 s.data 1216).load 0 16 8)
      ((frameEnv m0 s.data 1216).load 0 40 8))) = true
    rw [val_load (env := frameEnv m0 s.data 1216) (r := 0) hO.wi (o := 16)
        (v := BitVec.ofNat 64 i) (by simp),
      val_load (env := frameEnv m0 s.data 1216) (r := 0) hO.fr.args (o := 40)
        (v := reg m0 .rdx) (by simp [argVals])]
    have : CmpOp.apply .ult .W64 (BitVec.ofNat 64 i) (reg m0 .rdx) = true := by
      show (low .W64 (BitVec.ofNat 64 i)).ult (low .W64 (reg m0 .rdx)) = true
      rw [low_W64, low_W64]
      exact BitVec.ult_iff_lt.mpr (BitVec.lt_def.mpr (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hiN]; exact hi))
    rw [this]
    decide)
  -- `mle[i]`
  obtain ⟨hwf6, hm6, hv6⟩ := hO1.fr.body.elem (ret := 0) hS (by decide) (SliceIn.of_ok hrM) hi
    (x := .bin .add .W64 (.load 0 24 8) (.bin .shl .W64 (.reg .rdx) (.lit 4))) (o := 0) (by
      rw [eval_add, eval_load, eval_shl_lit _ (by decide), eval_reg, Env.ofMachine_regs,
        show s1.data.regs.get64 .rdx = BitVec.ofNat 64 i from hrdx, ofNat_shl4, add_ofNat_zero]
      rw [val_load (env := elemEnv m0 s1.data 1216 (reg m0 .rsi) i 0) (r := 0) hO1.fr.args
        (o := 24) (v := reg m0 .rsi) (by simp [argVals])])
  refine exec_at (hb6 hp) run_b6 hwf6 (by intro l h; cases h) (pc_len (n := 4) hpc1' rfl rfl) hm6
    fun s2 hm2 hpc2 ↦ ?_
  obtain ⟨hO2, hr2⟩ := Outer.of_keeps hO1 hS hm6 hm2 hwf6 rfl (after_eq run_b6 ▸ b6_ok).1
  have hrdx2 : reg s2.data .rdx = BitVec.ofNat 64 i := (hr2 .rdx (by simp)).trans hrdx
  simp only [PcOk] at hpc2
  refine Eventually.mono (enter_step R1 (es := ents m0) hS (hb9 hp) run_b9
    (after_eq run_b9 ▸ b9_ok) (hpc2.trans (lbl_9 hp)) hO2 (by simp only [ents, NativeRustcVm.length_ewsOf]; exact hi) hrdx2
    ?_)
    fun s' ⟨hpc', hI⟩ ↦ ⟨pc_len (n := 6) hpc' rfl rfl, hI⟩
  show ewArg (s2.data.regs.get64 .r15) (s2.data.regs.get64 .rbp) = _
  rw [hm2.regs .r15 _ (after_eq run_b6 ▸ b6_ok).2.1, hm2.regs .rbp _ (after_eq run_b6 ▸ b6_ok).2.2]
  exact hv6

/-- **`multilinear_eval_by` (`multilinear_eval`'s closure) meets its contract.** -/
theorem mleOfMultilinearEval_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hpre' := hpre
  obtain ⟨hS, h02, h64, hrM, hrP⟩ := hpre
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0)
    (stackOk_mono hS (show 1216 ≤ mleStack by decide)) fun _ h ↦ h
  refine exec_then (hb0 hp) run_b0 hwf (by intro l h; cases h) match_frame fun s1 hm1 hpc1 ↦ ?_
  have hZ := entry_zinv hS hm1 (after_eq run_b0 ▸ b0_ok).1 (after_eq run_b0 ▸ b0_ok).2
  refine Eventually.bind (zero_loop (hb1 hp) run_b1 (after_eq run_b1 ▸ b1_ok) (lbl_1 hp) hS
    (pc_len (n := 11) hpc1 rfl rfl) hZ) fun s2 ⟨hpc2, bd2, h56, hregs⟩ ↦ ?_
  have hr : ∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8], s2.data.regs.get64 r = reg m0 r := hregs
  have hwf2 := bd2.wf (vars := fun _ ↦ 0) (ret := 0) hS (by decide)
  refine exec_at (hb2 hp) run_b2 hwf2 (by intro l h; cases h) (pc_len (n := 12) hpc2 rfl rfl)
    bd2.mid_match fun s3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  rw [eval_test, eval_reg, Env.ofMachine_regs, hr .rdi (by simp), h02, ← ofNat_toNat (reg m0 .rdx),
    ofNat_beq (reg m0 .rdx).isLt (by decide)] at hpc3
  obtain ⟨hT, hF⟩ := pc_cond hpc3
  by_cases hz : (reg m0 .rdx).toNat = 0
  · -- `n = 0`: `0`.
    have bd3 := init_body hS bd2 hm3 (after_eq run_b2 ▸ init_ok).1
    have he : ents m0 = [] := List.eq_nil_of_length_eq_zero
      (by simp only [ents, NativeRustcVm.length_ewsOf]; exact hz)
    refine Eventually.bind (zero_end R1 (es := ents m0) hS (hb20 hp) run_b20
      (after_eq run_b20 ▸ b20_ok) ((hT (by simp [hz])).trans (lbl_3 hp)) bd3
      (by rw [he]; rfl)) fun s4 ⟨hpc4, hE⟩ ↦ ?_
    exact Eventually.mono (finish_step R1 hS (hb21 hp) run_b21 (after_eq run_b21 ▸ b21_ok)
      (pc_len (n := 3) hpc4 rfl rfl) hE) fun _ h ↦ post_of h
  · have hpc3' := pc_len (n := 10) (hF (by simp [hz])) rfl rfl
    refine exec_at (hb3 hp) (exec_after run_b2 run_b3) hwf2 (by intro l h; cases h) hpc3' hm3
      fun s4 hm4 hpc4 ↦ ?_
    simp only [PcOk] at hpc4
    rw [eval_test, eval_reg, Env.ofMachine_regs, hr .r8 (by simp), ← ofNat_toNat (reg m0 .r8),
      ofNat_beq (reg m0 .r8).isLt (by decide)] at hpc4
    obtain ⟨hT4, hF4⟩ := pc_cond hpc4
    by_cases hz4 : (reg m0 .r8).toNat = 0
    · -- `|point| = 0`: `mle[0]`.
      refine exec_at (hb18 hp) (exec_after run_b3 run_b18) hwf2 (by intro l h; cases h)
        ((hT4 (by simp [hz4])).trans (lbl_13 hp)) hm4 fun s5 hm5 hpc5 ↦ ?_
      have bd5 := init_body hS bd2 hm5 (after_eq run_b18 ▸ init_ok).2.2.1
      simp only [PcOk] at hpc5
      rw [eval_test, eval_reg, Env.ofMachine_regs, hr .rdx (by simp), ← ofNat_toNat (reg m0 .rdx),
        ofNat_beq (reg m0 .rdx).isLt (by decide)] at hpc5
      have hpc5' := pc_len (n := 3) ((pc_cond hpc5).2 (by simp [hz])) rfl rfl
      have hn0 : 0 < nn m0 := Nat.pos_of_ne_zero hz
      have hrsi : reg s5.data .rsi = reg m0 .rsi := by
        have h18 := after_eq run_b18 ▸ b18_rsi
        exact (hm5.regs .rsi (.reg .rsi) h18).trans (hr .rsi (by simp))
      have hrd : Readable s5.data (reg m0 .rsi) 16 := by
        have := elem_mapped hrM.1 bd5.kept hn0
        rwa [Nat.mul_zero, add_ofNat_zero] at this
      have hwf19 := wf1 hrd (st := s5.data)
      have hm19 : Match (Env.ofMachine s5.data [(reg m0 .rsi, 16)]) ldS s5.data :=
        match_ofMachine ⟨rfl, trivial⟩ ⟨hrsi.trans (eval_ptr0 rfl).symm, trivial⟩ trivial
          trivial trivial
      refine exec_at (hb19 hp) run_b19 hwf19 (by intro l h; cases h) hpc5' hm19
        fun s6 hm6 hpc6 ↦ ?_
      have bd6 := (body_of_keeps bd5 hS hm19 hm6 hwf19 rfl (after_eq run_b19 ▸ b19_ok).1).1
      simp only [PcOk] at hpc6
      refine Eventually.mono (finish_step R1 (es := ents m0) hS (hb21 hp) run_b21
        (after_eq run_b21 ▸ b21_ok) (hpc6.trans (lbl_15 hp)) ⟨bd6, ?_⟩) fun _ h ↦ post_of h
      have he := elem_of_apart bd5.same hS hrM.1.2 hrM.2 (apart_zero _ _) noWrap_zero hn0
      rw [Nat.mul_zero, add_ofNat_zero] at he
      have hd : (ents m0).drop 0 = _ := List.drop_eq_getElem_cons
        (by simp only [ents, NativeRustcVm.length_ewsOf]; exact hn0)
      rw [List.drop_zero] at hd
      rw [hd, NativeRustcVm.Mle.stream_cons, NativeRustcVm.Mle.cont_top _
        (by simp only [pts, NativeRustcVm.length_ewsOf]; exact Nat.le_of_eq hz4)]
      refine Eq.trans ?_ he
      show ewArg (s6.data.regs.get64 .r15) (s6.data.regs.get64 .rbp) = _
      rw [hm6.regs .r15 _ (after_eq run_b19 ▸ b19_ok).2.1,
        hm6.regs .rbp _ (after_eq run_b19 ▸ b19_ok).2.2, eval_load, eval_load]
      have := ewOf_loads (Env.ofMachine s5.data [(reg m0 .rsi, 16)]) 0 0
      rw [add_ofNat_zero] at this
      exact this.symm
    · -- the loops.
      refine exec_at (hb4 hp) (exec_after run_b3 run_b4) hwf2 (by intro l h; cases h)
        (pc_len (n := 2) (hF4 (by simp [hz4])) rfl rfl) hm4 fun s5 hm5 hpc5 ↦ ?_
      have hO := init_outer (es := ents m0) hS ⟨bd2, h56, hregs⟩ hm5
        (after_eq run_b4 ▸ init_ok).2.2.2 (after_eq run_b4 ▸ b4_args) (Nat.pos_of_ne_zero hz)
        (Nat.pos_of_ne_zero hz4) h64
      simp only [PcOk] at hpc5
      refine Eventually.bind (loops R1 (kO := k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b5Offset) (kI := k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b10Offset) (kEnd := k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b21Offset)
        (fun i s hpc hO ↦ outer hp hpre' hpc hO) (fun i kk s hpc hI ↦ ?_)
        (pc_len (n := 6) hpc5 rfl rfl) hO) fun s6 ⟨hpc6, hE⟩ ↦
        Eventually.mono (finish_step R1 hS (hb21 hp) run_b21 (after_eq run_b21 ▸ b21_ok) hpc6 hE)
          fun _ h ↦ post_of h
      have h11next : k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b11Offset + s11a.length + s11b.length =
          k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b12Offset := by
        change k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b11Offset + b11.length = _
        rw [Nat.add_assoc, NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b11_next]
      have h12next : k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b12Offset + b12.length = k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b13Offset := by
        rw [Nat.add_assoc, NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b12_next]
      have h13next : k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b13Offset + b13.length = k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b14Offset := by
        rw [Nat.add_assoc, NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b13_next]
      exact inner_turn R1 R1_saved hmul hS h02 (by simp only [ents, NativeRustcVm.length_ewsOf]) hrP
        (hb10 hp) run_b10 (after_eq run_b10 ▸ b10_ok) (lbl_11 hp)
        (hb16 hp) run_b16 (after_eq run_b16 ▸ b16_ok) (lbl_6 hp)
        (hb17 hp) rfl run_b17 (after_eq run_b17 ▸ jumps_ok.2)
        (k1 := k + NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.b11Offset) rfl (hb11 hp).1 run_s11a (after_eq run_s11a ▸ s11a_ok)
        (hb11 hp).2 run_s11b (after_eq run_s11b ▸ s11b_ok)
        (by rw [h11next]; exact hb12 hp)
        run_b12 (after_eq run_b12 ▸ b12_ok)
        (by rw [h11next, h12next]; exact hb13 hp)
        run_b13 (after_eq run_b13 ▸ b13_ok) (lbl_10 hp)
        (hb14 hp) (by rw [h11next, h12next, h13next])
        run_b14 (after_eq run_b14 ▸ jumps_ok.1) (lbl_15 hp) hpc hI

end

end NativeRustcVmX64.Arrays.MleOfMultilinearEval
