module

public import NativeRustcVmX64.Arrays.MultilinearEvalByOfComputedBytecodeValue.Exec
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfComputedBytecodeValue.Names

/-!
# `multilinear_eval_by` (`computed_bytecode_value`'s closure) on x86-64

**`mleOfComputedBytecodeValue_spec`**: rustc's
`multilinear_eval_by(n, |i| EW::of_k(words[i]), point)`, placed anywhere in the program, meets
`MleOfComputedBytecodeValuePre`/`MleOfComputedBytecodeValuePost` given `EW::mul`'s contract. The
prologue (`b0`) pushes RBP, R15, R14, R13, R12, RBX, reserves 1160 bytes, stores `point` and
returns `0` at `|point| > 63` (`b19`: the model's value is `0` there,
`NativeRustcVm.Mle.multilinearEval_eq_zero`); the loop `b2` zeroes the pending entries, `b3` the
flags; `n = 0` returns `0` (`b19`), `|point| = 0` returns `words[0]` (`b17`, `b18`); otherwise
`b5` stores the arguments and the loops (`MleFrame.loops`: `outer` loads `words[i]`,
`MleFrame.inner_turn` carries it) stream the entries; the epilogue `b20` returns the value.
-/

namespace NativeRustcVmX64.Arrays.MleOfComputedBytecodeValue

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue
  NativeVm.Model NativeRustcVmX64.Field NativeRustcVmX64.Arrays.MleFrame
open NativeRustcVm (wordOf ewOf ewsOf wordsOf)
open NativeRustcVm.Mle (stream cont setP)

public section

/-- The entries: the words, each in limb `0`. -/
abbrev wes (m0 : MachineData) : List EW :=
  (wordsOf m0.dmem (reg m0 .rsi) (reg m0 .rdx).toNat).map EW.ofK

theorem pc_len [Host] {s : MachineState} {a b n : Nat} {L : List Directive}
    (h : s.pc = Host.addrOf (a + L.length)) (hL : L.length = n) (e : a + n = b) :
    s.pc = Host.addrOf b := by
  rw [h, hL, e]

/-- The postcondition, from the streamed value. -/
theorem post_of [Host] {m0 : MachineData} {s : MachineState}
    (h : s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧
      ewRet s.data = stream (pts m0) (wes m0) (fun _ ↦ none) ∧ Changes m0 s.data mleStack 0 0 ∧
      Saved m0 s.data) :
    s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ MleOfComputedBytecodeValuePost m0 s.data :=
  ⟨h.1, h.2.1, h.2.2.1.trans (NativeRustcVm.Mle.stream_eq _ _), h.2.2.2⟩

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ofNat_mul8 (i : Nat) : BitVec.ofNat 64 i * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- A word in limb `0`. -/
theorem ewArg_ofK (w : UInt64) : ewArg w.toBitVec (BitVec.ofNat 64 0) = EW.ofK w := by
  unfold ewArg EW.ofK
  rw [UInt64.ofBitVec_toBitVec]
  rfl

/-- `ja` after `cmp $63`: `|point| > 63`. -/
theorem gt63 [Labels] (env : Env) :
    (SBool.and (.not (.cmp .ult .W64 (.reg .r8) (.lit 63)))
      (.not (.cmp .eq .W64 (.reg .r8) (.lit 63)))).eval env =
      decide (63 < (env.regs .r8).toNat) := by
  show (!(CmpOp.apply .ult .W64 (env.regs .r8) (BitVec.ofNat 64 63)) &&
    !(CmpOp.apply .eq .W64 (env.regs .r8) (BitVec.ofNat 64 63))) = _
  simp only [CmpOp.apply, low_W64]
  generalize env.regs .r8 = x
  have e1 : x.ult (BitVec.ofNat 64 63) = decide (x.toNat < 63) := by
    rw [Bool.eq_iff_iff, BitVec.ult_iff_lt, BitVec.lt_def, decide_eq_true_iff, BitVec.toNat_ofNat]
  have e2 : (x == BitVec.ofNat 64 63) = decide (x.toNat = 63) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · rintro rfl; rfl
    · intro h; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
  rw [e1, e2]
  by_cases h1 : x.toNat < 63 <;> by_cases h2 : x.toNat = 63 <;> simp [h1, h2] <;> omega

/-- At `|point| > 63` the value is `0`. -/
theorem stream_zero {m0 : MachineData} (h : 63 < (reg m0 .r8).toNat) :
    stream (pts m0) (wes m0) (fun _ ↦ none) = 0 := by
  rw [show stream (pts m0) (wes m0) (fun _ ↦ none) =
      multilinearEval (wordSliceE m0 (reg m0 .rsi) (reg m0 .rdx)) (slice m0 (reg m0 .rcx) (reg m0 .r8))
    from NativeRustcVm.Mle.stream_eq _ _]
  apply NativeRustcVm.Mle.multilinearEval_eq_zero
  simp only [wordSliceE, slice, List.size_toArray, List.length_map, NativeRustcVm.length_wordsOf,
    NativeRustcVm.length_ewsOf]
  calc (reg m0 .rdx).toNat < 2 ^ 64 := (reg m0 .rdx).isLt
    _ ≤ 2 ^ (reg m0 .r8).toNat := Nat.pow_le_pow_right (by decide) (by omega)

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b9Offset) :=
  b9_in_code.trans hp.1 (by simp [b9])
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b10Offset) :=
  b10_in_code.trans hp.1 (by simp [b10])
theorem hb11 (hp : Placed code k) : s11a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b11Offset) ∧
    s11b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b11Offset + s11a.length) := by
  have h := b11_in_code.trans hp.1 (by simp [b11])
  rw [← List.take_append_drop 9 b11] at h
  exact h.append
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b12Offset) :=
  b12_in_code.trans hp.1 (by simp [b12])
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b13Offset) :=
  b13_in_code.trans hp.1 (by simp [b13])
theorem hb14 (hp : Placed code k) : b14.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b14Offset) :=
  b14_in_code.trans hp.1 (by simp [b14])
theorem hb15 (hp : Placed code k) : b15.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b15Offset) :=
  b15_in_code.trans hp.1 (by simp [b15])
theorem hb16 (hp : Placed code k) : b16.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b16Offset) :=
  b16_in_code.trans hp.1 (by simp [b16])
theorem hb17 (hp : Placed code k) : b17.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b17Offset) :=
  b17_in_code.trans hp.1 (by simp [b17])
theorem hb18 (hp : Placed code k) : b18.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b18Offset) :=
  b18_in_code.trans hp.1 (by simp [b18])
theorem hb19 (hp : Placed code k) : b19.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b19Offset) :=
  b19_in_code.trans hp.1 (by simp [b19])
theorem hb20 (hp : Placed code k) : b20.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b20Offset) :=
  b20_in_code.trans hp.1 (by simp [b20])

theorem lbl_entry (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b0Offset) := hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.entry_at
theorem lbl_1 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b19Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_1_at
theorem lbl_3 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b2Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_3_at
theorem lbl_7 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_7 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b6Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_7_at
theorem lbl_10 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_10 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b9Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_10_at
theorem lbl_11 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_11 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b10Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_11_at
theorem lbl_12 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_12 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b15Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_12_at
theorem lbl_14 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_14 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b17Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_14_at
theorem lbl_16 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_16 = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b20Offset) :=
  hp.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.label_16_at

/-- **The outer loop's set-up** (`b6`, `b7`, `b9`): `words[i]` at level `0`. -/
theorem outer (hp : Placed code k) {m0 : MachineData} (hpre : MleOfComputedBytecodeValuePre m0)
    {i : Nat} {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b6Offset))
    (hO : Outer (wes m0) m0 i s.data) :
    Eventually (step1 Host.exe)
      (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b10Offset) ∧ Inner (wes m0) R2 m0 i 0 s'.data) s := by
  obtain ⟨hS, h02, hR, hoff, hrP⟩ := hpre
  have hi := hO.hi
  have hi' : i < (reg m0 .rdx).toNat := hi
  have hoff' := hoff (by omega)
  have hiN : i < 2 ^ 64 := by have := (reg m0 .rdx).isLt; omega
  have hwf := hO.fr.body.wf (vars := fun _ ↦ 0) (ret := 0) hS (by decide)
  refine exec_at (hb6 hp) run_b6 hwf (by intro l h; cases h) hpc hO.fr.body.mid_match
    fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨hO1, -⟩ := Outer.of_keeps hO hS hO.fr.body.mid_match hm1 hwf rfl
    (after_eq run_b6 ▸ b6_ok).1
  have hrcx : reg s1.data .rcx = BitVec.ofNat 64 i := by
    show s1.data.regs.get64 .rcx = _
    rw [hm1.regs .rcx _ (after_eq run_b6 ▸ b6_ok).2, eval_load]
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
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hiN]; exact hi'))
    rw [this]
    decide)
  -- `words[i]`
  have hfr := frame_piece hS hO1.fr.body.kept (o := 0) (n := 1224) (by omega)
  rw [add_ofNat_zero] at hfr
  have hw := word_mapped hR hO1.fr.body.kept hi'
  have hap := piece_offStack hS hoff' hR.2 (j := 8 * i) (w := 8) (o := 0) (n := 1224)
    (by omega) (by omega) (by omega) (by omega)
  rw [add_ofNat_zero] at hap
  have hwf7 := wf2 (st := s1.data) hfr hw (apart_symm hap)
  have hm7 : Match (Env.ofMachine s1.data [(fbOf m0, 1224),
      (reg m0 .rsi + BitVec.ofNat 64 (8 * i), 8)]) eS s1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hO1.fr.body.rsp, trivial⟩ trivial trivial ⟨by
      dsimp only
      rw [eval_add, eval_load, val_load (env := Env.ofMachine s1.data [(fbOf m0, 1224),
        (reg m0 .rsi + BitVec.ofNat 64 (8 * i), 8)]) (r := 0) hO1.fr.args (o := 24)
        (v := reg m0 .rsi) (by simp [argVals])]
      show reg m0 .rsi + BinOp.apply .mul .W64 (s1.data.regs.get64 .rcx) (BitVec.ofNat 64 8) =
        reg m0 .rsi + BitVec.ofNat 64 (8 * i) + BitVec.ofInt 64 0
      simp only [BinOp.apply, low_W64, ext_W64]
      rw [show s1.data.regs.get64 .rcx = BitVec.ofNat 64 i from hrcx, ofNat_mul8, ofInt_0,
        BitVec.add_zero], trivial⟩
  refine exec_at (hb7 hp) run_b7 hwf7 (by intro l h; cases h) (pc_len (n := 4) hpc1' rfl rfl) hm7
    fun s2 hm2 hpc2 ↦ ?_
  obtain ⟨hO2, hr2⟩ := Outer.of_keeps hO1 hS hm7 hm2 hwf7 rfl (after_eq run_b7 ▸ b7_ok).1
  have hrcx2 : reg s2.data .rcx = BitVec.ofNat 64 i := (hr2 .rcx (by simp)).trans hrcx
  simp only [PcOk] at hpc2
  refine Eventually.mono (enter_step R2 (es := wes m0) hS (hb9 hp) run_b9
    (after_eq run_b9 ▸ b9_ok) (hpc2.trans (lbl_10 hp)) hO2
    (by simp only [wes, List.length_map, NativeRustcVm.length_wordsOf]; exact hi') hrcx2 ?_)
    fun s' ⟨hpc', hI⟩ ↦ ⟨pc_len (n := 7) hpc' rfl rfl, hI⟩
  show ewArg (s2.data.regs.get64 .r13) (BitVec.ofNat 64 0) = _
  rw [hm2.regs .r13 _ (after_eq run_b7 ▸ b7_ok).2, eval_load, load8_eq, add_ofNat_zero, ewArg_ofK,
    List.getElem_map]
  congr 1
  exact word_of_apart hO1.fr.body.same hS hR.2 hoff' hi'

/-- **`multilinear_eval_by` (`computed_bytecode_value`'s closure) meets its contract.** -/
theorem mleOfComputedBytecodeValue_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.entryLabel) MleOfComputedBytecodeValuePre
      MleOfComputedBytecodeValuePost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hpre' := hpre
  obtain ⟨hS, h02, hR, hoff, hrP⟩ := hpre
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0)
    (stackOk_mono hS (show 1216 ≤ mleStack by decide)) fun _ h ↦ h
  refine exec_then (hb0 hp) run_b0 hwf (by intro l h; cases h) match_frame fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  rw [gt63, Env.ofMachine_regs] at hpc1
  obtain ⟨hT0, hF0⟩ := pc_cond hpc1
  by_cases h63 : 63 < (reg m0 .r8).toNat
  · -- `|point| > 63`: `0`.
    have bd1 := entry_body hS hm1 (after_eq run_b0 ▸ b0_ok)
    refine Eventually.bind (zero_end R2 (es := wes m0) hS (hb19 hp) run_b19
      (after_eq run_b19 ▸ b19_ok) ((hT0 (by simp [h63])).trans (lbl_1 hp)) bd1
      (stream_zero h63)) fun s4 ⟨hpc4, hE⟩ ↦ ?_
    exact Eventually.mono (finish_step R2 hS (hb20 hp) run_b20 (after_eq run_b20 ▸ b20_ok)
      (pc_len (n := 3) hpc4 rfl rfl) hE) fun _ h ↦ post_of h
  have h64 : mm m0 < 64 := by simp only [mm]; omega
  refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf (by intro l h; cases h)
    (pc_len (n := 11) (hF0 (by simp [h63])) rfl rfl) hm1 fun s1' hm1' hpc1' ↦ ?_
  have hZ := entry_zinv hS hm1' (after_eq run_b1 ▸ b1_ok).1 (after_eq run_b1 ▸ b1_ok).2
  refine Eventually.bind (zero_loop (hb2 hp) run_b2 (after_eq run_b2 ▸ b2_ok) (lbl_3 hp) hS
    (pc_len (n := 2) hpc1' rfl rfl) hZ) fun s2 ⟨hpc2, bd2, h56, hregs⟩ ↦ ?_
  have hr : ∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8], s2.data.regs.get64 r = reg m0 r := hregs
  have hwf2 := bd2.wf (vars := fun _ ↦ 0) (ret := 0) hS (by decide)
  refine exec_at (hb3 hp) run_b3 hwf2 (by intro l h; cases h) (pc_len (n := 12) hpc2 rfl rfl)
    bd2.mid_match fun s3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  rw [eval_test, eval_reg, Env.ofMachine_regs, hr .rdi (by simp), h02, ← ofNat_toNat (reg m0 .rdx),
    ofNat_beq (reg m0 .rdx).isLt (by decide)] at hpc3
  obtain ⟨hT, hF⟩ := pc_cond hpc3
  by_cases hz : (reg m0 .rdx).toNat = 0
  · -- `n = 0`: `0`.
    have bd3 := init_body hS bd2 hm3 (after_eq run_b3 ▸ init_ok).1
    have he : wes m0 = [] := List.eq_nil_of_length_eq_zero
      (by simp only [wes, List.length_map, NativeRustcVm.length_wordsOf]; exact hz)
    refine Eventually.bind (zero_end R2 (es := wes m0) hS (hb19 hp) run_b19
      (after_eq run_b19 ▸ b19_ok) ((hT (by simp [hz])).trans (lbl_1 hp)) bd3
      (by rw [he]; rfl)) fun s4 ⟨hpc4, hE⟩ ↦ ?_
    exact Eventually.mono (finish_step R2 hS (hb20 hp) run_b20 (after_eq run_b20 ▸ b20_ok)
      (pc_len (n := 3) hpc4 rfl rfl) hE) fun _ h ↦ post_of h
  · have hpc3' := pc_len (n := 10) (hF (by simp [hz])) rfl rfl
    refine exec_at (hb4 hp) (exec_after run_b3 run_b4) hwf2 (by intro l h; cases h) hpc3' hm3
      fun s4 hm4 hpc4 ↦ ?_
    simp only [PcOk] at hpc4
    rw [eval_test, eval_reg, Env.ofMachine_regs, hr .r8 (by simp), ← ofNat_toNat (reg m0 .r8),
      ofNat_beq (reg m0 .r8).isLt (by decide)] at hpc4
    obtain ⟨hT4, hF4⟩ := pc_cond hpc4
    have hn0 : 0 < (reg m0 .rdx).toNat := Nat.pos_of_ne_zero hz
    by_cases hz4 : (reg m0 .r8).toNat = 0
    · -- `|point| = 0`: `words[0]`.
      refine exec_at (hb17 hp) (exec_after run_b4 run_b17) hwf2 (by intro l h; cases h)
        ((hT4 (by simp [hz4])).trans (lbl_14 hp)) hm4 fun s5 hm5 hpc5 ↦ ?_
      have bd5 := init_body hS bd2 hm5 (after_eq run_b17 ▸ init_ok).2.2.1
      simp only [PcOk] at hpc5
      rw [eval_test, eval_reg, Env.ofMachine_regs, hr .rdx (by simp), ← ofNat_toNat (reg m0 .rdx),
        ofNat_beq (reg m0 .rdx).isLt (by decide)] at hpc5
      have hpc5' := pc_len (n := 3) ((pc_cond hpc5).2 (by simp [hz])) rfl rfl
      have hrsi : reg s5.data .rsi = reg m0 .rsi := by
        have h17 := after_eq run_b17 ▸ b17_rsi
        exact (hm5.regs .rsi (.reg .rsi) h17).trans (hr .rsi (by simp))
      have hrd : Readable s5.data (reg m0 .rsi) 8 := by
        have := word_mapped hR bd5.kept hn0
        rwa [Nat.mul_zero, add_ofNat_zero] at this
      have hwf18 := wf1 hrd (st := s5.data)
      have hm18 : Match (Env.ofMachine s5.data [(reg m0 .rsi, 8)]) ldS s5.data :=
        match_ofMachine ⟨rfl, trivial⟩ ⟨hrsi.trans (eval_ptr0 rfl).symm, trivial⟩ trivial
          trivial trivial
      refine exec_at (hb18 hp) run_b18 hwf18 (by intro l h; cases h) hpc5' hm18
        fun s6 hm6 hpc6 ↦ ?_
      have bd6 := (body_of_keeps bd5 hS hm18 hm6 hwf18 rfl (after_eq run_b18 ▸ b18_ok).1).1
      simp only [PcOk] at hpc6
      refine Eventually.mono (finish_step R2 (es := wes m0) hS (hb20 hp) run_b20
        (after_eq run_b20 ▸ b20_ok) (hpc6.trans (lbl_16 hp)) ⟨bd6, ?_⟩) fun _ h ↦ post_of h
      have hw0 := word_of_apart bd5.same hS hR.2 (hoff hn0) hn0
      rw [Nat.mul_zero, add_ofNat_zero] at hw0
      have hd : (wes m0).drop 0 = _ := List.drop_eq_getElem_cons
        (by simp only [wes, List.length_map, NativeRustcVm.length_wordsOf]; exact hn0)
      rw [List.drop_zero] at hd
      rw [hd, NativeRustcVm.Mle.stream_cons, NativeRustcVm.Mle.cont_top _
        (by simp only [pts, NativeRustcVm.length_ewsOf]; exact Nat.le_of_eq hz4), List.getElem_map]
      show ewArg (s6.data.regs.get64 .r13) (s6.data.regs.get64 .rbp) = _
      rw [hm6.regs .r13 _ (after_eq run_b18 ▸ b18_ok).2.1,
        hm6.regs .rbp _ (after_eq run_b18 ▸ b18_ok).2.2, eval_load, eval_lit, load8_eq,
        add_ofNat_zero, ewArg_ofK]
      exact congrArg EW.ofK hw0
    · -- the loops.
      refine exec_at (hb5 hp) (exec_after run_b4 run_b5) hwf2 (by intro l h; cases h)
        (pc_len (n := 2) (hF4 (by simp [hz4])) rfl rfl) hm4 fun s5 hm5 hpc5 ↦ ?_
      have hO := init_outer (es := wes m0) hS ⟨bd2, h56, hregs⟩ hm5
        (after_eq run_b5 ▸ init_ok).2.2.2 (after_eq run_b5 ▸ b5_args) hn0
        (Nat.pos_of_ne_zero hz4) h64
      simp only [PcOk] at hpc5
      refine Eventually.bind (loops R2 (kO := k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b6Offset) (kI := k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b10Offset) (kEnd := k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b20Offset)
        (fun i s hpc hO ↦ outer hp hpre' hpc hO) (fun i kk s hpc hI ↦ ?_)
        (pc_len (n := 6) hpc5 rfl rfl) hO) fun s6 ⟨hpc6, hE⟩ ↦
        Eventually.mono (finish_step R2 hS (hb20 hp) run_b20 (after_eq run_b20 ▸ b20_ok) hpc6 hE)
          fun _ h ↦ post_of h
      have h11next : k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b11Offset + s11a.length + s11b.length =
          k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b12Offset := by
        change k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b11Offset + b11.length = _
        rw [Nat.add_assoc, NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b11_next]
      have h12next : k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b12Offset + b12.length = k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b13Offset := by
        rw [Nat.add_assoc, NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b12_next]
      have h13next : k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b13Offset + b13.length = k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b14Offset := by
        rw [Nat.add_assoc, NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b13_next]
      exact inner_turn R2 R2_saved hmul hS h02
        (by simp only [wes, List.length_map, NativeRustcVm.length_wordsOf]) hrP
        (hb10 hp) run_b10 (after_eq run_b10 ▸ b10_ok) (lbl_12 hp)
        (hb15 hp) run_b15 (after_eq run_b15 ▸ b15_ok) (lbl_7 hp)
        (hb16 hp) rfl run_b16 (after_eq run_b16 ▸ jumps_ok.2)
        (k1 := k + NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.b11Offset) rfl (hb11 hp).1 run_s11a (after_eq run_s11a ▸ s11a_ok)
        (hb11 hp).2 run_s11b (after_eq run_s11b ▸ s11b_ok)
        (by rw [h11next]; exact hb12 hp)
        run_b12 (after_eq run_b12 ▸ b12_ok)
        (by rw [h11next, h12next]; exact hb13 hp)
        run_b13 (after_eq run_b13 ▸ b13_ok) (lbl_11 hp)
        (hb14 hp) (by rw [h11next, h12next, h13next])
        run_b14 (after_eq run_b14 ▸ jumps_ok.1) (lbl_16 hp) hpc hI

end

end NativeRustcVmX64.Arrays.MleOfComputedBytecodeValue
