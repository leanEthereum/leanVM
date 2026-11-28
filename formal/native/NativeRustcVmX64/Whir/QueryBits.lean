module

public import NativeRustcVmX64.Whir.QueryBits.Exec
public import NativeRustcVmX64.Field.Leaf
public import NativeRustcVmX64.Spec.Whir
public import NativeRustcVmX64.Code.Vm.QueryBits.Names

/-!
# `query_bits` on x86-64

Four paths, by the shift `s` (RDX): `0` (`b0`, `b6`), below `64` (`b0`, `b1`, `b2`: `shrd`, `b6`),
below `128` (`b0`, `b1`, `b3`, `b4`: `shr` of the high word, `b6`), else (`b0`, `b1`, `b3`, `b5`:
`0`, `b6`); `b6` masks with `-1` for a depth (RCX) of `64` or more, else `!(-1 << depth)`, the low
`depth` bits (`eval_retS`).
-/

namespace NativeRustcVmX64.Whir.QueryBits

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.QueryBits NativeRustcVmX64.Field
  NativeVm.Model

public section

/-! ## Words -/

/-- The low `n` bits, as the code computes them. -/
theorem not_shl_eq (n : Nat) (h : n < 64) :
    ~~~(BitVec.ofNat 64 18446744073709551615 <<< n) = BitVec.ofNat 64 (2 ^ n - 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and]
  by_cases hin : i < n
  · simp [hin]
  · have : (18446744073709551615 : Nat).testBit (i - n) = true := by
      rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl, Nat.testBit_two_pow_sub_one]
      simp; omega
    simp [hin, this]
    omega

/-- The model's mask. -/
theorem mask_toBitVec (n : Nat) (h : n < 64) :
    ((1 : UInt64) <<< n.toUInt64 - 1).toBitVec = BitVec.ofNat 64 (2 ^ n - 1) := by
  have hp : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) h
  have hp1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  apply BitVec.eq_of_toNat_eq
  have hn : (n.toUInt64.toBitVec % 64).toNat = n := by
    rw [BitVec.toNat_umod]; simp; omega
  rw [UInt64.toBitVec_sub, UInt64.toBitVec_shiftLeft, BitVec.toNat_sub, BitVec.shiftLeft_eq', hn,
    BitVec.toNat_shiftLeft]
  simp only [UInt64.toBitVec_one, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  generalize 2 ^ n = P at hp hp1 ⊢
  omega

/-- A shift count read from ECX: the count modulo `64`. -/
theorem shiftCount_trunc (x : BitVec 64) :
    shiftCount .W64 (UnOp.apply .trunc .W32 x) = x.toNat % 64 := by
  simp only [shiftCount, shiftMask, UnOp.apply, toNat_low, toNat_ext, Width.bits]
  show x.toNat % 2 ^ 32 % 2 ^ 8 &&& (2 ^ 6 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem toNat_umod64 {n : Nat} (h : n < 64) : (n.toUInt64.toBitVec % 64).toNat = n := by
  rw [BitVec.toNat_umod]; simp; omega

/-- `shrd lo, hi, s`: the low 64 bits of `hi : lo` shifted right by `0 < s < 64`. -/
theorem shrd_eq (lo hi z : BitVec 64) {s : Nat} (hc : shiftCount .W64 z = s) (h0 : 0 < s)
    (hs : s < 64) : TernOp.apply .shrd .W64 lo hi z = lo >>> s ||| hi <<< (64 - s) := by
  simp only [TernOp.apply, hc, low_W64, ext_W64, show (s == 0) = false by simp; omega,
    Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [Width.bits, BitVec.take, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hi', decide_true,
    Bool.true_and, Nat.zero_add]
  rw [show hi.append lo = hi ++ lo from rfl, BitVec.getLsbD_append]
  by_cases h1 : s + i < 64
  · simp only [h1, ↓reduceIte]
    simp [show i < 64 - s by omega]
  · simp only [h1, ↓reduceIte]
    rw [BitVec.getLsbD_of_ge lo (s + i) (by omega), Bool.false_or,
      show s + i - 64 = i - (64 - s) by omega]
    simp [show ¬ i < 64 - s by omega]

/-! ## The model -/

/-- The model's value before its mask. -/
@[expose] def qv (c : EW) (s : Nat) : UInt64 :=
  if s = 0 then c.c0
  else if s < 64 then (c.c0 >>> s.toUInt64) ||| (c.c1 <<< (64 - s).toUInt64)
  else if s < 128 then c.c1 >>> (s - 64).toUInt64
  else 0

theorem queryBits_eq (c : EW) (s d : Nat) :
    queryBits c s d = if 64 ≤ d then qv c s else qv c s &&& ((1 : UInt64) <<< d.toUInt64 - 1) :=
  rfl

section
variable [Labels]

/-- **RAX at the return**: the value masked to its low `depth` bits below `64`. -/
theorem eval_retS (env : Env) (v : Sym) :
    (retS v).eval env = if 64 ≤ (env.regs .rcx).toNat then v.eval env
      else v.eval env &&& BitVec.ofNat 64 (2 ^ (env.regs .rcx).toNat - 1) := by
  simp only [retS, maskS, Sym.eval, SBool.eval, BinOp.apply, UnOp.apply, CmpOp.apply, low_W64,
    ext_W64]
  by_cases h : 64 ≤ (env.regs .rcx).toNat
  · have hu : (env.regs .rcx).ult (BitVec.ofNat 64 64) = false := by
      simp [BitVec.ult]; omega
    simp only [hu, Bool.not_false, ↓reduceIte, h]
    rw [show (BitVec.ofNat 64 18446744073709551615 : BitVec 64) = BitVec.allOnes 64 by decide,
      BitVec.allOnes_and]
  · have hu : (env.regs .rcx).ult (BitVec.ofNat 64 64) = true := by
      simp [BitVec.ult]; omega
    simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h]
    rw [show shiftCount .W64 (ext .W32 (low .W32 (env.regs .rcx))) = (env.regs .rcx).toNat from by
        rw [← show UnOp.apply .trunc .W32 (env.regs .rcx) = ext .W32 (low .W32 (env.regs .rcx))
          from rfl, shiftCount_trunc]
        omega,
      not_shl_eq _ (by omega), BitVec.and_comm]
end

variable [Host] {k : Nat}

/-- The environment of the entry: region 0 its return address. -/
abbrev envOf (m : MachineData) : Env := frameEnv m m 0

/-- **A path's end**: `ret` from a state `finOk`, RAX the model's value where the path's value `v`
is the model's before the mask. -/
theorem finish {m : MachineData} (hpre : QueryBitsPre m) {S' : SState} {v : Sym}
    {st : MachineState} (hm' : Match (envOf m) S' st.data)
    {nx : Int64} (hpc : PcOk (envOf m) (.ret (.load 0 0 8)) nx st) (hf : finOk S' v = true)
    (hv : v.eval (envOf m) = (qv (ewArg (reg m .rdi) (reg m .rsi)) (reg m .rdx).toNat).toBitVec) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧ QueryBitsPost m st.data) st := by
  simp only [finOk, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hf
  obtain ⟨⟨⟨hax, hk⟩, hmem⟩, hsp⟩ := hf
  obtain ⟨hpc', hrsp, hso, hsaved⟩ :=
    leaf_done (F := 0) hpre hm' hpc hsp hk (by rw [hmem]; intro w hw; cases hw)
  refine .done _ ⟨hpc', hrsp, ?_, fun p hp ↦ hso p fun h ↦ hp (.inr h), hsaved⟩
  show st.data.regs.get64 .rax = _
  rw [hm'.regs .rax _ hax, eval_retS, hv, queryBits_eq]
  show (if 64 ≤ (reg m .rcx).toNat then _ else _) = _
  split
  · rfl
  · rw [UInt64.toBitVec_and, mask_toBitVec _ (by omega)]
    rfl

theorem inf (hp : Placed code k) {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

/-- **`query_bits`'s contract.** -/
theorem queryBits_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmX64.Vm.QueryBits.entryLabel) QueryBitsPre QueryBitsPost := by
  intro m hpre
  rw [show Labels.label NativeRustcVmX64.Vm.QueryBits.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.QueryBits.b0Offset) from hp.label NativeRustcVmX64.Vm.QueryBits.entry_at]
  have hwf : (envOf m).WF := frame_wf (F := 0) hpre fun _ h ↦ h
  have hm : Match (envOf m) entryS m := match_frame
  have hx : ∀ r, (envOf m).regs r = reg m r := fun _ ↦ rfl
  have hc0 : ∀ x : BitVec 64, (ewArg (reg m .rdi) x).c0.toBitVec = reg m .rdi := fun _ ↦ rfl
  have hc1 : (ewArg (reg m .rdi) (reg m .rsi)).c1.toBitVec = reg m .rsi := rfl
  refine exec_then (inf hp b0_in_code (by simp [b0])) run_b0 hwf (by intro l h; cases h) hm
    fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmX64.Vm.QueryBits.b0_length, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply,
    low_W64, ext_W64, BitVec.and_self, hx] at hpc1
  by_cases hz : (reg m .rdx).toNat = 0
  · -- shift `0`: `b6`
    have hz' : reg m .rdx = BitVec.ofNat 64 0 := BitVec.eq_of_toNat_eq (by simp [hz])
    simp only [hz', beq_self_eq_true, ↓reduceIte, hp.label NativeRustcVmX64.Vm.QueryBits.label_6_at] at hpc1
    refine exec_at (inf hp b6_in_code (by simp [b6])) (exec_after run_b0 run_b6z) hwf
      (by intro l h; cases h) hpc1 hm1 fun st hm' hpc ↦ finish hpre hm' hpc
        (after_eq run_b6z ▸ fin_z) ?_
    simp only [qv, hz, ↓reduceIte]
    rfl
  have hz' : (reg m .rdx == BitVec.ofNat 64 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact fun h ↦ hz (by rw [h]; rfl)
  simp only [hz', Bool.false_eq_true, ↓reduceIte] at hpc1
  refine exec_at (inf hp b1_in_code (by simp [b1])) (exec_after run_b0 run_b1) hwf
    (by intro l h; cases h) hpc1 hm1 fun st2 hm2 hpc2 ↦ ?_
  simp only [PcOk, show k + NativeRustcVmX64.Vm.QueryBits.b1Offset + b1.length = k + NativeRustcVmX64.Vm.QueryBits.b2Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.QueryBits.b1_next], SBool.eval, Sym.eval,
    CmpOp.apply, low_W64, hx] at hpc2
  by_cases h64 : (reg m .rdx).toNat < 64
  · -- `0 < shift < 64`: `b2`, `b6`
    have hu : (reg m .rdx).ult (BitVec.ofNat 64 64) = true := by simp [BitVec.ult]; omega
    simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc2
    refine exec_at (inf hp b2_in_code (by simp [b2])) (exec_after run_b1 run_b2) hwf
      (by intro l h; cases h) hpc2 hm2 fun st3 hm3 hpc3 ↦ ?_
    simp only [PcOk, hp.label NativeRustcVmX64.Vm.QueryBits.label_6_at] at hpc3
    refine exec_at (inf hp b6_in_code (by simp [b6])) (exec_after run_b2 run_b6a) hwf
      (by intro l h; cases h) hpc3 hm3 fun st hm' hpc ↦ finish hpre hm' hpc
        (after_eq run_b6a ▸ fin_a) ?_
    simp only [qv, hz, h64, ↓reduceIte, Sym.eval, shS, hx]
    rw [shrd_eq _ _ _ ((shiftCount_trunc _).trans (Nat.mod_eq_of_lt h64)) (by omega) h64,
      UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft,
      BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', toNat_umod64 h64, toNat_umod64 (by omega)]
    rfl
  have hu : (reg m .rdx).ult (BitVec.ofNat 64 64) = false := by simp [BitVec.ult]; omega
  simp only [hu, Bool.not_false, ↓reduceIte, hp.label NativeRustcVmX64.Vm.QueryBits.label_2_at] at hpc2
  refine exec_at (inf hp b3_in_code (by simp [b3])) (exec_after run_b1 run_b3) hwf
    (by intro l h; cases h) hpc2 hm2 fun st4 hm4 hpc4 ↦ ?_
  simp only [PcOk, show k + NativeRustcVmX64.Vm.QueryBits.b3Offset + b3.length = k + NativeRustcVmX64.Vm.QueryBits.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.QueryBits.b3_next], SBool.eval, Sym.eval,
    CmpOp.apply, low_W64, hx] at hpc4
  by_cases h128 : (reg m .rdx).toNat < 128
  · -- `64 ≤ shift < 128`: `b4`, `b6`
    have hu : (reg m .rdx).ult (BitVec.ofNat 64 128) = true := by simp [BitVec.ult]; omega
    simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc4
    refine exec_at (inf hp b4_in_code (by simp [b4])) (exec_after run_b3 run_b4) hwf
      (by intro l h; cases h) hpc4 hm4 fun st5 hm5 hpc5 ↦ ?_
    simp only [PcOk, hp.label NativeRustcVmX64.Vm.QueryBits.label_6_at] at hpc5
    refine exec_at (inf hp b6_in_code (by simp [b6])) (exec_after run_b4 run_b6b) hwf
      (by intro l h; cases h) hpc5 hm5 fun st hm' hpc ↦ finish hpre hm' hpc
        (after_eq run_b6b ▸ fin_b) ?_
    simp only [qv, hz, h64, h128, ↓reduceIte, Sym.eval, shS, hx, BinOp.apply, low_W64, ext_W64,
      shiftCount_trunc]
    rw [UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', toNat_umod64 (by omega),
      show (reg m .rdx).toNat % 64 = (reg m .rdx).toNat - 64 by omega]
    rfl
  · -- `128 ≤ shift`: `b5`, `b6`
    have hu : (reg m .rdx).ult (BitVec.ofNat 64 128) = false := by simp [BitVec.ult]; omega
    simp only [hu, Bool.not_false, ↓reduceIte, hp.label NativeRustcVmX64.Vm.QueryBits.label_3_at] at hpc4
    refine exec_at (inf hp b5_in_code (by simp [b5])) (exec_after run_b3 run_b5) hwf
      (by intro l h; cases h) hpc4 hm4 fun st5 hm5 hpc5 ↦ ?_
    simp only [PcOk, show k + NativeRustcVmX64.Vm.QueryBits.b5Offset + b5.length = k + NativeRustcVmX64.Vm.QueryBits.b6Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.QueryBits.b5_next]] at hpc5
    refine exec_at (inf hp b6_in_code (by simp [b6])) (exec_after run_b5 run_b6c) hwf
      (by intro l h; cases h) hpc5 hm5 fun st hm' hpc ↦ finish hpre hm' hpc
        (after_eq run_b6c ▸ fin_c) ?_
    simp only [qv, hz, h64, h128, ↓reduceIte, Sym.eval]
    rfl

end

end NativeRustcVmX64.Whir.QueryBits
