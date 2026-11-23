module

public import NativeRustcVmArm.Code.Vm.QueryBits.Names
public import NativeRustcVmArm.Whir.QueryBits.Exec
public import NativeRustcVmArm.Spec.Whir

/-!
# `query_bits`

Four paths, by the shift `s` (X2): `0` (`b0`, `b3`), below `64` (`b0`, `b1`, `b2`, `b3`), below `128`
(`b0`, `b1`, `b4`, `b5`), else (`b0`, `b1`, `b4`, `b6`); each ends masking with `-1` for a depth
(X3) above `63`, else `!(-1 << depth)`, the low `depth` bits (`mask_eq`).
-/

namespace NativeRustcVmArm.Whir.QueryBits

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.QueryBits NativeVm.Model

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

/-- The code's mask for the depth `d`: all ones above `63`, else `!(-1 << d)`. -/
def maskB (d : BitVec 64) : BitVec 64 :=
  if (!d.ult 63#64 && !d == 63#64) = true then 18446744073709551615#64
  else ~~~(18446744073709551615#64 <<< (d.toNat % 64))

/-- **The mask**: the code's `v & mask` is the model's. -/
theorem and_maskB (v d : UInt64) :
    v.toBitVec &&& maskB d.toBitVec =
      (if 64 ≤ d.toNat then v else v &&& ((1 : UInt64) <<< d.toNat.toUInt64 - 1)).toBitVec := by
  unfold maskB
  by_cases h : 64 ≤ d.toNat
  · have hc : (!d.toBitVec.ult 63#64 && !d.toBitVec == 63#64) = true := by
      have hne : d.toBitVec ≠ 63#64 := fun he ↦ by
        have := congrArg BitVec.toNat he
        simp at this; omega
      simp [BitVec.ult, hne]; omega
    simp only [hc, h, ↓reduceIte,
      show (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
  · have hc : (!d.toBitVec.ult 63#64 && !d.toBitVec == 63#64) = false := by
      by_cases h63 : d.toNat = 63
      · have : d.toBitVec = 63#64 := BitVec.eq_of_toNat_eq (by simp [h63])
        simp [this]
      · simp [BitVec.ult]; omega
    simp only [hc, h, Bool.false_eq_true, ↓reduceIte]
    rw [UInt64.toBitVec_and, mask_toBitVec _ (by omega),
      Nat.mod_eq_of_lt (show d.toBitVec.toNat < 64 by simpa using (by omega : d.toNat < 64)),
      UInt64.toNat_toBitVec, not_shl_eq _ (by omega)]

/-- `lsl x, #1`. -/
theorem evalUBFM_lsl1 (x : BitVec 64) : (evalUBFM (w := .W64) x 63 62 : BitVec 64) = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [evalUBFM, BitVec.toNat_shiftLeft, BitVec.take]
  simp only [show RegWidth.W64.bits = 64 from rfl]
  simp
  omega

/-- `mvn w9, w2` as `lsl`'s amount: `63 - s`. -/
theorem mvn_amount (s : BitVec 64) (h : s.toNat < 64) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 0#64 |||
      ~~~BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 s)))).toNat % 64 =
      63 - s.toNat := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_not, BitVec.toNat_ofNat,
    Nat.zero_mod, Nat.zero_or]
  omega

/-- The model's value, by the shift. -/
theorem queryBits_eq (c : EW) (s d : Nat) :
    queryBits c s d =
      let v : UInt64 :=
        if s = 0 then c.c0
        else if s < 64 then (c.c0 >>> s.toUInt64) ||| (c.c1 <<< (64 - s).toUInt64)
        else if s < 128 then c.c1 >>> (s - 64).toUInt64
        else 0
      if 64 ≤ d then v else v &&& ((1 : UInt64) <<< d.toUInt64 - 1) := rfl

/-- A path's X0: the code's value `e` masked, `e` the model's unmasked value `v`. -/
theorem fin_eq {x v d : UInt64} {e : BitVec 64} (h0 : x.toBitVec = e &&& maskB d.toBitVec)
    (he : e = v.toBitVec) :
    x = if 64 ≤ d.toNat then v else v &&& ((1 : UInt64) <<< d.toNat.toUInt64 - 1) :=
  UInt64.toBitVec_inj.mp (by rw [h0, he, and_maskB])

/-! ## The contract -/

theorem getXReg_X2 (m : MachineData) : m.regs.getXReg .X2 = m.regs.X2 := rfl

theorem ult_ofNat (x : UInt64) {n : Nat} (hn : n < 2 ^ 64) :
    x.toBitVec.ult (BitVec.ofNat 64 n) = decide (x.toNat < n) := by
  simp only [BitVec.ult, UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem beq_zero (x : UInt64) : (x.toBitVec == 0#64) = decide (x = 0) := by
  by_cases h : x = 0
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    exact fun h' ↦ h (UInt64.toBitVec_inj.mp (h'.trans rfl))

variable [Host] {k : Nat}

/-- The entry's environment: no region. -/
abbrev envOf (m : MachineData) : Env := Env.ofMachine m []

/-- **A path's end**: `ret` from a state keeping the callee-saved registers, SP and X30, no write,
X0 the model's value. -/
theorem finish {m : MachineData} {S' : SState} {st : MachineState}
    (hm' : Match (envOf m) S' st.data) {nx : Int64} (hpc : PcOk (envOf m) .ret nx st) (hmem : S'.mem = [])
    (hk : keeps entryS S' = true) (h30 : S'.reg .X30 = some (.reg .X30))
    (hx0 : st.data.regs.X0 = queryBits ⟨m.regs.X0, m.regs.X1⟩ m.regs.X2.toNat m.regs.X3.toNat) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧ QueryBitsPost m st.data) st := by
  have hwf := Env.wf_nil m
  have hm := match_nil m
  have hd := hm'.dmem_eq hwf hmem
  have h30' : st.data.regs.X30 = m.regs.X30 := Match.reg_eq (r := .X30) hm hm' rfl h30
  refine .done _ ⟨?_, hx0, fun p _ ↦ by rw [hd]; rfl, Match.saved hm hm' hwf rfl hk⟩
  simp only [PcOk] at hpc
  rw [hpc]
  simp only [retOf, h30']

/-- **`query_bits`'s contract.** -/
theorem queryBits_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.QueryBits.entryLabel) QueryBitsPre QueryBitsPost := by
  intro m _
  have hentry : Labels.label NativeRustcVmArm.Vm.QueryBits.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.QueryBits.b0Offset) := hp.label (j := NativeRustcVmArm.Vm.QueryBits.entryOffset) NativeRustcVmArm.Vm.QueryBits.entry_at
  rw [hentry]
  have hwf := Env.wf_nil m
  have hm : Match (envOf m) entryS m := match_nil m
  have inf : ∀ {b : List Directive} {j : Nat}, b.IsInfixAt code j → b ≠ [] →
      b.IsInfixAt Host.prog (k + j) := fun hb hne ↦ hb.trans hp.1 hne
  refine exec_then (inf b0_in_code (by simp [b0])) run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have e0 : k + NativeRustcVmArm.Vm.QueryBits.b0Offset + b0.length = k + NativeRustcVmArm.Vm.QueryBits.b1Offset := by rw [Nat.add_assoc, b0_next]
  by_cases hz : m.regs.X2 = 0
  · -- shift `0`: `b3`
    simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, Env.ofMachine_regs, getXReg_X2, beq_zero, hz,
      decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.QueryBits.b3Offset) NativeRustcVmArm.Vm.QueryBits.label_3_at] at hpc1
    refine exec_at (inf b3_in_code (by simp [b3])) (exec_after run_b0 run_b3z) hwf hpc1 hm1
      fun st hm' hpc ↦ finish hm' hpc rfl (by decide) rfl ?_
    have h0 := hm'.regs .X0 _ rfl
    sym_simp at h0
    rw [queryBits_eq]
    simp only [show m.regs.X2.toNat = 0 by simp [hz], ↓reduceIte]
    exact fin_eq (d := m.regs.X3) h0 rfl
  simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, Env.ofMachine_regs, getXReg_X2, beq_zero, hz,
    decide_false, Bool.false_eq_true, ↓reduceIte, e0] at hpc1
  refine exec_at (inf b1_in_code (by simp [b1])) (exec_after run_b0 run_b1) hwf hpc1 hm1
    fun st2 hm2 hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  have e1 : k + NativeRustcVmArm.Vm.QueryBits.b1Offset + b1.length = k + NativeRustcVmArm.Vm.QueryBits.b2Offset := by rw [Nat.add_assoc, b1_next]
  by_cases h64 : m.regs.X2.toNat < 64
  · -- `0 < shift < 64`: `b2`, `b3`
    simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, Env.ofMachine_regs, getXReg_X2,
      ult_ofNat _ (show 64 < 2 ^ 64 by decide), h64, decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, e1] at hpc2
    refine exec_at (inf b2_in_code (by simp [b2])) (exec_after run_b1 run_b2) hwf hpc2 hm2
      fun st3 hm3 hpc3 ↦ ?_
    simp only [PcOk] at hpc3
    have e2 : k + NativeRustcVmArm.Vm.QueryBits.b2Offset + b2.length = k + NativeRustcVmArm.Vm.QueryBits.b3Offset := by rw [Nat.add_assoc, b2_next]
    rw [e2] at hpc3
    refine exec_at (inf b3_in_code (by simp [b3])) (exec_after run_b2 run_b3) hwf hpc3 hm3
      fun st hm' hpc ↦ finish hm' hpc rfl (by decide) rfl ?_
    have h0 := hm'.regs .X0 _ rfl
    sym_simp at h0
    have hs0 : m.regs.X2.toNat ≠ 0 := fun h ↦ hz (UInt64.toNat_inj.mp (by simpa using h))
    rw [queryBits_eq]
    simp only [hs0, h64, ↓reduceIte]
    refine fin_eq (d := m.regs.X3) h0 ?_
    have hx2 : ((Env.ofMachine m []).regs XReg.X2).toNat = m.regs.X2.toNat := rfl
    rw [evalUBFM_lsl1, mvn_amount _ (by rw [hx2]; exact h64), hx2, UInt64.toBitVec_or,
      UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq',
      BitVec.ushiftRight_eq', ← BitVec.shiftLeft_add]
    have ha : ((64 - m.regs.X2.toNat).toUInt64.toBitVec % 64).toNat = 64 - m.regs.X2.toNat := by
      rw [BitVec.toNat_umod]; simp; omega
    have hb : (m.regs.X2.toNat.toUInt64.toBitVec % 64).toNat = m.regs.X2.toNat := by
      rw [BitVec.toNat_umod]; simp; omega
    rw [ha, hb, show 1 + (63 - m.regs.X2.toNat) = 64 - m.regs.X2.toNat by omega,
      Nat.mod_eq_of_lt (show m.regs.X2.toNat < RegWidth.W64.bits from h64), BitVec.or_comm]
    rfl
  simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, Env.ofMachine_regs, getXReg_X2,
    ult_ofNat _ (show 64 < 2 ^ 64 by decide), h64, decide_false, Bool.not_false, ↓reduceIte,
    hp.label (j := NativeRustcVmArm.Vm.QueryBits.b4Offset) NativeRustcVmArm.Vm.QueryBits.label_4_at] at hpc2
  refine exec_at (inf b4_in_code (by simp [b4])) (exec_after run_b1 run_b4) hwf hpc2 hm2
    fun st4 hm4 hpc4 ↦ ?_
  simp only [PcOk] at hpc4
  have e4 : k + NativeRustcVmArm.Vm.QueryBits.b4Offset + b4.length = k + NativeRustcVmArm.Vm.QueryBits.b5Offset := by rw [Nat.add_assoc, b4_next]
  by_cases h128 : m.regs.X2.toNat < 128
  · -- `64 ≤ shift < 128`: `b5`
    simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, Env.ofMachine_regs, getXReg_X2,
      ult_ofNat _ (show 128 < 2 ^ 64 by decide), h128, decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, e4] at hpc4
    refine exec_at (inf b5_in_code (by simp [b5])) (exec_after run_b4 run_b5) hwf hpc4 hm4
      fun st hm' hpc ↦ finish hm' hpc rfl (by decide) rfl ?_
    have h0 := hm'.regs .X0 _ rfl
    sym_simp at h0
    rw [queryBits_eq]
    have hs0 : m.regs.X2.toNat ≠ 0 := by omega
    simp only [hs0, h64, h128, ↓reduceIte]
    refine fin_eq (d := m.regs.X3) h0 ?_
    have hx2 : ((Env.ofMachine m []).regs XReg.X2).toNat = m.regs.X2.toNat := rfl
    have ha : ((m.regs.X2.toNat - 64).toUInt64.toBitVec % 64).toNat = m.regs.X2.toNat - 64 := by
      rw [BitVec.toNat_umod]; simp; omega
    rw [hx2, UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', ha,
      show m.regs.X2.toNat % RegWidth.W64.bits = m.regs.X2.toNat - 64 by
        show m.regs.X2.toNat % 64 = _; omega]
    rfl
  · -- `128 ≤ shift`: `b6`
    simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, Env.ofMachine_regs, getXReg_X2,
      ult_ofNat _ (show 128 < 2 ^ 64 by decide), h128, decide_false, Bool.not_false, ↓reduceIte,
      hp.label (j := NativeRustcVmArm.Vm.QueryBits.b6Offset) NativeRustcVmArm.Vm.QueryBits.label_6_at] at hpc4
    refine exec_at (inf b6_in_code (by simp [b6])) (exec_after run_b4 run_b6) hwf hpc4 hm4
      fun st hm' hpc ↦ finish hm' hpc rfl (by decide) rfl ?_
    have h0 := hm'.regs .X0 _ rfl
    sym_simp at h0
    rw [queryBits_eq]
    have hs0 : m.regs.X2.toNat ≠ 0 := by omega
    simp only [hs0, h64, h128, ↓reduceIte]
    exact fin_eq (d := m.regs.X3) h0 rfl

end

end NativeRustcVmArm.Whir.QueryBits
