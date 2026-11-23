module

public import NativeRustcVmArm.Code.Vm.SubspaceTable.Names
public import NativeRustcVmArm.Whir.SubspaceTable.Inv

/-!
# `subspace_table`'s layer initialization

The layer's word `i` becomes `2^(i+1)`: four words a turn in the unrolled loop (`b7`, `vec_step`,
from `VInv j` to `VInv (j + 1)` or `VDone`), then one a turn (`b10`, `tail_step`, from `TInv i` to
`TInv (i + 1)` or `Init μ`).
-/

namespace NativeRustcVmArm.Whir.SubspaceTable

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region WordAt WordsAt)

public section

/-- `c << i` for `c = 2^(r+1)`: the layer's word `i + r`. -/
theorem lslv_pow2 {x y : BitVec 64} {r i : Nat} (hx : x = BitVec.ofNat 64 (2 ^ (r + 1)))
    (hy : y.toNat = i) (hi : i < 64) :
    UInt64.ofBitVec (x <<< (y.toNat % 64)) = pow2 (i + r) := by
  apply UInt64.toBitVec_inj.mp
  rw [hy, Nat.mod_eq_of_lt hi, hx]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, pow2,
    Nat.toUInt64]
  rw [Nat.mod_mul_mod, ← Nat.pow_add]
  congr 2
  omega

theorem addr3 (b : BitVec 64) {x y z w : Nat} (h : x + y = z + w) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 z + BitVec.ofNat 64 w := by
  rw [addr_add, addr_add, h]

theorem initL_getElem {i k : Nat} (hk : k < (initL i).length) :
    (initL i)[k] = if k < i then pow2 k else 0 := by
  simp [initL]

variable [Host] {k : Nat}

/-- **A turn of the unrolled initialization.** -/
theorem vec_step (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 subspaceTableStack)
    {j : Nat} {st : MachineData} (hV : VInv m0 j st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (VInv m0 (j + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b7Offset)) ∨
        (VDone m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b8Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b7Offset)⟩ := by
  have hF : 864 ≤ subspaceTableStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfb : (fbOf m0).toNat + 864 ≤ 2 ^ 64 := hfnw
  have hI := hV.init
  have hmu := hI.hmu
  have hj := hV.hj
  have hn4 := n4Of_le m0
  have hn4m : n4Of m0 % 4 = 0 := by unfold n4Of; omega
  let ba := fbOf m0 + BitVec.ofNat 64 (16 + 32 * j)
  have hk7 : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b7Offset) := b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hrd : Readable st ba 32 := hI.fr.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega))
  let env := Env.ofMachine st [(ba, 32)]
  have hwf : env.WF := wf_one hrd.1 hrd.2
  have hm : Match env vecS st := match_one (by
    show st.regs.X11.toBitVec = ba + BitVec.ofInt 64 16
    rw [hV.x11]
    show _ = fbOf m0 + BitVec.ofNat 64 (16 + 32 * j) + BitVec.ofNat 64 16
    rw [addr_add]
    congr 2
    omega)
  refine exec_then hk7 run_b7 hwf hm fun s1 hm1 hpc1 ↦ ?_
  have hb7 := after_eq run_b7 ▸ b7_keeps
  have hsame := same_region hm1 hwf (r := 0) rfl hb7.2
  have hfr1 := hI.fr.of_block hm hm1 hwf rfl hb7.1 (r := 0) rfl le_rfl hb7.2
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 16 + 32 * j) (n := 32) (by omega) h))
    (fun q hq i hi ↦ not_inRange_slot hS hF (o := 16 + 32 * j) (n := 32) (by omega)
      (slots_le q hq) hi (.inl (by have := slots_ge q hq; omega)))
  have hbnw : NativeRustcVm.NoWrap ba 32 := NativeRustcVm.NoWrap.sub hfnw (by omega)
  have h12 : (st.regs.X12.toBitVec - BitVec.ofNat 64 1).toNat = 4 * j := by
    rw [toNat_sub_ofNat (by have := hV.x12; show 1 ≤ st.regs.X12.toNat; omega)]
    have := hV.x12
    show st.regs.X12.toNat - 1 = _
    omega
  -- the four words
  have hw : ∀ r < 4, WordAt s1.data.dmem (ba + BitVec.ofNat 64 (8 * r)) (pow2 (4 * j + r)) := by
    intro r hr
    have hj4 : 4 * j < 64 := by omega
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl
    · have := Match.wordAt_write hm1 (r := 0) (o := 0) rfl (by decide)
        (v := .bin .lslv .W64 (.reg .X13) (.bin .sub .W64 (.reg .X12) (.lit 1))) (by decide)
      convert this using 1
      sym_simp
      exact (lslv_pow2 (by show st.regs.X13.toBitVec = _; rw [hV.x13]; rfl) h12 hj4).symm
    · have := Match.wordAt_write hm1 (r := 0) (o := 8) rfl (by decide)
        (v := .bin .lslv .W64 (.reg .X14) (.bin .sub .W64 (.reg .X12) (.lit 1))) (by decide)
      convert this using 1
      sym_simp
      exact (lslv_pow2 (by show st.regs.X14.toBitVec = _; rw [hV.x14]; rfl) h12 hj4).symm
    · have := Match.wordAt_write hm1 (r := 0) (o := 16) rfl (by decide)
        (v := .bin .lslv .W64 (.reg .X15) (.bin .sub .W64 (.reg .X12) (.lit 1))) (by decide)
      convert this using 1
      sym_simp
      exact (lslv_pow2 (by show st.regs.X15.toBitVec = _; rw [hV.x15]; rfl) h12 hj4).symm
    · have := Match.wordAt_write hm1 (r := 0) (o := 24) rfl (by decide)
        (v := .bin .lslv .W64 (.reg .X16) (.bin .sub .W64 (.reg .X12) (.lit 1))) (by decide)
      convert this using 1
      sym_simp
      exact (lslv_pow2 (by show st.regs.X16.toBitVec = _; rw [hV.x16]; rfl) h12 hj4).symm
  have hlay : WordsAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (initL (4 * (j + 1))) := by
    refine wordsAt_update (lo := 4 * j) (n := 4) hI.layer ?_
      (NativeRustcVm.NoWrap.sub hfnw (by rw [initL_length]; omega)) (by rw [initL_length]; omega)
      (by rw [initL_length, initL_length]) (fun i hi hout ↦ ?_) (fun i hi h1 h2 ↦ ?_)
    · rw [addr_add, show 16 + 8 * (4 * j) = 16 + 32 * j by omega]
      exact hsame
    · rw [initL_getElem, initL_getElem]
      by_cases h : i < 4 * j
      · simp [h, show i < 4 * (j + 1) by omega]
      · simp [h, show ¬i < 4 * (j + 1) by omega]
    · rw [initL_getElem, ite_eq_left (by omega)]
      have := hw (i - 4 * j) (by omega)
      rw [show 4 * j + (i - 4 * j) = i by omega] at this
      rw [addr3 _ (show 16 + 8 * i = (16 + 32 * j) + 8 * (i - 4 * j) by omega)]
      exact this
  have hout : WordAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 8) m0.regs.X0 :=
    NativeRustcVm.BytesAt.of_sameOutside_apart hI.out hsame (by
      unfold NativeRustcVm.Apart
      rw [NativeRustcVm.length_wordBytes, toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
      omega) (NativeRustcVm.NoWrap.sub hfnw (by rw [NativeRustcVm.length_wordBytes]; omega)) hbnw
  have e : ∀ r ∈ [XReg.X8, .X9, .X10, .X13, .X14, .X15, .X16, .X20, .X21, .X24],
      s1.data.regs.getXReg r = st.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq hm hm1 rfl rfl
  have hI1 : Init m0 (4 * (j + 1)) s1.data :=
    ⟨hfr1, hout, hlay, (e .X20 (by simp)).trans hI.x20,
      by rw [show s1.data.regs.X21 = st.regs.X21 from e .X21 (by simp)]; exact hI.x21,
      by rw [show s1.data.regs.X24 = st.regs.X24 from e .X24 (by simp)]; exact hI.x24, hmu⟩
  have h17 : st.regs.X17.toNat = n4Of m0 - 4 * j := hV.x17
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  simp only [bv_beq_toNat] at hpc1
  rw [show (env.regs .X17).toNat = n4Of m0 - 4 * j from h17] at hpc1
  by_cases hlast : n4Of m0 - 4 * j = 4
  · simp only [hlast, BitVec.toNat_ofNat, show 4 % 2 ^ 64 = 4 from rfl, decide_true,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine .done _ (.inr ⟨⟨by rw [show n4Of m0 = 4 * (j + 1) by omega]; exact hI1, ?_, ?_, ?_⟩,
      hpc1⟩)
    · rw [show s1.data.regs.X8 = st.regs.X8 from e .X8 (by simp)]; exact hV.x8
    · rw [show s1.data.regs.X9 = st.regs.X9 from e .X9 (by simp)]; exact hV.x9
    · rw [show s1.data.regs.X10 = st.regs.X10 from e .X10 (by simp)]; exact hV.x10
  · have hne : decide (n4Of m0 - 4 * j = (BitVec.ofNat 64 4).toNat) = false := by
      rw [decide_eq_false_iff_not, BitVec.toNat_ofNat]
      omega
    simp only [hne, Bool.not_false, ↓reduceIte] at hpc1
    have hl : Labels.label NativeRustcVmArm.Vm.SubspaceTable.label_6 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b7Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceTable.b7Offset) NativeRustcVmArm.Vm.SubspaceTable.label_6_at
    refine .done _ (.inl ⟨⟨hI1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩, hpc1.trans hl⟩)
    · rw [show s1.data.regs.X8 = st.regs.X8 from e .X8 (by simp)]; exact hV.x8
    · rw [show s1.data.regs.X9 = st.regs.X9 from e .X9 (by simp)]; exact hV.x9
    · rw [show s1.data.regs.X10 = st.regs.X10 from e .X10 (by simp)]; exact hV.x10
    · show (s1.data.regs.getXReg .X11).toBitVec = _
      rw [hm1.regs .X11 _ rfl]
      simp only [Sym.eval]
      show ba + BitVec.ofInt 64 48 = _
      rw [show BitVec.ofInt 64 48 = BitVec.ofNat 64 48 from rfl, addr_add]
      congr 2
      omega
    · show (s1.data.regs.getXReg .X12).toBitVec.toNat = _
      rw [hm1.regs .X12 _ rfl]
      sym_simp
      show (st.regs.X12.toBitVec + BitVec.ofNat 64 4).toNat = _
      have := hV.x12
      rw [toNat_add_ofNat' (by show st.regs.X12.toNat + 4 < _; omega)]
      show st.regs.X12.toNat + 4 = _
      omega
    · rw [show s1.data.regs.X13 = st.regs.X13 from e .X13 (by simp)]; exact hV.x13
    · rw [show s1.data.regs.X14 = st.regs.X14 from e .X14 (by simp)]; exact hV.x14
    · rw [show s1.data.regs.X15 = st.regs.X15 from e .X15 (by simp)]; exact hV.x15
    · rw [show s1.data.regs.X16 = st.regs.X16 from e .X16 (by simp)]; exact hV.x16
    · show (s1.data.regs.getXReg .X17).toBitVec.toNat = _
      rw [hm1.regs .X17 _ rfl]
      sym_simp
      show (st.regs.X17.toBitVec - BitVec.ofNat 64 4).toNat = _
      rw [toNat_sub_ofNat (by show 4 ≤ st.regs.X17.toNat; omega)]
      show st.regs.X17.toNat - 4 = _
      omega

/-- **A turn of the word-by-word initialization.** -/
theorem tail_step (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 subspaceTableStack)
    {i : Nat} {st : MachineData} (hT : TInv m0 i st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (TInv m0 (i + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b10Offset)) ∨
        (Init m0 (muOf m0) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b11Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b10Offset)⟩ := by
  have hF : 864 ≤ subspaceTableStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfb : (fbOf m0).toNat + 864 ≤ 2 ^ 64 := hfnw
  have hI := hT.init
  have hmu := hI.hmu
  have hi := hT.hi
  let ba := fbOf m0 + BitVec.ofNat 64 (16 + 8 * i)
  have hk10 : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b10Offset) := b10_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hrd : Readable st ba 8 := hI.fr.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega))
  let env := Env.ofMachine st [(ba, 8)]
  have hwf : env.WF := wf_one hrd.1 hrd.2
  have hm : Match env tailS st := match_one (by
    show st.regs.X9.toBitVec = ba + BitVec.ofInt 64 0
    rw [hT.x9]
    simp [ba])
  refine exec_then hk10 run_b10 hwf hm fun s1 hm1 hpc1 ↦ ?_
  have hb10 := after_eq run_b10 ▸ b10_keeps
  have hsame := same_region hm1 hwf (r := 0) rfl hb10.2
  have hfr1 := hI.fr.of_block hm hm1 hwf rfl hb10.1 (r := 0) rfl le_rfl hb10.2
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 16 + 8 * i) (n := 8) (by omega) h))
    (fun q hq j hj ↦ not_inRange_slot hS hF (o := 16 + 8 * i) (n := 8) (by omega)
      (slots_le q hq) hj (.inl (by have := slots_ge q hq; omega)))
  have hbnw : NativeRustcVm.NoWrap ba 8 := NativeRustcVm.NoWrap.sub hfnw (by omega)
  have hw : WordAt s1.data.dmem ba (pow2 i) := by
    have := Match.wordAt_write hm1 (r := 0) (o := 0) rfl (by decide)
      (v := .bin .lslv .W64 (.reg .X11) (.reg .X8)) (by decide)
    rw [NativeRustcVm.addr_add_zero] at this
    convert this using 1
    sym_simp
    exact (lslv_pow2 (r := 0) (by show st.regs.X11.toBitVec = _; rw [hT.x11]; rfl) hT.x8
      (by omega)).symm
  have hlay : WordsAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (initL (i + 1)) := by
    rw [← initL_set]
    refine NativeRustcVm.WordsAt.set hI.layer (by rw [addr_add]; exact hw) ?_
      (by rw [initL_length]; omega) (NativeRustcVm.NoWrap.sub hfnw (by rw [initL_length]; omega))
    rw [addr_add]
    exact hsame
  have hout : WordAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 8) m0.regs.X0 :=
    NativeRustcVm.BytesAt.of_sameOutside_apart hI.out hsame (by
      unfold NativeRustcVm.Apart
      rw [NativeRustcVm.length_wordBytes, toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
      omega) (NativeRustcVm.NoWrap.sub hfnw (by rw [NativeRustcVm.length_wordBytes]; omega)) hbnw
  have e : ∀ r ∈ [XReg.X10, .X11, .X20, .X21, .X24],
      s1.data.regs.getXReg r = st.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  have hI1 : Init m0 (i + 1) s1.data :=
    ⟨hfr1, hout, hlay, (e .X20 (by simp)).trans hI.x20,
      by rw [show s1.data.regs.X21 = st.regs.X21 from e .X21 (by simp)]; exact hI.x21,
      by rw [show s1.data.regs.X24 = st.regs.X24 from e .X24 (by simp)]; exact hI.x24, hmu⟩
  have h9 : (s1.data.regs.getXReg .X9).toBitVec = fbOf m0 + BitVec.ofNat 64 (16 + 8 * (i + 1)) := by
    rw [hm1.regs .X9 _ rfl]
    simp only [Sym.eval]
    show ba + BitVec.ofInt 64 8 = _
    rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add]
    congr 2
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  simp only [bv_beq_toNat] at hpc1
  have hx10 : (env.regs .X10).toNat = (fbOf m0).toNat + (16 + 8 * muOf m0) := by
    show st.regs.X10.toBitVec.toNat = _
    rw [hT.x10, toNat_add_ofNat' (by omega)]
  have hb : (env.base 0 + BitVec.ofInt 64 8).toNat = (fbOf m0).toNat + (16 + 8 * (i + 1)) := by
    show (ba + BitVec.ofNat 64 8).toNat = _
    rw [addr_add, toNat_add_ofNat' (by omega)]
    omega
  rw [hx10, hb] at hpc1
  by_cases hlast : i + 1 = muOf m0
  · simp only [hlast, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact .done _ (.inr ⟨hlast ▸ hI1, hpc1⟩)
  · have hne : decide ((fbOf m0).toNat + (16 + 8 * (i + 1)) =
        (fbOf m0).toNat + (16 + 8 * muOf m0)) = false := by
      rw [decide_eq_false_iff_not]
      omega
    simp only [hne, Bool.not_false, ↓reduceIte] at hpc1
    have hl : Labels.label NativeRustcVmArm.Vm.SubspaceTable.label_9 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b10Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceTable.b10Offset) NativeRustcVmArm.Vm.SubspaceTable.label_9_at
    refine .done _ (.inl ⟨⟨hI1, ?_, h9, ?_, ?_, by omega⟩, hpc1.trans hl⟩)
    · show (s1.data.regs.getXReg .X8).toBitVec.toNat = _
      rw [hm1.regs .X8 _ rfl]
      sym_simp
      show (st.regs.X8.toBitVec + BitVec.ofNat 64 1).toNat = _
      rw [toNat_add_ofNat' (by rw [show st.regs.X8.toBitVec.toNat = i from hT.x8]; omega)]
      rw [show st.regs.X8.toBitVec.toNat = i from hT.x8]
    · rw [show s1.data.regs.X10 = st.regs.X10 from e .X10 (by simp)]; exact hT.x10
    · rw [show s1.data.regs.X11 = st.regs.X11 from e .X11 (by simp)]; exact hT.x11

end

end NativeRustcVmArm.Whir.SubspaceTable
