module

public import NativeRustcVmArm.Code.Vm.PaddingWeight.Names
public import NativeRustcVmArm.Bus.AccumulateSide.LoopEnv

/-!
# `accumulate_side`: padding weight and the next turn's running ones
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

@[expose] def Qkept : List (Sym × Nat) :=
  [(.reg .X19, 101), (.reg .X20, 12), (.reg .X23, 94), (.reg .X24, 95), (.reg .X25, 23),
    (.reg .X26, 13), (.reg .X29, 100), (.load 0 120 8, 92), (.load 0 128 8, 93)] ++ DLf0

@[expose] def Qnew : List (Sym × Nat) :=
  [(.reg .X21, 102), (.reg .X22, 104), (.reg .X27, 198), (.reg .X28, 199),
    (.load 0 136 8, 190), (.load 0 144 8, 191)]

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

private theorem eval_ite_true {env : Env} {c : SBool} {a b : Sym} (hc : SBool.eval env c = true) :
    (Sym.ite c a b).eval env = a.eval env := by simp only [Sym.eval, hc, ↓reduceIte]

private theorem eval_min (env : Env) (a b : Sym) :
    ((Sym.ite (.cmp .ult .W64 a b) a b).eval env).toNat = min (a.eval env).toNat (b.eval env).toNat := by
  by_cases h : (a.eval env).toNat < (b.eval env).toNat
  · simp [Sym.eval, SBool.eval, CmpOp.apply, low_W64, BitVec.ult, h, Nat.min_eq_left (Nat.le_of_lt h)]
  · simp [Sym.eval, SBool.eval, CmpOp.apply, low_W64, BitVec.ult, h, Nat.min_eq_right (Nat.le_of_not_gt h)]

/-- **`b33`**: read the owner's height and rows, update the running ones, and call `padding_weight`. -/
theorem turn33 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hpw : Spec (Labels.label NativeRustcVmArm.Vm.PaddingWeight.entryLabel) PaddingWeightPre PaddingWeightPost)
    {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) L32 m) {g : FormW}
    (hg : FormBufAt m.dmem (base m0 F + BitVec.ofNat 64 152) g) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm j) L34 m2 →
      FormBufAt m2.dmem (base m0 F + BitVec.ofNat 64 152) g → KeepF m0 m m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b34Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b33Offset)⟩ := by
  have hh := St.lift (D := L32) hst (by decide) 0 [(m0.regs.X5.toBitVec, 120)]
  have hwf := wf1 h hst.fr.kept (layout_ok h)
  have hol : (blk (BA L rows bl) j).owner < 6 := by
    rw [blk_eq hj]
    exact (h.bown bl[j] (List.getElem_mem hj)).1
  have height : (Sym.loadx 1 24 (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X20)) 8).eval
      (Env.ofMachine m [(base m0 F, F + 0), (m0.regs.X5.toBitVec, 120)]) =
      (blk (BA L rows bl) j).logRows.toUInt64.toBitVec := by
    rw [layout_load h hj hst (by omega), ht_word h hol, blk_eq hj]
    rfl
  have rowCount : (Sym.loadx 1 72 (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X20)) 8).eval
      (Env.ofMachine m [(base m0 F, F + 0), (m0.regs.X5.toBitVec, 120)]) =
      (blk (BA L rows bl) j).rows.toUInt64.toBitVec := by
    rw [layout_load h hj hst (by omega), rw_word h hol, blk_eq hj]
    rfl
  have hheight : (blk (BA L rows bl) j).logRows ≤ 30 := by
    rw [blk_eq hj]
    exact ht_le h _
  have h21 : (Env.ofMachine m [(base m0 F, F + 0), (m0.regs.X5.toBitVec, 120)]).regs .X21 =
      (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * (blk (BA L rows bl) j).owner + 4) 0).toBitVec :=
    Holds.evc hh (s := .reg .X21) (i := 102) (by decide)
  have h22 : (Env.ofMachine m [(base m0 F, F + 0), (m0.regs.X5.toBitVec, 120)]).regs .X22 =
      (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * (blk (BA L rows bl) j).owner + 3) 0).toBitVec :=
    Holds.evc hh (s := .reg .X22) (i := 103) (by decide)
  have hguard := padding_guard hol h21 h22
  have haddr := padding_addr hol h22
  refine St.runCallK h (.inl rfl) (sz := [12096, 120]) rfl
    (b33_in_code.trans hp.1 (by simp [b33])) run_b33 hst.fr hh hwf (matchQ h hj hst)
    rfl (by decide) (D' := Qkept) (E := Qnew) (by decide) (by decide)
    (fun st hm' p hp' ↦ ?_) (N' := paddingWeightStack) le_pw (by decide) hpw
    (fun st hm' hst' ↦ ?_) (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1
      (fun _ h ↦ h.elim (fun h ↦ by unfold InRange at h; omega) id), hq.2.2⟩)
    fun st m2 hm' hst' hst2 hq hF hB ↦ ?_
  · simp only [Qnew, List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [tval_reg_of hm' rfl, eval_ite_true hguard]
      exact hh (.reg .X21, 102) (by decide)
    · rw [tval_reg_of hm' rfl, eval_ite_true hguard, haddr]
      rfl
    · rw [tval_reg_of hm' rfl]
      change UInt64.ofBitVec (BinOp.apply .add .W64 ((Sym.reg .X27).eval _) (BitVec.ofNat 64 16)) = _
      rw [Holds.evc hh (s := .reg .X27) (i := 98) (by decide)]
      apply UInt64.toBitVec_inj.mp
      simp only [BinOp.apply, low_W64, ext_W64]
      change (m0.regs.X6.toBitVec + BitVec.ofNat 64 (80 + 16 * j)) + BitVec.ofNat 64 16 =
        m0.regs.X6.toBitVec + BitVec.ofNat 64 (80 + 16 * (j + 1))
      rw [NativeRustcVm.addr_add_add]
      congr 1
    · rw [tval_reg_of hm' rfl]
      change UInt64.ofBitVec (BinOp.apply .add .W64 ((Sym.reg .X28).eval _) (BitVec.ofNat 64 16)) = _
      rw [Holds.evc hh (s := .reg .X28) (i := 99) (by decide)]
      apply UInt64.toBitVec_inj.mp
      simp only [BinOp.apply, low_W64, ext_W64]
      change (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 + 16 * j)) + BitVec.ofNat 64 16 =
        m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 + 16 * (j + 1))
      rw [NativeRustcVm.addr_add_add]
      congr 1
    · rw [tval_write hm' rfl rfl (by decide) (by intro i hi; interval_cases i <;> rfl), ofBitVec_eor]
      change tval _ m (.reg .X23) ^^^ tval _ m (.load 0 136 8) = _
      rw [hh (.reg .X23, 94) (by decide), hh (.load 0 136 8, 90) (by decide)]
      change (tsl SL m0 j).c0 ^^^ (onesT SL (ptA m0) j).c0 = (onesT SL (ptA m0) (j + 1)).c0
      rw [onesT_succ, add_c0]
      exact UInt64.xor_comm _ _
    · rw [tval_write hm' rfl rfl (by decide) (by intro i hi; interval_cases i <;> rfl), ofBitVec_eor]
      change tval _ m (.reg .X24) ^^^ tval _ m (.load 0 144 8) = _
      rw [hh (.reg .X24, 95) (by decide), hh (.load 0 144 8, 91) (by decide)]
      change (tsl SL m0 j).c1 ^^^ (onesT SL (ptA m0) j).c1 = (onesT SL (ptA m0) (j + 1)).c1
      rw [onesT_succ, add_c1]
      exact UInt64.xor_comm _ _
  all_goals
    have e0 : st.regs.X0 = stackArg m0 40 := by
      change st.regs.getXReg .X0 = _
      exact argv (sz := [12096, 120]) rfl hh hm' (r := .X0) (a := 12) (by decide)
    have e1 : st.regs.X1.toNat = min (blk (BA L rows bl) j).logRows (stackArg m0 48).toNat := by
      change (st.regs.getXReg .X1).toBitVec.toNat = _
      rw [hm'.regs .X1 _ rfl, eval_min, height,
        Holds.evc hh (s := .load 0 112 8) (i := 13) (by decide)]
      change min (blk (BA L rows bl) j).logRows.toUInt64.toNat (stackArg m0 48).toNat = _
      rw [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
    have e2 : st.regs.X2.toNat = (blk (BA L rows bl) j).rows % 2 ^ 64 := by
      change (st.regs.getXReg .X2).toBitVec.toNat = _
      rw [hm'.regs .X2 _ rfl, rowCount]
      change (blk (BA L rows bl) j).rows.toUInt64.toNat = _
      rw [Nat.toUInt64, UInt64.toNat_ofNat']
  · refine ⟨hst'.fr.stackOk h.stack (by decide) le_pw, ?_, ?_⟩
    · rw [e1]
      have := h.pn
      omega
    · have hs : SliceOk st (stackArg m0 40) (stackArg m0 48) paddingWeightStack :=
        ⟨Bus.Fr.readable hst'.fr h.pt.1, Bus.Fr.offStack hst'.fr h.stack h.pt.2 le_pw⟩
      rw [e0]
      obtain ⟨⟨hm, hn⟩, ho⟩ := hs
      refine ⟨⟨fun i hi ↦ hm i (by rw [e1] at hi; omega), ?_⟩, ?_⟩
      · unfold NoWrap at hn ⊢
        rw [e1]
        omega
      · unfold OffStack Apart at ho ⊢
        rw [e1]
        omega
  · have hr : ewRet m2 = pw m0 (BA L rows bl) j := by
      rw [hq.1, e0, slice_low e1, pt_eq h hst'.fr, e2]
      apply paddingWeight_mod64
      have hp := h.pn
      have hs : (ptA m0).size = (stackArg m0 48).toNat := by simp [ptA, slice, NativeRustcVm.ewsOf]
      simp only [Array.size_extract, hs]
      omega
    rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b33Offset + b33.length = k + NativeRustcVmArm.Vm.AccumulateSide.b34Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b33_next]]
    exact cont m2 ⟨hst2.fr, holds_ewRet (r0 := 106) (Holds.sub hst2.hd
      (D' := (Sym.reg .X23, 94) :: (Sym.reg .X24, 95) :: L34c) (by decide)) hr rfl rfl⟩
      (NativeRustcVm.Tables.FormBufAt.of_same hg (hB 152 5928 (by decide) (by decide))) hF

end

end NativeRustcVmArm.Bus.AccumulateSide
