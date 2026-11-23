module

public import NativeRustcVmArm.Code.Vm.FormBufAddScaled.Names
public import NativeRustcVmArm.Bus.AccumulateSide.LoopUpdate

/-!
# `accumulate_side`: adding the block form to its owner's form
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

@[expose] def Tkept : List (Sym × Nat) :=
  [(.reg .X20, 96), (.reg .X23, 94), (.reg .X24, 95), (.reg .X27, 98), (.reg .X28, 99),
    (.reg .X29, 100)] ++ DLf

@[expose] def Tnew : List (Sym × Nat) :=
  [(.reg .X19, 101), (.reg .X21, 102), (.reg .X22, 103), (.reg .X25, 23),
    (.load 0 120 8, 92), (.load 0 128 8, 93)]

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

private theorem eval_true {env : Env} {c : SBool} {a b : Sym} (hc : SBool.eval env c = true) :
    (Sym.ite c a b).eval env = a.eval env := by simp only [Sym.eval, hc, ↓reduceIte]

/-- **`b31`**: the owner's form is updated and the block form stays intact. -/
theorem turn31 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (has : ∀ f g, Spec (Labels.label NativeRustcVmArm.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f g) (FormBufAddScaledPost f g))
    {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) L31 m)
    (hg : FormBufAt m.dmem (base m0 F + BitVec.ofNat 64 152) (gf m0 (BA L rows bl) j))
    (hG : FormsAt m.dmem m0.regs.X1.toBitVec (sta SL m0 (BA L rows bl) Fm j).1)
    {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm j) L32 m2 → m2.regs.X0 = 1 →
      FormBufAt m2.dmem (base m0 F + BitVec.ofNat 64 152) (gf m0 (BA L rows bl) j) →
      FormsAt m2.dmem m0.regs.X1.toBitVec (sta SL m0 (BA L rows bl) Fm (j + 1)).1 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b32Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b31Offset)⟩ := by
  have hh := St.lift (D := L31) hst (by decide) 0 [(NativeRustcVmArm.rodataAddr .tables, 240)]
  have hwf := wf1 h hst.fr.kept (tables_ok h)
  have hol : (blk (BA L rows bl) j).owner < 6 := by
    rw [blk_eq hj]
    exact (h.bown bl[j] (List.getElem_mem hj)).1
  have hlen : tval [(base m0 F, F + 0), (NativeRustcVmArm.rodataAddr .tables, 240)] m (.load 0 152 8) =
      (gf m0 (BA L rows bl) j).size.toUInt64 := tval_load rfl hg.len
  have hsize := hg.len_le
  change (gf m0 (BA L rows bl) j).size ≤ 148 at hsize
  have hcmp : SBool.eval (Env.ofMachine m [(base m0 F, F + 0), (NativeRustcVmArm.rodataAddr .tables, 240)])
      (.cmp .ult .W64 (.load 0 152 8) (.lit 149)) = true := by
    have he := congrArg UInt64.toBitVec hlen
    change (Sym.load 0 152 8).eval _ = _ at he
    rw [cmp_ult_lit _ he (by decide : 149 < 2 ^ 64)]
    simp only [Nat.toUInt64, UInt64.toNat_ofNat_of_lt'
      (by unfold UInt64.size; omega : (gf m0 (BA L rows bl) j).size < UInt64.size)]
    simp only [decide_eq_true_eq]
    omega
  have howner : (Sym.reg .X20).eval (Env.ofMachine m
      [(base m0 F, F + 0), (NativeRustcVmArm.rodataAddr .tables, 240)]) =
      BitVec.ofNat 64 (blk (BA L rows bl) j).owner := Holds.evc hh (i := 96) (by decide)
  have hok := slot_ok h hol
  obtain ⟨hshape, hrow⟩ := sta_shape h j
  have ho : (blk (BA L rows bl) j).owner < (sta SL m0 (BA L rows bl) Fm j).1.size := by omega
  have hs : m0.regs.X2.toNat < (sta SL m0 (BA L rows bl) Fm j).1[(blk (BA L rows bl) j).owner].size := by
    rw [hrow _ ho]
    exact h.side
  refine St.runCall h (A := 0) (sz := [12096, 240]) rfl
    (b31_in_code.trans hp.1 (by simp [b31])) run_b31 hst.fr hh hwf (matchT h hj hst) rfl
    (by decide) (D' := Tkept) (E := Tnew) (by decide) (by decide)
    (fun st hm' p hp' ↦ ?_) (N' := formBufAddScaledStack) (lo := 0) (n := 0) le_as
    (by decide) (by decide) (has (slotOf (sta SL m0 (BA L rows bl) Fm j).1
      (blk (BA L rows bl) j).owner m0.regs.X2.toNat) (gf m0 (BA L rows bl) j))
    (fun st hm' hst' ↦ ?_) (fun st m2 hm' hq ↦ ?_)
    fun st m2 hm' hst' hst2 hq _ ↦ ?_
  · simp only [Tnew, List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [tval_reg_of hm' rfl, eval_true hcmp]
      exact hlen
    · rw [tval_reg_of hm' rfl, tab_sel _ _ 32 hol howner, table_load h hst.fr hol (by decide : 4 < 5)]
      rfl
    · rw [tval_reg_of hm' rfl, tab_sel _ _ 24 hol howner, table_load h hst.fr hol (by decide : 3 < 5)]
      rfl
    · rw [tval_reg_of hm' rfl, eval_true hcmp]
      exact hh (.load 0 80 8, 23) (by decide)
    · rw [tval_write hm' rfl rfl (by decide) (by intro i hi; interval_cases i <;> rfl)]
      exact hh (.reg .X22, 92) (by decide)
    · rw [tval_write hm' rfl rfl (by decide) (by intro i hi; interval_cases i <;> rfl)]
      exact hh (.reg .X21, 93) (by decide)
  all_goals
    have e0 : st.regs.X0.toBitVec = m0.regs.X1.toBitVec +
        BitVec.ofNat 64 (formBufBytes * (3 * (blk (BA L rows bl) j).owner + m0.regs.X2.toNat)) := by
      change (st.regs.getXReg .X0).toBitVec = _
      rw [hm'.regs .X0 _ rfl]
      change BinOp.apply .add .W64 (BinOp.apply .mul .W64 ((Sym.reg .X20).eval _)
        (BitVec.ofNat 64 17784)) ((Sym.load 0 56 8).eval _) = _
      rw [howner, Holds.evc hh (s := .load 0 56 8) (i := 22) (by decide)]
      rw [TT_sv (by decide)]
      change BinOp.apply .add .W64 (BinOp.apply .mul .W64
        (BitVec.ofNat 64 (blk (BA L rows bl) j).owner) (BitVec.ofNat 64 17784))
        (m0.regs.X2 * 5928 + m0.regs.X1).toBitVec = _
      simpa only [BinOp.apply, low_W64, ext_W64, UInt64.toBitVec_add, UInt64.toBitVec_mul,
        show (5928 : UInt64).toBitVec = 5928#64 by decide +kernel] using
        slot_addr (a := m0.regs.X1.toBitVec) (x2 := m0.regs.X2.toBitVec)
          (o := (blk (BA L rows bl) j).owner) (s := m0.regs.X2.toNat) rfl
    have e1 : st.regs.X1.toBitVec = base m0 F + BitVec.ofNat 64 160 := by
      change (st.regs.getXReg .X1).toBitVec = _
      rw [hm'.regs .X1 _ rfl, eval_true hcmp, Holds.evc hh (s := .load 0 80 8) (i := 23) (by decide)]
      rfl
    have e2 : st.regs.X2.toNat = (gf m0 (BA L rows bl) j).size := by
      change (st.regs.getXReg .X2).toBitVec.toNat = _
      rw [hm'.regs .X2 _ rfl, eval_true hcmp]
      have he := congrArg UInt64.toNat hlen
      change ((Sym.load 0 152 8).eval _).toNat = _ at he
      rw [he]
      exact UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
    have e3 : st.regs.X3 = (tsl SL m0 j).c0 := argv (sz := [12096, 240]) rfl hh hm'
      (r := .X3) (a := 94) (by decide)
    have e4 : st.regs.X4 = (tsl SL m0 j).c1 := argv (sz := [12096, 240]) rfl hh hm'
      (r := .X4) (a := 95) (by decide)
  · have hbuf := NativeRustcVm.Tables.FormBufAt.of_same hg
      (same_block (F_le h) hm' hwf (o := 152) (n := 5928) (by decide) (by decide))
    have hforms := forms_wrOk h (.inl rfl) hm' hwf (by decide) hG
    have hterms := hbuf.terms
    change TermsAt st.dmem ((base m0 F + BitVec.ofNat 64 152) + BitVec.ofNat 64 8) _ at hterms
    rw [NativeRustcVm.addr_add_add] at hterms
    have ht : InOk st (base m0 F + BitVec.ofNat 64 160) (termBytes * (gf m0 (BA L rows bl) j).size)
        formBufAddScaledStack := Bus.local_ok h.stack le_as
      (by change 160 + 40 * (gf m0 (BA L rows bl) j).size ≤ F; change 160 + 40 * (gf m0 (BA L rows bl) j).size ≤ 12096; omega)
      hst'.fr.kept hst'.fr.sp
    refine ⟨hst'.fr.stackOk h.stack (by decide) le_as, e2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e0, slotOf_eq ho hs]
      exact hforms.forms _ ho _ hs
    · rw [e1]
      exact hterms
    · rw [e0]
      exact Bus.Fr.readable hst'.fr hok.1
    · rw [e0]
      exact Bus.Fr.offStack hst'.fr h.stack hok.2 le_as
    · rw [e1, e2]
      exact ht.1
    · rw [e1, e2]
      exact ht.2
    · rw [e0, e1, e2]
      exact NativeRustcVm.Apart.symm (in_frame h hok.2 (by
        change 160 + 40 * (gf m0 (BA L rows bl) j).size ≤ 12096; omega))
  · refine ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hh ↦ ?_, hq.2.2⟩
    rw [e0] at hh
    exact hh.elim (fun hq ↦ .inr (.inr (slot_out h hol hq))) .inl
  · have hif := hq.1
    change (if (_ : FormW).size ≤ formCap then _ else _) at hif
    rw [e3, e4] at hif
    change (if ((slotOf (sta SL m0 (BA L rows bl) Fm j).1 (blk (BA L rows bl) j).owner
      m0.regs.X2.toNat).addScaled (gf m0 (BA L rows bl) j) (tsl SL m0 j)).size ≤ formCap then _ else _) at hif
    rw [ite_eq_left_of_eq_true _ _ (eq_true (add_scaled_fits h hj)), e0] at hif
    have hch : SameOutside st.dmem m2.dmem (fun q ↦ InRange (stackBelow st formBufAddScaledStack)
        formBufAddScaledStack q ∨ InRange (base m0 F + BitVec.ofNat 64 0) 0 q ∨ outs m0 q) :=
      NativeRustcVm.SameOutside.mono hq.2.1 fun q hh ↦ by
        rw [e0] at hh
        exact hh.elim (fun hq ↦ .inr (.inr (slot_out h hol hq))) .inl
    have hb := (same_block (F_le h) hm' hwf (o := 152) (n := 5928) (by decide) (by decide)).trans
      (same_call hst'.fr.sp (by have := h.stack.2.1; have := le_as; omega) (outs_frame h) hch
        (by decide) (by decide) (.inr (by decide)))
    have hforms := forms_wrOk h (.inl rfl) hm' hwf (by decide) hG
    have hnew : FormsAt m2.dmem m0.regs.X1.toBitVec
        ((sta SL m0 (BA L rows bl) Fm j).1.modify (blk (BA L rows bl) j).owner fun row ↦
          row.modify m0.regs.X2.toNat fun f ↦ f.addScaled (gf m0 (BA L rows bl) j) (tsl SL m0 j)) := by
      refine FormsAt.modify hforms ho hs (fun f ↦ f.addScaled (gf m0 (BA L rows bl) j) (tsl SL m0 j))
        ?_ h.formsOk.1.2 (by rw [← e0]; exact hq.2.1) ?_
      · rw [← slotOf_eq ho hs]
        exact hif.2
      · intro i hi
        have ha := Bus.Fr.offStack hst'.fr h.stack h.formsOk.2 le_as
        exact NativeRustcVm.Apart.not_inRange_add ha h.formsOk.1.2 (by
          unfold NativeRustcVm.NoWrap
          rw [stackBelow_toNat h hst'.fr le_as]
          have := m0.regs.SP.toNat_lt
          have := le_as
          have := h.stack.2.1
          omega) hi
    rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b31Offset + b31.length = k + NativeRustcVmArm.Vm.AccumulateSide.b32Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b31_next]]
    refine cont m2 ⟨hst2.fr, Holds.sub hst2.hd (by decide)⟩ hif.1
      (NativeRustcVm.Tables.FormBufAt.of_same hg hb) ?_
    change FormsAt m2.dmem m0.regs.X1.toBitVec (stAt Fm m0.regs.X2.toNat (BA L rows bl) SL
      (wA m0) (betaA m0) (ptA m0) (j + 1)).1
    rw [stAt_succ]
    exact hnew

end

end NativeRustcVmArm.Bus.AccumulateSide
