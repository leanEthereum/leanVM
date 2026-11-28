module

public import NativeRustcVmArm.Code.Vm.BlockForm.Names
public import NativeRustcVmArm.Bus.AccumulateSide.Loop1
public import NativeRustcVm.Bus.Tuples

/-!
# `accumulate_side`: a turn of the table loop, `block_form`

`b28` calls `block_form` for table block `j`'s tuple into the frame's `FormBuf` at byte `152`
(`turn28`): it fits, X0 is `1`, the `FormBuf` holds the block's form.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

/-- **`b28`**: `block_form` for table block `j`. -/
theorem turn28 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hbf : Spec (Labels.label NativeRustcVmArm.Vm.BlockForm.entryLabel) BlockFormPre BlockFormPost)
    {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) L28 m) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm j) L29 m2 → m2.regs.X0 = 1 →
      FormBufAt m2.dmem (base m0 F + BitVec.ofNat 64 152) (gf m0 (BA L rows bl) j) →
      KeepF m0 m m2 → Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b29Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b28Offset)⟩ := by
  have hfr := hst.fr
  have h51 := bl_size h
  have hok : ROk m0 0 (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j), 16) :=
    ROk.sub h.blocksOk (by omega) (by decide)
  have hH0 : Holds ((base m0 F, F + 0) ::
      [(m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j), 16)]) (TT SL m0 L rows bl Fm j)
      L28 m := St.lift (D := L28) hst (by decide) 0 _
  have hwf := wf1 h hfr.kept hok
  have h28 : (m.regs.getXReg .X28).toBitVec =
      m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 8 := by
    rw [Holds.regv hst.hd (r := .X28) (i := 99) (by decide), NativeRustcVm.addr_add_add]
    show (UInt64.ofBitVec (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 + 16 * j))).toBitVec = _
    rw [show 8 + 16 * j = 16 * j + 8 by omega]
  obtain ⟨-, htup⟩ := bl_words h hj
  have htl := (h.bown bl[j] (List.getElem_mem hj)).2
  rw [NativeRustcVm.Bus.tuples_length] at htl
  have hwd : NativeRustcVm.wordOf m.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j + 8)) =
      bl[j].tuple.toUInt64 := by
    rw [word_in h hfr h.blocksOk (NativeRustcVm.Apart.symm h.fB) (by omega), htup]
  refine St.runCall h (A := 0) (sz := [12096, 16]) rfl
    (b28_in_code.trans hp.1 (by simp [b28])) run_b28 hfr hH0 hwf (matchR h hfr.sp h28) rfl
    (by decide) (D' := L29a) (E := [(.reg .X28, 99)]) (by decide) (by decide)
    (fun st hm' ↦ holds_one ?_) (N' := blockFormStack) (lo := 152) (n := 5928) le_bf
    (by decide) (by decide) hbf (fun st hm' hst' ↦ ?_) (fun st m' hm' hq ↦ ?_)
    fun st m2 hm' hst' hst2 hq _ ↦ ?_
  · rw [tval_reg_of hm' rfl, ptr1_eval (oi := 8) (o := 8) _ _ _ _ _ rfl,
      NativeRustcVm.addr_add_add]
    show _ = UInt64.ofBitVec (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 + 16 * j))
    rw [show 16 * j + 8 = 8 + 16 * j by omega]
  all_goals
    have ex0 : st.regs.X0 = bl[j].tuple.toUInt64 := by
      apply UInt64.toBitVec_inj.mp
      rw [show st.regs.X0 = st.regs.getXReg .X0 from rfl, hm'.regs .X0 _ rfl, load_rk rfl,
        NativeRustcVm.addr_add_add, hwd]
    have ex1 : st.regs.X1 = stackArg m0 8 :=
      (argv (sz := [12096, 16]) rfl hH0 hm' (r := .X1) (a := 8) (by decide)).trans
        (TT_sv (by decide))
    have ex2 : st.regs.X2 = stackArg m0 16 :=
      (argv (sz := [12096, 16]) rfl hH0 hm' (r := .X2) (a := 9) (by decide)).trans
        (TT_sv (by decide))
    have ex3 : st.regs.X3 = stackArg m0 24 :=
      (argv (sz := [12096, 16]) rfl hH0 hm' (r := .X3) (a := 10) (by decide)).trans
        (TT_sv (by decide))
    have ex4 : st.regs.X4 = stackArg m0 32 :=
      (argv (sz := [12096, 16]) rfl hH0 hm' (r := .X4) (a := 11) (by decide)).trans
        (TT_sv (by decide))
    have ex5 : st.regs.X5.toBitVec = base m0 F + BitVec.ofNat 64 152 := by
      rw [show st.regs.X5 = st.regs.getXReg .X5 from rfl, hm'.regs .X5 _ rfl,
        ptr0_eval (oi := 152) (o := 152) _ _ _ _ rfl]
  · refine ⟨hst'.fr.stackOk h.stack (by decide) le_bf, Bus.Fr.rodataAt hst'.fr h.rodata
      h.stack.2.1 le_bf (fun t i hi ho ↦ rodataApart_out h.formsRo h.rodata h.formsOk.1.2 t i hi
        ho), ?_, ?_, ?_, ?_, ?_⟩
    · rw [ex0, NativeRustcVm.Bus.tuples_length, Nat.toUInt64,
        UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
      exact htl
    · rw [ex1, ex2]
      exact ⟨Bus.Fr.readable hst'.fr h.w.1, Bus.Fr.offStack hst'.fr h.stack h.w.2 le_bf⟩
    · rw [ex5]
      exact Bus.local_ok h.stack le_bf (by decide) hst'.fr.kept hst'.fr.sp
    · rw [ex5]
      exact ro_frame h (by decide)
    · rw [ex5, ex1, ex2]
      exact in_frame h h.w.2 (by decide)
  · refine ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩
    rw [ex5] at hq'
    exact hq'.elim (fun h ↦ .inr (.inl h)) .inl
  · rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b28Offset + b28.length = k + NativeRustcVmArm.Vm.AccumulateSide.b29Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b28_next]]
    have hg : blockForm ⟨0, 0, tupleOf st.regs.X0.toNat, 0⟩ (slice st st.regs.X1 st.regs.X2)
        (ewArg st.regs.X3 st.regs.X4) = gf m0 (BA L rows bl) j := by
      rw [ex0, ex1, ex2, ex3, ex4, w_eq h hst'.fr, gf_eq hj, Nat.toUInt64,
        UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
      rfl
    obtain ⟨hif, hch, -⟩ := hq
    have hif' : (if (gf m0 (BA L rows bl) j).size ≤ formCap then m2.regs.X0 = 1 ∧
        FormBufAt m2.dmem st.regs.X5.toBitVec (gf m0 (BA L rows bl) j) else m2.regs.X0 = 0) := by
      rw [← hg]; exact hif
    rw [ite_eq_left_of_eq_true _ _ (eq_true (gf_size h hj)), ex5] at hif'
    refine cont m2 ⟨hst2.fr, Holds.sub hst2.hd (by decide)⟩ hif'.1 hif'.2 fun G hG ↦ ?_
    refine forms_frame h hst'.fr.sp le_bf (lo := 152) (n := 5928) (by decide) ?_
      (forms_wrOk h (.inl rfl) hm' hwf (by decide) hG)
    rw [← ex5]
    exact hch

end

end NativeRustcVmArm.Bus.AccumulateSide
