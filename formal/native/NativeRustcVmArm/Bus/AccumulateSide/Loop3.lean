module

public import NativeRustcVmArm.Bus.AccumulateSide.LoopKit

/-!
# `accumulate_side`: a turn of the table loop, the success checks

`b29`: `block_form` returned `1` (`turn29`). `b30`: the block's owner, below `6` (`turn30`). `b32`: `add_scaled` returned `1` (`turn32`).
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- `b30`'s locations kept. -/
@[expose] def L30a : List (Sym × Nat) :=
  [(.reg .X21, 93), (.reg .X22, 92), (.reg .X23, 94), (.reg .X24, 95),
    (.reg .X27, 98), (.reg .X29, 100)] ++ DLf

/-- The frame's `FormBuf` through a block writing none of its bytes. -/
theorem fb_block [Labels] {m0 m st : MachineData} {A : Nat} {rs : List (BitVec 64 × Nat)}
    {S : SState} (hSP : F ≤ m0.regs.SP.toNat)
    (hm : Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S st)
    (hwf : (Env.ofMachine m ((base m0 F, F + A) :: rs)).WF)
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ (w.off + w.n ≤ 152 ∨ 6080 ≤ w.off)) {g : FormW}
    (hg : FormBufAt m.dmem (base m0 F + BitVec.ofNat 64 152) g) :
    FormBufAt st.dmem (base m0 F + BitVec.ofNat 64 152) g :=
  NativeRustcVm.Tables.FormBufAt.of_same hg (same_block hSP hm hwf (by decide) hw)

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

/-- **`b29`**: `block_form` returned `1`. -/
theorem turn29 (hp : Placed code k) (h : Pre L rows bl Fm SL m0) {j : Nat} {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) L29 m) (hx0 : m.regs.X0 = 1) {g : FormW}
    (hg : FormBufAt m.dmem (base m0 F + BitVec.ofNat 64 152) g) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm j) L30 m2 →
      FormBufAt m2.dmem (base m0 F + BitVec.ofNat 64 152) g → KeepF m0 m m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b30Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b29Offset)⟩ := by
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b29_in_code.trans hp.1 (by simp [b29])) run_b29 hst.fr (St.lift (D := L29) hst (by decide) 0 [])
    hwf (matchF h hst.fr.sp) rfl (by decide) (D' := L30) (E := []) (by decide) (by decide)
    (fun _ _ ↦ holds_nil _ _ _) fun st hm' hpc hst' ↦ ?_
  have hc : SBool.eval (Env.ofMachine m [(base m0 F, F + 0)]) (.not (.bit .W32 (.reg .X0) 0)) =
      false := by
    show (!(low .W32 (m.regs.getXReg .X0).toBitVec).getLsbD 0) = false
    rw [show m.regs.getXReg .X0 = 1 from hx0]
    rfl
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc
  refine Gkr.at_pc hpc ?_
  rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b29Offset + b29.length = k + NativeRustcVmArm.Vm.AccumulateSide.b30Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b29_next]]
  exact cont st.data ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
    (fb_block (F_le h) hm' hwf (by decide) hg) fun G hG ↦ forms_wrOk h (.inl rfl) hm' hwf
      (by decide) hG

/-- **`b30`**: table block `j`'s owner, below `6`. -/
theorem turn30 (hp : Placed code k) (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < bl.length)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm j) L30 m) {g : FormW}
    (hg : FormBufAt m.dmem (base m0 F + BitVec.ofNat 64 152) g) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm j) L31 m2 →
      FormBufAt m2.dmem (base m0 F + BitVec.ofNat 64 152) g → KeepF m0 m m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b31Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b30Offset)⟩ := by
  have hfr := hst.fr
  have h51 := bl_size h
  have hok : ROk m0 0 (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j), 16) :=
    ROk.sub h.blocksOk (by omega) (by decide)
  have hH0 : Holds ((base m0 F, F + 0) ::
      [(m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j), 16)]) (TT SL m0 L rows bl Fm j)
      L30 m := St.lift (D := L30) hst (by decide) 0 _
  have hwf := wf1 h hfr.kept hok
  have h28 : (m.regs.getXReg .X28).toBitVec =
      m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 8 := by
    rw [Holds.regv hst.hd (r := .X28) (i := 99) (by decide), NativeRustcVm.addr_add_add]
    show (UInt64.ofBitVec (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 + 16 * j))).toBitVec = _
    rw [show 8 + 16 * j = 16 * j + 8 by omega]
  obtain ⟨hown, -⟩ := bl_words h hj
  have hol := (h.bown bl[j] (List.getElem_mem hj)).1
  unfold nTables at hol
  have hwd : (Sym.load 1 0 8).eval (Env.ofMachine m ((base m0 F, F + 0) ::
      [(m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j), 16)])) = bl[j].owner.toUInt64.toBitVec := by
    rw [load_rk rfl, add_zero', word_in h hfr h.blocksOk (NativeRustcVm.Apart.symm h.fB)
      (by omega), hown]
  refine St.run h.stack (A := 0) (sz := [12096, 16]) rfl
    (b30_in_code.trans hp.1 (by simp [b30])) run_b30 hfr hH0 hwf (matchR h hfr.sp h28) rfl
    (by decide) (D' := L30a) (E := [(.reg .X20, 96), (.reg .X28, 99)]) (by decide) (by decide)
    (fun st hm' p hp' ↦ ?_) fun st hm' hpc hst' ↦ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl
    · rw [tval_reg_of hm' rfl, hwd]
      show _ = (blk (BA L rows bl) j).owner.toUInt64
      rw [blk_eq hj]
      rfl
    · rw [tval_reg_of hm' rfl, ptr1_eval (oi := 8) (o := 8) _ _ _ _ _ rfl,
        NativeRustcVm.addr_add_add]
      show _ = UInt64.ofBitVec (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 + 16 * j))
      rw [show 16 * j + 8 = 8 + 16 * j by omega]
  · have hc : SBool.eval (Env.ofMachine m ((base m0 F, F + 0) ::
        [(m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j), 16)]))
        (.and (.not (.cmp .ult .W64 (.load 1 0 8) (.lit 5)))
          (.not (.cmp .eq .W64 (.load 1 0 8) (.lit 5)))) = false := by
      have hlo : bl[j].owner < 2 ^ 64 := by omega
      change (!(SBool.eval _ (.cmp .ult .W64 (.load 1 0 8) (.lit 5))) &&
        !(SBool.eval _ (.cmp .eq .W64 (.load 1 0 8) (.lit 5)))) = false
      simp only [cmp_ult_lit _ hwd (by decide : 5 < 2 ^ 64),
        cmp_eq_lit _ hwd (by decide : 5 < 2 ^ 64), Nat.toUInt64,
        UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega : bl[j].owner < UInt64.size)]
      by_cases h5 : bl[j].owner < 5
      · simp [h5]
      · simp [show bl[j].owner = 5 by omega]
    simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc
    refine Gkr.at_pc hpc ?_
    rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b30Offset + b30.length = k + NativeRustcVmArm.Vm.AccumulateSide.b31Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b30_next]]
    exact cont st.data ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
      (fb_block (F_le h) hm' hwf (by decide) hg) fun G hG ↦ forms_wrOk h (.inl rfl) hm' hwf
        (by decide) hG

/-- **`b32`**: `add_scaled` succeeded. -/
theorem turn32 (hp : Placed code k) (h : Pre L rows bl Fm SL m0) {j : Nat} {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) L32 m) (hx0 : m.regs.X0 = 1) {g : FormW}
    (hg : FormBufAt m.dmem (base m0 F + BitVec.ofNat 64 152) g) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm j) L32 m2 →
      FormBufAt m2.dmem (base m0 F + BitVec.ofNat 64 152) g → KeepF m0 m m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b33Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b32Offset)⟩ := by
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b32_in_code.trans hp.1 (by simp [b32])) run_b32 hst.fr (St.lift (D := L32) hst (by decide) 0 [])
    hwf (matchF h hst.fr.sp) rfl (by decide) (D' := L32) (E := []) (by decide) (by decide)
    (fun _ _ ↦ holds_nil _ _ _) fun st hm' hpc hst' ↦ ?_
  have hc : SBool.eval (Env.ofMachine m [(base m0 F, F + 0)])
      (.cmp .eq .W32 (.reg .X0) (.lit 0)) = false := by
    change (low .W32 m.regs.X0.toBitVec == low .W32 (BitVec.ofNat 64 0)) = false
    rw [hx0]
    rfl
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc
  refine Gkr.at_pc hpc ?_
  rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b32Offset + b32.length = k + NativeRustcVmArm.Vm.AccumulateSide.b33Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b32_next]]
  exact cont st.data ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
    (fb_block (F_le h) hm' hwf (by decide) hg) fun G hG ↦ forms_wrOk h (.inl rfl) hm' hwf
      (by decide) hG

end

end NativeRustcVmArm.Bus.AccumulateSide
