module

public import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmArm.Bus.AccumulateSide.CallKit

/-!
# `accumulate_side`: a turn of the table loop, the selector and the block's form

Turn `j` (`TT j` its table): `b27` calls `eq_eval_fn` for table block `j`'s selector
(`turn27`), `b28` `block_form` for its form into the frame's `FormBuf` at byte `152` (`turn28`).
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- `b27`'s registers kept but X27. -/
@[expose] def DLr27 : List (Sym × Nat) :=
  [(.reg .X20, 12), (.reg .X21, 93), (.reg .X22, 92), (.reg .X26, 13),
    (.reg .X28, 99), (.reg .X29, 100)]

/-- `b28`'s locations kept. -/
@[expose] def L29a : List (Sym × Nat) :=
  [(.reg .X20, 12), (.reg .X26, 13), (.reg .X21, 93), (.reg .X22, 92),
    (.reg .X23, 94), (.reg .X24, 95), (.reg .X27, 98), (.reg .X29, 100)] ++ DLf

/-- The table of turn `j`. -/
abbrev TT [Labels] (SL : BusLayoutW) (m0 : MachineData) (L : LayoutW) (rows : Array Nat)
    (bl : List NativeRustcVm.Data.Block) (Fm : Array (Array FormW)) (j : Nat) : Nat → UInt64 :=
  T SL m0 (BA L rows bl) Fm j

section
variable [Labels]

theorem ptr1_eval (m : MachineData) (b0 b1 : BitVec 64) (n0 n1 : Nat) {oi : Int} {o : Nat}
    (ho : oi = o) :
    (Sym.ptr 1 oi).eval (Env.ofMachine m [(b0, n0), (b1, n1)]) = b1 + BitVec.ofNat 64 o := by
  subst ho
  simp only [Sym.eval, Env.base_ofMachine_eq]
  rw [BitVec.ofInt_natCast]
  rfl

theorem ptr0_eval (m : MachineData) (rs : List (BitVec 64 × Nat)) (b0 : BitVec 64) (n0 : Nat)
    {oi : Int} {o : Nat} (ho : oi = o) :
    (Sym.ptr 0 oi).eval (Env.ofMachine m ((b0, n0) :: rs)) = b0 + BitVec.ofNat 64 o := by
  subst ho
  simp only [Sym.eval, Env.base_ofMachine_eq]
  rw [BitVec.ofInt_natCast]
  rfl

/-- **A register after a block**, a location of the description. -/
theorem argv {rs : List (BitVec 64 × Nat)} {sz : List Nat} (hsz : rs.map Prod.snd = sz)
    {V : Nat → UInt64} {D : List (Sym × Nat)} {m st : MachineData} {S : SState}
    (hH : Holds rs V D m) (hm : Match (Env.ofMachine m rs) S st) {r : XReg} {a : Nat}
    (ht : trackOk sz S D [(.reg r, a)] = true) : st.regs.getXReg r = V a :=
  hH.after hsz hm ht _ (List.mem_singleton_self _)

end

section
variable [Labels] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

/-- The weights in a state of the body are the entry's. -/
theorem w_eq (h : Pre L rows bl Fm SL m0) {st : MachineData}
    (hfr : Fr m0 F N slots keep (outs m0) st) :
    slice st (stackArg m0 8) (stackArg m0 16) = wA m0 :=
  Bus.Fr.slice_eq hfr h.stack h.w fun _ hj ↦
    NativeRustcVm.Apart.not_inRange_add (NativeRustcVm.Apart.symm h.fW) h.w.1.2 h.formsOk.1.2 hj

/-- **The forms through a call** writing its stack and frame bytes. -/
theorem forms_frame (h : Pre L rows bl Fm SL m0) {st m2 : MachineData}
    (hsp : st.regs.SP.toBitVec = base m0 F) {N' lo n : Nat} (hle : F + N' ≤ N)
    (hlo : lo + n ≤ F)
    (hs : SameOutside st.dmem m2.dmem (fun q ↦ InRange (base m0 F + BitVec.ofNat 64 lo) n q ∨
      InRange (stackBelow st N') N' q))
    {G : Array (Array FormW)} (hG : FormsAt st.dmem m0.regs.X1.toBitVec G) :
    FormsAt m2.dmem m0.regs.X1.toBitVec G := by
  have hN := h.stack.2.1
  have hoff := h.formsOk.2
  have hnw := forms_nw h
  have hb := base_toNat (m0 := m0) (F := F) (by have := F_le h; omega)
  have hsb : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
  have hsb' : (stackBelow st N').toNat = m0.regs.SP.toNat - (F + N') := by
    rw [stackBelow_eq hsp (by omega)]; exact base_toNat (by omega)
  have hcnw : NoWrap (stackBelow st N') N' := by
    unfold NoWrap; rw [hsb']; have := m0.regs.SP.toNat_lt; omega
  have hlt := m0.regs.SP.toNat_lt
  have hF := F_le h
  have hfa : (base m0 F + BitVec.ofNat 64 lo).toNat = (base m0 F).toNat + lo :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  refine FormsAt.of_same hG (Same.of_sameOutside hs fun j hj hq ↦ ?_)
  unfold OffStack Apart at hoff
  unfold NoWrap at hnw
  have : formsBytes = 106704 := rfl
  have e : (m0.regs.X1.toBitVec + BitVec.ofNat 64 j).toNat = m0.regs.X1.toBitVec.toNat + j :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  rcases hq with hq | hq
  · rw [Sym.inRange_iff (by rw [hfa]; omega), hfa, e] at hq
    omega
  · rw [Sym.inRange_iff hcnw, hsb', e] at hq
    omega

/-- The frame is apart from the read-only data. -/
theorem ro_frame (h : Pre L rows bl Fm SL m0) {o n : Nat} (hon : o + n ≤ F) :
    RodataApart (base m0 F + BitVec.ofNat 64 o) n := fun t ↦ by
  have hA := (h.rodata t).2.2
  have hN := h.stack.2.1
  have hb := base_toNat (m0 := m0) (F := F) (by have := F_le h; omega)
  have hsb : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
  have hlt := m0.regs.SP.toNat_lt
  have hF := F_le h
  unfold NativeRustcVm.Apart at hA ⊢
  rw [NativeRustcVm.toNat_add_ofNat (by omega), hb]
  rw [hsb] at hA
  have : F ≤ N := by decide
  omega

/-- The frame is apart from an input apart from the stack. -/
theorem in_frame (h : Pre L rows bl Fm SL m0) {a : BitVec 64} {n' : Nat}
    (ha : OffStack m0 a n' N) {o n : Nat} (hon : o + n ≤ F) :
    Apart (base m0 F + BitVec.ofNat 64 o) n a n' := by
  have hN := h.stack.2.1
  have hb := base_toNat (m0 := m0) (F := F) (by have := F_le h; omega)
  have hsb : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
  have hlt := m0.regs.SP.toNat_lt
  have hF := F_le h
  unfold OffStack Apart at ha
  unfold Apart
  rw [NativeRustcVm.toNat_add_ofNat (by omega), hb]
  rw [hsb] at ha
  have : F ≤ N := by decide
  omega

theorem bl_size (h : Pre L rows bl Fm SL m0) : bl.length ≤ 51 := by
  have := h.sl.tables.1; rw [h.sl_size] at this; exact this

omit [Labels] in
theorem BA_size : (BA L rows bl).size = bl.length := by simp [BA]

omit [Labels] in
theorem blk_eq {j : Nat} (hj : j < bl.length) :
    blk (BA L rows bl) j = blockW L.tableLogHeights rows bl[j] := by
  simp [blk, BA, Array.getD_eq_getD_getElem?, hj]

omit [Labels] in
theorem gf_eq {j : Nat} (hj : j < bl.length) :
    gf m0 (BA L rows bl) j = blockForm ⟨0, 0, tupleOf bl[j].tuple, 0⟩ (wA m0) (betaA m0) := by
  unfold gf
  rw [blk_eq hj]
  rfl

theorem gf_size (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < bl.length) :
    (gf m0 (BA L rows bl) j).size ≤ formCap := by
  have := h.fits.1 (blk (BA L rows bl) j) (by
    rw [blk_eq hj]; simp only [BA, List.mem_toArray, List.mem_map]
    exact ⟨bl[j], List.getElem_mem hj, rfl⟩)
  exact this

/-- Turn `j`'s table at the entry's arguments. -/
theorem TT_sv {j i : Nat} (hi : i < 30) : TT SL m0 L rows bl Fm j i = sv m0 i := T_sv _ _ _ _ _ hi

end

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

/-- **`b27`**: table block `j`'s selector. -/
theorem turn27 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) DL m) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm j) L28 m2 → KeepF m0 m m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b28Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b27Offset)⟩ := by
  have hfr := hst.fr
  have h51 := bl_size h
  have hjt : j < SL.tables.size := by rw [h.sl_size]; exact hj
  obtain ⟨hvc, hix, hw0, hw1⟩ := tb_p h hjt
  have hok : ROk m0 0 (m0.regs.X6.toBitVec + BitVec.ofNat 64 (72 + 16 * j), 16) :=
    ROk.sub h.slOk (by show _ ≤ 888; omega) (by decide)
  have hH0 : Holds ((base m0 F, F + 0) ::
      [(m0.regs.X6.toBitVec + BitVec.ofNat 64 (72 + 16 * j), 16)]) (TT SL m0 L rows bl Fm j)
      DL m := St.lift (D := DL) hst (by decide) 0 _
  have h27 : (m.regs.getXReg .X27).toBitVec =
      m0.regs.X6.toBitVec + BitVec.ofNat 64 (72 + 16 * j) + BitVec.ofNat 64 8 := by
    rw [Holds.regv hst.hd (r := .X27) (i := 98) (by decide), NativeRustcVm.addr_add_add]
    show (UInt64.ofBitVec (m0.regs.X6.toBitVec + BitVec.ofNat 64 (80 + 16 * j))).toBitVec = _
    rw [show 80 + 16 * j = 72 + 16 * j + 8 by omega]
  have hwd : ∀ o, o + 8 ≤ 888 → NativeRustcVm.wordOf m.dmem
      (m0.regs.X6.toBitVec + BitVec.ofNat 64 o) =
      NativeRustcVm.wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 o) := fun o ho ↦
    word_in h hfr h.slOk (NativeRustcVm.Apart.symm h.fSL) ho
  refine St.eqCall h hee (.inl rfl) (sz := [12096, 16]) rfl
    (b27_in_code.trans hp.1 (by simp [b27])) run_b27 hfr hH0 (wf1 h hfr.kept hok)
    (matchR h hfr.sp h27) rfl (by decide) (D' := DLr27 ++ DLf) (E := [(.reg .X27, 98)])
    (by decide) (by decide) (fun st hm' ↦ holds_one ?_) (by decide)
    (n := .reg .X26) (pa := .reg .X20) (z := .reg .X12) (vs := .load 1 0 8) (is := .load 1 8 8)
    (p := SL.tables[j]) rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ fun m2 hst2 hret hF _ ↦ ?_
  · rw [tval_reg_of hm' rfl, ptr1_eval (oi := 8) (o := 8) _ _ _ _ _ rfl,
      NativeRustcVm.addr_add_add]
    show _ = UInt64.ofBitVec (m0.regs.X6.toBitVec + BitVec.ofNat 64 (80 + 16 * j))
    rw [show 72 + 16 * j + 8 = 80 + 16 * j by omega]
  · rw [Holds.evc hH0 (s := .reg .X26) (i := 13) (by decide), TT_sv (by decide)]
    rfl
  · rw [Holds.evc hH0 (s := .reg .X20) (i := 12) (by decide), TT_sv (by decide)]
    rfl
  · rw [Holds.evc hH0 (s := .reg .X12) (i := 97) (by decide)]
    rfl
  · rw [load_rk rfl, add_zero', hwd _ (by omega), hw0, UInt64.toNat_toBitVec, Nat.toUInt64,
      UInt64.toNat_ofNat_of_lt' hvc]
  · rw [load_rk rfl, NativeRustcVm.addr_add_add, show 72 + 16 * j + 8 = 80 + 16 * j by omega,
      hwd _ (by omega), hw1, UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hix]
  · rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b27Offset + b27.length = k + NativeRustcVmArm.Vm.AccumulateSide.b28Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b27_next]]
    refine cont m2 ⟨hst2.fr, Holds.sub (holds_ewRet hst2.hd (r0 := 94) (x := tsl SL m0 j) ?_ rfl
      rfl) (by decide)⟩ hF
    rw [hret]
    show _ = eqAbove (SL.tables.getD j default) (ptA m0)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjt, Option.getD_some]

end

end NativeRustcVmArm.Bus.AccumulateSide
