module

public import NativeRustcVmX64.Bus.AccumulateSide.Keep

/-!
# `accumulate_side`: what the table loop's turn shares (x86-64)

The turn's table of values (`VT`); the frame apart from what is apart from the stack
(`Pre.frame_apart`) and from the read-only data (`Pre.frame_roApart`); the read-only data for a
callee (`St.rodata`); a prefix of a slice (`sliceOk_prefix`); the table blocks' count (`Pre.bl51`).
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

/-- The table loop's values at turn `j`. -/
abbrev VT [Labels] (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block)
    (Fm : Array (Array FormW)) (SL : BusLayoutW) (m0 : MachineData) (j : Nat) : Nat → UInt64 :=
  Vt SL m0 (lpT L rows bl Fm SL m0 j)

end

public section

theorem outs_id {m0 : MachineData} : ∀ q, outs m0 q → outs m0 q := fun _ h ↦ h

/-- A prefix of a slice. -/
theorem sliceOk_prefix {m : MachineData} {a n n' : BitVec 64} {s : Nat} (h : SliceOk m a n s)
    (hn : n'.toNat ≤ n.toNat) : SliceOk m a n' s := by
  obtain ⟨⟨hm, hnw⟩, hA⟩ := h
  refine ⟨⟨fun i hi ↦ hm i (by omega), ?_⟩, ?_⟩
  · unfold NoWrap at hnw ⊢; omega
  · unfold OffStack Apart at hA ⊢; omega

/-- A prefix of an input. -/
theorem inOk_prefix {m : MachineData} {a : BitVec 64} {n n' s : Nat} (h : InOk m a n s)
    (hn : n' ≤ n) : InOk m a n' s := by
  obtain ⟨⟨hm, hnw⟩, hA⟩ := h
  refine ⟨⟨fun i hi ↦ hm i (by omega), ?_⟩, ?_⟩
  · unfold NoWrap at hnw ⊢; omega
  · unfold OffStack Apart at hA ⊢; omega

theorem apart_shrink {a b : BitVec 64} {n m m' : Nat} (h : NativeRustcVm.Apart a n b m)
    (hm : m' ≤ m) : NativeRustcVm.Apart a n b m' := by
  unfold NativeRustcVm.Apart at h ⊢; omega

theorem mul64 (x y : BitVec 64) : BinOp.apply .mul .W64 x y = x * y := by
  simp only [BinOp.apply, low_W64, ext_W64]

/-- The address of the forms' slot of owner `o`, side `s`, as `b21` computes it. -/
theorem slot_addr (a d : BitVec 64) {s o : Nat} (hs : d.toNat = s) :
    d * 5928#64 + a + BitVec.ofNat 64 o * BitVec.ofNat 64 17784 =
      off a (formBufBytes * (3 * o + s)) := by
  rw [bv_eq hs]
  have hf : formBufBytes = 5928 := rfl
  rw [hf]
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

section
variable {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData}

theorem stA_succ (j : Nat) : stA L rows bl Fm SL m0 (j + 1) =
    stepT (reg m0 .rdx).toNat (BA L rows bl) SL (wA m0) (betaA m0) (ptA m0)
      (stA L rows bl Fm SL m0 j) j :=
  stAt_succ _ _ _ _ _ _ _ _

theorem stA_succ_fst (j : Nat) : (stA L rows bl Fm SL m0 (j + 1)).1 =
    (stA L rows bl Fm SL m0 j).1.modify (bkA L rows bl j).owner (fun row ↦
      row.modify (reg m0 .rdx).toNat fun f ↦ f.addScaled (fmA L rows bl m0 j) (tsel SL (ptA m0) j)) := by
  rw [stA_succ]; rfl

theorem stA_succ_snd (j : Nat) : (stA L rows bl Fm SL m0 (j + 1)).2 =
    (stA L rows bl Fm SL m0 j).2 +
      tsel SL (ptA m0) j * pwA L rows bl m0 j * (evA L rows bl m0 j + 1) := by
  rw [stA_succ]; rfl

end

variable [Labels] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData}

theorem Pre.bl51 (h : Pre L rows bl Fm SL m0) : bl.length ≤ 51 := by
  have := h.sl.tables.1
  rw [h.sl_size] at this
  exact this

/-- **Frame bytes** apart from what is apart from the stack. -/
theorem Pre.frame_apart (h : Pre L rows bl Fm SL m0) {a : BitVec 64} {l : Nat}
    (hA : NativeRustcVm.Apart a l (stackBelow m0 N) (N + 8)) {o n : Nat} (hon : o + n ≤ F + 8)
    (hn : 0 < n) : NativeRustcVm.Apart (off (fb m0) o) n a l := by
  have hnw : (fb m0).toNat + (F + 8) ≤ 2 ^ 64 := h.frame_nw
  have hF : F = 12032 := rfl
  have h1 : NativeRustcVm.Apart a l (fb m0) (F + 8) := apart_frame hA h.spN le_F
  have ho : (off (fb m0) o).toNat = (fb m0).toNat + o := toNat_off (by omega)
  unfold NativeRustcVm.Apart at h1 ⊢
  rw [ho]
  omega

/-- **Frame bytes** apart from the read-only data. -/
theorem Pre.frame_roApart (h : Pre L rows bl Fm SL m0) {o n : Nat} (hon : o + n ≤ F + 8)
    (hn : 0 < n) : RodataApart (off (fb m0) o) n := fun t ↦
  h.frame_apart (h.rodata t).2.2 hon hn

/-- **The read-only data** for a callee of the body. -/
theorem St.rodata (h : Pre L rows bl Fm SL m0) {O : BitVec 64 → Prop} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {m : MachineData} (hst : St m0 O V D 0 m)
    (hO : ∀ q, O q → outs m0 q) {Nc : Nat} (hle : F + Nc ≤ N) : RodataAt m Nc := by
  unfold RodataAt NativeRustcVm.RodataAt
  intro t
  obtain ⟨hb, hnw, hA⟩ := h.rodata t
  refine ⟨hb.of_sameOutside hst.same fun i hi hq ↦ ?_, hnw, ?_⟩
  · rcases hq with hq | hq
    · exact NativeRustcVm.Apart.not_inRange_add (Apart.symm' (h.formsRo t)) hnw h.forms_nw hi
        (hO _ hq)
    · exact NativeRustcVm.Apart.not_inRange_add hA hnw (noWrap_stackBelow h.stack) hi
        (Ring.inRange_le hq (by omega))
  · exact apart_callee hA (by rw [hst.fr.sp, off_zero]) h.spN hle

/-- **Owner `o`'s form of side `s`** for a callee of the body: readable, apart from its stack. -/
theorem St.slotOk (h : Pre L rows bl Fm SL m0) {O : BitVec 64 → Prop} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {m : MachineData} (hst : St m0 O V D 0 m) {Nc : Nat}
    (hle : F + Nc ≤ N) {o s : Nat} (ho : o < 6) (hs : s < 3) :
    InOk m (off (reg m0 .rsi) (formBufBytes * (3 * o + s))) formBufBytes Nc := by
  have hnw : (reg m0 .rsi).toNat + formsBytes ≤ 2 ^ 64 := h.forms_nw
  have hf : formBufBytes = 5928 := rfl
  have hfs : formsBytes = 106704 := rfl
  have hol : formBufBytes * (3 * o + s) + formBufBytes ≤ formsBytes := by
    rw [hf, hfs]; omega
  have ho' : (off (reg m0 .rsi) (formBufBytes * (3 * o + s))).toNat =
      (reg m0 .rsi).toNat + formBufBytes * (3 * o + s) := toNat_off (by rw [hf] at hol ⊢; omega)
  refine ⟨⟨mapped_off (Mapped.keeps h.formsOk.1.1 hst.fr.kept) hol, ?_⟩, ?_⟩
  · show NativeRustcVm.NoWrap _ _
    unfold NativeRustcVm.NoWrap; rw [ho']; omega
  · exact apart_callee (Apart.symm' (apart_sub (Apart.symm' h.formsOk.2) h.forms_nw hol
      (by rw [hf]; decide))) (by rw [hst.fr.sp, off_zero]) h.spN hle

/-- Owner `o`'s form of side `s` apart from the stack. -/
theorem Pre.slot_stack (h : Pre L rows bl Fm SL m0) {o s : Nat} (ho : o < 6) (hs : s < 3) :
    NativeRustcVm.Apart (off (reg m0 .rsi) (formBufBytes * (3 * o + s))) formBufBytes
      (stackBelow m0 N) (N + 8) := by
  have hf : formBufBytes = 5928 := rfl
  have hfs : formsBytes = 106704 := rfl
  exact Apart.symm' (apart_sub (Apart.symm' h.formsOk.2) h.forms_nw (by rw [hf, hfs]; omega)
    (by rw [hf]; decide))

/-- **The owner's form of the side after turn `j`.** -/
theorem slot_succ (h : Pre L rows bl Fm SL m0) (j : Nat) (ho : (bkA L rows bl j).owner < 6) :
    slotOf (stA L rows bl Fm SL m0 (j + 1)).1 (bkA L rows bl j).owner (reg m0 .rdx).toNat =
      (slotOf (stA L rows bl Fm SL m0 j).1 (bkA L rows bl j).owner (reg m0 .rdx).toNat).addScaled
        (fmA L rows bl m0 j) (tsel SL (ptA m0) j) := by
  rw [stA_succ_fst, slotOf_modify]
  obtain ⟨g1, g2⟩ := sta_shape h j
  have hside := h.side
  have hoS : (bkA L rows bl j).owner < (stA L rows bl Fm SL m0 j).1.size := by rw [g1]; exact ho
  have hs : (reg m0 .rdx).toNat < ((stA L rows bl Fm SL m0 j).1.getD (bkA L rows bl j).owner #[]).size := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hoS, Option.getD_some, g2 _ hoS]
    exact hside
  rw [ite_eq_left ⟨rfl, rfl, hoS, hs⟩]

end

end NativeRustcVmX64.Bus.AccumulateSide
