module

public import NativeRustcVmArm.Bus.AccumulateSide.Loop2

/-!
# `accumulate_side`: what the table loop's `add_scaled` needs

`TABLES`' word of the owner a six-way `csel` chain picks (`tab_sel`). The owner's form of the side:
its address (`slot_addr`), it fits (`slot_fits`), the forms with it replaced (`FormsAt.modify`).
A part of an input (`InOk.sub`).
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVm.Transcript (off)

public section

/-- **The six-way `csel` chain** on the owner: `TABLES`' word of the owner. -/
theorem tab_sel [Labels] (env : Env) (x : Sym) (c : Nat) {o : Nat} (ho : o < 6)
    (hx : x.eval env = BitVec.ofNat 64 o) :
    (Sym.ite (.cmp .eq .W64 x (.lit 0)) (.load 1 c 8)
      (.ite (.cmp .eq .W64 x (.lit 1)) (.load 1 (40 + c) 8)
      (.ite (.cmp .eq .W64 x (.lit 2)) (.load 1 (80 + c) 8)
      (.ite (.cmp .eq .W64 x (.lit 3)) (.load 1 (120 + c) 8)
      (.ite (.cmp .eq .W64 x (.lit 4)) (.load 1 (160 + c) 8) (.load 1 (200 + c) 8)))))).eval env =
      (Sym.load 1 (40 * o + c) 8).eval env := by
  have e : ∀ i : Nat, i < 6 → SBool.eval env (.cmp .eq .W64 x (.lit i)) = decide (o = i) :=
    fun i hi ↦ by
      simp only [SBool.eval, CmpOp.apply, low_W64, hx, Sym.eval]
      by_cases hoi : o = i
      · subst hoi; simp
      · simp only [hoi, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro he
        have := congrArg BitVec.toNat he
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        exact hoi this
  simp only [Sym.eval, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide),
    e 4 (by decide)]
  rcases (by omega : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- A part of an input. -/
theorem InOk.sub {m0 : MachineData} {a : BitVec 64} {n o n' : Nat} (hok : InOk m0 a n N)
    (ho : o + n' ≤ n) (hpos : 0 < n') : InOk m0 (a + BitVec.ofNat 64 o) n' N := by
  obtain ⟨⟨hm, hnw⟩, hap⟩ := hok
  unfold NoWrap at hnw
  unfold OffStack Apart at hap
  have e : (a + BitVec.ofNat 64 o).toNat = a.toNat + o := NativeRustcVm.toNat_add_ofNat (by omega)
  refine ⟨⟨fun i hi ↦ ?_, ?_⟩, ?_⟩
  · rw [NativeRustcVm.addr_add_add]; exact hm _ (by omega)
  · unfold NoWrap; rw [e]; omega
  · unfold OffStack Apart; rw [e]; omega

/-- **The owner's form of the side**: its address. -/
theorem slot_addr {a x2 : BitVec 64} {o s : Nat} (hx2 : x2.toNat = s) :
    BinOp.apply .add .W64 (BinOp.apply .mul .W64 (BitVec.ofNat 64 o) (BitVec.ofNat 64 17784))
      (BinOp.apply .add .W64 (BinOp.apply .mul .W64 x2 (BitVec.ofNat 64 5928)) a) =
      a + BitVec.ofNat 64 (formBufBytes * (3 * o + s)) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  have : formsBytes = 106704 := rfl
  have hf : formBufBytes = 5928 := rfl
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hx2, hf,
    show MemWidth.W64.bits = 64 from rfl, Nat.reducePow]
  have := a.isLt
  omega

/-- **The forms with the owner's form of the side replaced.** -/
theorem FormsAt.modify {d d' : Mem 64} {a : BitVec 64} {G : Array (Array FormW)}
    (h : FormsAt d a G) {o s : Nat} (ho : o < G.size) (hs : s < G[o].size) (g : FormW → FormW)
    (hx : FormBufAt d' (off a (formBufBytes * (3 * o + s))) (g G[o][s]))
    {Z : BitVec 64 → Prop} (hnw : a.toNat + formsBytes ≤ 2 ^ 64)
    (hss : SameOutside d d' fun q ↦
      InRange (a + BitVec.ofNat 64 (formBufBytes * (3 * o + s))) formBufBytes q ∨ Z q)
    (hZ : ∀ j < formsBytes, ¬Z (a + BitVec.ofNat 64 j)) :
    FormsAt d' a (G.modify o fun row ↦ row.modify s g) := by
  have hG := h.size
  have hrow := h.row_size
  have hf : formBufBytes = 5928 := rfl
  have hfs : formsBytes = 106704 := rfl
  unfold nTables at hG
  have ho6 : o < 6 := by rw [hG] at ho; exact ho
  have hs3 : s < 3 := by rw [hrow o ho] at hs; exact hs
  have key : ∀ t s', t < 6 → s' < 3 → 3 * t + s' ≠ 3 * o + s →
      Same d d' (off a (formBufBytes * (3 * t + s'))) formBufBytes := by
    intro t s' ht hs' hne j hj
    rw [hf] at hj
    refine hss _ fun hq ↦ hq.elim (fun hq ↦ ?_)
      (fun hq ↦ hZ (5928 * (3 * t + s') + j) (by omega) ?_)
    · simp only [off, hf] at hq
      rw [NativeRustcVm.addr_add_add, Sym.inRange_iff (by
        rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega),
        NativeRustcVm.toNat_add_ofNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega)]
        at hq
      omega
    · simp only [off, hf] at hq
      rwa [NativeRustcVm.addr_add_add] at hq
  refine ⟨by rw [Array.size_modify]; exact hG, fun t ht ↦ ?_, fun t ht s' hs' ↦ ?_⟩
  · rw [Array.size_modify] at ht
    rw [Array.getElem_modify]
    split
    · rw [Array.size_modify]; exact hrow t ht
    · exact hrow t ht
  · have ht' : t < G.size := by rw [Array.size_modify] at ht; exact ht
    have hr := hrow t ht'
    have ht6 : t < 6 := by rw [hG] at ht'; exact ht'
    simp only [Array.getElem_modify] at hs' ⊢
    by_cases hto : o = t
    · subst hto
      simp only [↓reduceIte, Array.size_modify] at hs' ⊢
      rw [Array.getElem_modify]
      by_cases hss' : s = s'
      · subst hss'
        simp only [↓reduceIte]
        exact hx
      · simp only [hss', ↓reduceIte]
        have hs3' : s' < 3 := by rw [hr] at hs'; exact hs'
        exact NativeRustcVm.Tables.FormBufAt.of_same (h.forms o ht' s' hs')
          (key o s' ho6 hs3' (by omega))
    · simp only [hto, ↓reduceIte] at hs' ⊢
      have hs3' : s' < 3 := by rw [hr] at hs'; exact hs'
      exact NativeRustcVm.Tables.FormBufAt.of_same (h.forms t ht' s' hs')
        (key t s' ht6 hs3' (by omega))

section
variable [Labels] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

theorem fm_shape (h : Pre L rows bl Fm SL m0) : Fm.size = 6 ∧ ∀ o (ho : o < Fm.size),
    Fm[o].size = 3 :=
  ⟨h.forms.size, h.forms.row_size⟩

theorem sta_shape (h : Pre L rows bl Fm SL m0) (j : Nat) :
    (sta SL m0 (BA L rows bl) Fm j).1.size = 6 ∧ ∀ o (ho : o < (sta SL m0 (BA L rows bl) Fm j).1.size),
      (sta SL m0 (BA L rows bl) Fm j).1[o].size = 3 := by
  obtain ⟨h1, h2⟩ := stAt_size Fm m0.regs.X2.toNat (BA L rows bl) SL (wA m0) (betaA m0) (ptA m0) j
  obtain ⟨s1, s2⟩ := fm_shape h
  refine ⟨h1.trans s1, fun o ho ↦ ?_⟩
  rw [h2 o (by rw [h1] at ho; exact ho) ho]
  exact s2 o (by rw [h1] at ho; exact ho)

omit [Labels] in
theorem slotOf_eq {G : Array (Array FormW)} {o s : Nat} (ho : o < G.size) (hs : s < G[o].size) :
    slotOf G o s = G[o][s] := by
  simp [slotOf, Array.getD_eq_getD_getElem?, ho, hs]

/-- **The owner's form of the side fits** after any turn. -/
theorem slot_fits (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j ≤ bl.length) {o s : Nat}
    (ho : o < 6) (hs : s < 3) : (slotOf (sta SL m0 (BA L rows bl) Fm j).1 o s).size ≤ formCap := by
  have hjk : j ≤ (BA L rows bl).size := by rw [BA_size]; exact hj
  have hmono := slot_size_mono Fm m0.regs.X2.toNat (BA L rows bl) SL (wA m0) (betaA m0) (ptA m0)
    o s (j := j) (k := (BA L rows bl).size) hjk
  refine Nat.le_trans hmono ?_
  obtain ⟨g1, g2⟩ := sta_shape h (BA L rows bl).size
  have ho' : o < (sta SL m0 (BA L rows bl) Fm (BA L rows bl).size).1.size := by rw [g1]; exact ho
  have hs' : s < (sta SL m0 (BA L rows bl) Fm (BA L rows bl).size).1[o].size := by
    rw [g2 o ho']; exact hs
  have hfit := h.fits.2
  rw [accumulateSide_eq _ _ _ _ _ _ _ _ _ (by rw [h.sl_size, BA_size])] at hfit
  rw [slotOf_eq ho' hs']
  exact hfit _ (Array.getElem_mem ho') _ (Array.getElem_mem hs')

end

end

end NativeRustcVmArm.Bus.AccumulateSide
