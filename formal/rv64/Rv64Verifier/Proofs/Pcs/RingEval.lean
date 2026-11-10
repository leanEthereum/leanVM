import Rv64Verifier.Proofs.Pcs.RingEvalBase

/-!
# `<RingWeight>::evaluate`: the loops and the contract

See `RingEvalBase.lean` for the code's layout and the invariants.
-/

namespace Rv64Verifier.Proofs.Pcs.RingEval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F66
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The inner loop's body -/

/-- At the call to `E::square`, `0x8000e2a0`: the product updated, the values not yet. -/
structure AtSq (s u : MachineState) (nx P : Word) (i j : Nat) : Prop extends Regs s u P where
  inv : Inv s u nx
  pc : u.pc = 0x8000e2a0
  lt : i < nc s
  ltj : j < nn s
  x21 : u.getReg .x21 = cp s + BitVec.ofNat 64 (24 * i)
  x19 : u.getReg .x19 = P + BitVec.ofNat 64 (24 * j)
  x27 : u.getReg .x27 = s.getReg .x12 + BitVec.ofNat 64 (24 * j) + 16
  x1 : u.getReg .x1 = 0x8000e0b0
  x10 : u.getReg .x10 = s.getReg .x2 - 128
  x11 : u.getReg .x11 = P + BitVec.ofNat 64 (24 * j)
  acc : Model.limbs (st s i).1 = (u.getReg .x20, u.getReg .x23, u.getReg .x22)
  prod : eAt u (s.getReg .x2 - 176) = prodJ (rp s) (st s i).2 ((cs s).getD i 0) (j + 1)
  buf : ∀ l < nn s, eAt u (P + BitVec.ofNat 64 (24 * l)) =
    if l < j then (st s i).2.getD l 0 * (st s i).2.getD l 0 else (st s i).2.getD l 0
  o8 : u.getMem (s.getReg .x10 + 8) = 0
  o16 : u.getMem (s.getReg .x10 + 16) = 0

theorem limbs_sum (a b : E) : Model.limbs (1 + a + b) =
    (1 ^^^ (Model.limbs a).1 ^^^ (Model.limbs b).1, (Model.limbs a).2.1 ^^^ (Model.limbs b).2.1,
      (Model.limbs a).2.2 ^^^ (Model.limbs b).2.2) := by
  rw [limbs_add, limbs_add, limbs_one]
  rv_eval []

/-- `1 + value + challenge`, `mul`, and the copy back. -/
theorem innerMul (hMul : MulSpec) {s u : MachineState} {nx P : Word} {i j : Nat}
    (hpre : RingEvalPre s) (hlen : s.getMem (s.getReg .x11 + 16) = s.getReg .x13)
    (hBuf : BufOk s P nx) (hin : Inner s u nx P i j) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ AtSq s v nx P i j) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hj := hin.ltj
  have hfit := hin.inv.fits
  have hPr := hBuf.range.resolve_left (by omega)
  have hPa := hBuf.align
  have hlo := hpre.heap.lo
  have hRr := hpre.rPrime.region.resolve_left (by simp only [nn] at hj; omega)
  have hRb := Region.bounds hRr
  simp only [nn] at hj hPr
  have hsp := hin.inv.sp
  have hx19 := hin.x19
  have hx27 := hin.x27
  have hHr := heap_region (a := P) (n := 24 * nn s) (by simp only [heapStart] at hlo; omega)
    (by simp only [nn]; omega) hPa
  -- `1 + value + challenge` at `S - 152`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000e040_spec hin.pc (by
    rv_eval [hsp, hx19, hx27]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hHr (by addr_omega [hPr, hj, hfit])
          (by addr_omega [hPr, hj, hfit]) (by addr_omega [hPa, hPr, hj, hfit])
      | exact Region.valid hRr (by addr_omega [hRb, hj]) (by addr_omega [hRb, hj])
          (by addr_omega [hRb, hj]))
  have k₁ := b8000e040_keeps h₁
  have hm₁ := b8000e040_frame h₁ (by rw [hsp]; addr_omega [hb])
  rw [hsp] at hm₁
  rv_eval [] at hm₁
  have hnxs : ¬ Within nextAddr (s.getReg .x2 - 1200) 1200 := by
    simp only [ringEvalStack, mulStack, stackLo] at hnx8; addr_omega [hnx8, hb]
  have inv₁ := Inv.step' hpre hin.inv (DFrame.of_memFrame hm₁)
    (fun a ha ↦ Or.inr (Or.inl (by simp only [ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb])))
    (fun a ha ↦ by addr_omega [ha, hb])
    ((hm₁ _ (by simp only [ringEvalStack, mulStack, stackLo] at hnx8; addr_omega [hnx8, hb])).trans
      hin.inv.next) (Nat.le_refl _) hfit (k₁ .x2 (by decide))
  -- the sum
  have hv : eAt u (P + BitVec.ofNat 64 (24 * j)) = (st s i).2.getD j 0 := by
    have := hin.buf j (by simp only [nn]; omega)
    simpa using this
  have hrs := hpre.rPrime
  have hc : eAt u (s.getReg .x12 + BitVec.ofNat 64 (24 * j)) = (rp s).getD j 0 := by
    rw [rp_getD s j (by simp only [nn]; omega)]
    exact DFrame.eAt' hin.inv.mem (fun x hx ↦ Inv.src hin.inv hrs hpre.outRPrime x
      (by addr_omega [hx, hRb, hj])) (by addr_omega [hRb, hj])
  have hsum : eAt t₁ (s.getReg .x2 - 152) = 1 + (st s i).2.getD j 0 + (rp s).getD j 0 := by
    rw [← hv, ← hc]
    apply eAt_eq_of_limbs
    rw [limbs_sum, limbs_eAt, limbs_eAt]
    have m0 := b8000e040_m_x2_24 h₁
    have m1 := b8000e040_m_x2_32 h₁
    have m2 := b8000e040_m_x2_40 h₁
    rw [hsp, hx19, hx27] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    rv_eval [m0, m1, m2, Prod.mk.injEq]
    ac_rfl
  -- `mul`
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 176 := inv₁.sp
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 128 := by rw [b8000e040_x10 h₁, hsp]; rv_eval []
  have hx11₁ : t₁.getReg .x11 = s.getReg .x2 - 176 := by rw [b8000e040_x11 h₁, hsp]; rv_eval []
  have hx12₁ : t₁.getReg .x12 = s.getReg .x2 - 152 := by rw [b8000e040_x12 h₁, hsp]; rv_eval []
  have hsl : stackLo t₁ mulStack = s.getReg .x2 - 1200 := by
    simp only [stackLo, hsp₁, mulStack]; rv_eval []
  have hro := hst.rodata
  have hpreM : MulPre t₁ := {
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    lhs := by rw [hx11₁]; valid_sub hst.valid [hb]
    rhs := by rw [hx12₁]; valid_sub hst.valid [hb]
    stack := ⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₁]; addr_omega [hb]⟩
    outLhs := by rw [hx10₁, hx11₁]; addr_omega [hb]
    outRhs := by rw [hx10₁, hx12₁]; addr_omega [hb]
    outStack := by rw [hx10₁, hsl]; addr_omega [hb]
    lhsStack := by rw [hx11₁, hsl]; addr_omega [hb]
    rhsStack := by rw [hx12₁, hsl]; addr_omega [hb]
    rodata := Inv.rodata' hpre inv₁
    stackRodata := by rw [hsl]; addr_omega [hro, hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hMul.call hr₁ (b8000e040_pc h₁) hpreM
  swap
  · exact ⟨t₂, hr₂, Or.inl hdead⟩
  have hprod := hpost₂.value
  rw [hx10₁, hx11₁, hx12₁, hsum, hm₁.eAt (by addr_omega [hb]) (by addr_omega [hb]), hin.prod] at hprod
  have hfr₂ := hpost₂.frame
  rw [hx10₁, hsl] at hfr₂
  have inv₂ := Inv.step' hpre inv₁ (DFrame.of_two hfr₂)
    (fun a ha ↦ Or.inr (Or.inl (by
      simp only [ringEvalStack, mulStack, stackLo]; rcases ha with ha | ha <;> addr_omega [ha, hb])))
    (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb])
    ((hfr₂ _ (by addr_omega [hnxs, hb]) (by addr_omega [hnxs, hb])).trans inv₁.next) (Nat.le_refl _)
    hfit (hpres₂.reg .x2)
  -- copy the product, call `E::square`
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 176 := inv₂.sp
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000e088_spec
    (by rw [hpc₂, returnAddress_eq, b8000e040_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      and_intros <;> valid_access hst.valid [hb])
  have k₃ := b8000e088_keeps h₃
  have hm₃ := b8000e088_frame h₃ (by rw [hsp₂]; addr_omega [hb])
  rw [hsp₂] at hm₃
  rv_eval [] at hm₃
  have inv₃ := Inv.step' hpre inv₂ (DFrame.of_memFrame hm₃)
    (fun a ha ↦ Or.inr (Or.inl (by simp only [ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb])))
    (fun a ha ↦ by addr_omega [ha, hb])
    ((hm₃ _ (by addr_omega [hnxs, hb])).trans inv₂.next) (Nat.le_refl _) hfit (k₃ .x2 (by decide))
  have hp₃ : eAt t₃ (s.getReg .x2 - 176) = prodJ (rp s) (st s i).2 ((cs s).getD i 0) (j + 1) := by
    rw [prodJ_succ _ _ _ _ (by rw [st_length (pt_length hlen)]; simp only [nn]; omega)
      (by rw [rp_length]; simp only [nn]; omega), ← hprod]
    have m0 := b8000e088_m_x2_0 h₃
    have m1 := b8000e088_m_x2_8 h₃
    have m2 := b8000e088_m_x2_16 h₃
    rw [hsp₂] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    unfold eAt
    rv_eval [m0, m1, m2]
  have keepE (p : Word) (hp : Apart p 24 (s.getReg .x2 - 1200) 1200) (hw : p.toNat + 24 ≤ 2 ^ 64) :
      eAt t₃ p = eAt u p := by
    rw [hm₃.eAt (by addr_omega [hp, hb, hw]) hw,
      DFrame.eAt' (DFrame.of_two hfr₂) (fun x hx hX ↦ by
        rcases hX with hX | hX <;> addr_omega [hx, hX, hp, hb, hw]) hw,
      hm₁.eAt (by addr_omega [hp, hb, hw]) hw]
  have keepW (a : Word) (hp : Apart a 8 (s.getReg .x2 - 1200) 1200) (hw : a.toNat + 8 ≤ 2 ^ 64) :
      t₃.getMem a = u.getMem a := by
    rw [hm₃ a (by addr_omega [hp, hb, hw]), hfr₂ a (by addr_omega [hp, hb, hw])
      (by addr_omega [hp, hb, hw]), hm₁ a (by addr_omega [hp, hb, hw])]
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27]) : t₃.getReg r = u.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _),
      k₁ r (mem_of_mem hr _)]
  have hO := Region.bounds hpre.out.region
  have hOs := hpre.out.stack
  refine ⟨t₃, hr₂.trans hr₃, Or.inr {
    x8 := (hreg .x8 (by decide)).trans hin.x8
    x9 := (hreg .x9 (by decide)).trans hin.x9
    x18 := (hreg .x18 (by decide)).trans hin.x18
    x24 := (hreg .x24 (by decide)).trans hin.x24
    x25 := (hreg .x25 (by decide)).trans hin.x25
    x26 := (hreg .x26 (by decide)).trans hin.x26
    inv := inv₃
    pc := b8000e088_pc h₃
    lt := hin.lt
    ltj := hin.ltj
    x21 := (hreg .x21 (by decide)).trans hin.x21
    x19 := (hreg .x19 (by decide)).trans hx19
    x27 := (hreg .x27 (by decide)).trans hx27
    x1 := b8000e088_x1 h₃
    x10 := by rw [b8000e088_x10 h₃, hsp₂]; rv_eval []
    x11 := by rw [b8000e088_x11 h₃, hpres₂.reg .x19, k₁ .x19 (by decide), hx19]
    acc := by
      rw [hreg .x20 (by decide), hreg .x22 (by decide), hreg .x23 (by decide)]; exact hin.acc
    prod := hp₃
    buf := fun l hl ↦ by
      rw [keepE _ (by simp only [nn] at hl; addr_omega [hl, hPr, hfit, hab, hb])
        (by simp only [nn] at hl; addr_omega [hl, hPr, hfit])]
      exact hin.buf l hl
    o8 := by
      rw [keepW _ (by addr_omega [hO, hOs, hb]) (by addr_omega [hO])]; exact hin.o8
    o16 := by
      rw [keepW _ (by addr_omega [hO, hOs, hb]) (by addr_omega [hO])]; exact hin.o16 }⟩

theorem st_succ_getD {s : MachineState} (hlen : s.getMem (s.getReg .x11 + 16) = s.getReg .x13)
    {i l : Nat} (hi : i < nc s) (hl : l < nn s) :
    (st s (i + 1)).2.getD l 0 = (st s i).2.getD l 0 * (st s i).2.getD l 0 := by
  have hL := st_length (pt_length hlen) i
  rw [st_succ hi]
  simp only [stepW]
  rw [ringWeightPass_snd _ _ _ (by rw [hL, rp_length]),
    List.getD_eq_getElem _ _ (by rw [List.length_map, hL]; exact hl), List.getElem_map,
    List.getD_eq_getElem _ _ (by rw [hL]; exact hl), sq]

/-- `E::square`, the square stored over the value, and the next value or the pass's end. -/
theorem innerSquare (hSq : ESquareSpec) {s u : MachineState} {nx P : Word} {i j : Nat}
    (hpre : RingEvalPre s) (hlen : s.getMem (s.getReg .x11 + 16) = s.getReg .x13)
    (hBuf : BufOk s P nx) (ha : AtSq s u nx P i j) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ (j + 1 < nn s ∧ Inner s v nx P i (j + 1)) ∨
      (j + 1 = nn s ∧ Done s v nx P i)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hj := ha.ltj
  have hfit := ha.inv.fits
  have hPr := hBuf.range.resolve_left (by omega)
  have hPa := hBuf.align
  have hlo := hpre.heap.lo
  simp only [nn] at hj hPr
  have hsp := ha.inv.sp
  have hHr := heap_region (a := P) (n := 24 * nn s) (by simp only [heapStart] at hlo; omega)
    (by simp only [nn]; omega) hPa
  have hnxs : ¬ Within nextAddr (s.getReg .x2 - 1200) 1200 := by
    simp only [ringEvalStack, mulStack, stackLo] at hnx8; addr_omega [hnx8, hb]
  -- `E::square`
  have hpreS : ESquarePre u := {
    out := by rw [ha.x10]; valid_sub hst.valid [hb]
    arg := by
      rw [ha.x11]
      exact Region.vrange hHr (by addr_omega [hPr, hj, hfit]) (by addr_omega [hPr, hj, hfit])
        (by addr_omega [hPa, hPr, hj, hfit]) }
  obtain ⟨t₁, hr₁, ⟨hpc₁, hpres₁, hpost₁⟩ | hdead⟩ :=
    hSq.call (Reaches.refl u) ha.pc hpreS
  swap
  · exact ⟨t₁, hr₁, Or.inl hdead⟩
  have hsq := hpost₁.value
  rw [ha.x10, ha.x11] at hsq
  have hv : eAt u (P + BitVec.ofNat 64 (24 * j)) = (st s i).2.getD j 0 := by
    have := ha.buf j (by simp only [nn]; omega)
    simpa using this
  rw [hv] at hsq
  have hfr₁ := hpost₁.frame
  rw [ha.x10] at hfr₁
  have inv₁ := Inv.step' hpre ha.inv (DFrame.of_memFrame hfr₁)
    (fun a h ↦ Or.inr (Or.inl (by simp only [ringEvalStack, mulStack, stackLo]; addr_omega [h, hb])))
    (fun a h ↦ by addr_omega [h, hb])
    ((hfr₁ _ (by addr_omega [hnxs, hb])).trans ha.inv.next) (Nat.le_refl _) hfit
    (hpres₁.reg .x2)
  -- store it over the value, advance
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 176 := inv₁.sp
  have hx19₁ : t₁.getReg .x19 = P + BitVec.ofNat 64 (24 * j) := (hpres₁.reg .x19).trans ha.x19
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000e0b0_spec
    (by rw [hpc₁, returnAddress_eq, ha.x1]; decide) (by
      rv_eval [hsp₁, hx19₁]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid hHr (by addr_omega [hPr, hj, hfit])
            (by addr_omega [hPr, hj, hfit]) (by addr_omega [hPa, hPr, hj, hfit]))
  have k₂ := b8000e0b0_keeps h₂
  have hm₂ := b8000e0b0_frame h₂ (by rw [hx19₁]; addr_omega [hPr, hj, hfit])
  rw [hx19₁] at hm₂
  have inv₂ := Inv.step' hpre inv₁ (DFrame.of_memFrame hm₂)
    (fun a h ↦ Or.inr (Or.inr (Or.inr (by addr_omega [h, hPr, hj, hfit]))))
    (fun a h ↦ by addr_omega [h, hPr, hj, hfit, hab, hb])
    ((hm₂ _ (by have := hpre.heap.hi; addr_omega [hPr, hj, hfit])).trans inv₁.next) (Nat.le_refl _)
    hfit (k₂ .x2 (by decide))
  have hnew : eAt t₂ (P + BitVec.ofNat 64 (24 * j)) =
      (st s i).2.getD j 0 * (st s i).2.getD j 0 := by
    rw [← hsq]
    have m0 := b8000e0b0_m_x19_0 h₂
    have m1 := b8000e0b0_m_x19_8 h₂
    have m2 := b8000e0b0_m_x19_16 h₂
    rw [hsp₁, hx19₁] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    unfold eAt
    rv_eval [m0, m1, m2]
  have keepE (p : Word) (h1 : Apart p 24 (s.getReg .x2 - 128) 24)
      (h2 : Apart p 24 (P + BitVec.ofNat 64 (24 * j)) 24) (hw : p.toNat + 24 ≤ 2 ^ 64) :
      eAt t₂ p = eAt u p := by
    rw [hm₂.eAt h2 hw, hfr₁.eAt h1 hw]
  have keepW (a : Word) (h1 : Apart a 8 (s.getReg .x2 - 128) 24)
      (h2 : Apart a 8 (P + BitVec.ofNat 64 (24 * j)) 24) : t₂.getMem a = u.getMem a := by
    rw [hm₂ a (by addr_omega [h2]), hfr₁ a (by addr_omega [h1])]
  have hO := Region.bounds hpre.out.region
  have hOs := hpre.out.stack
  have hOf := hpre.out.free
  simp only [Outside] at hOf
  have hOP (c : Nat) (hc : c = 8 ∨ c = 16) :
      Apart (s.getReg .x10 + BitVec.ofNat 64 c) 8 (P + BitVec.ofNat 64 (24 * j)) 24 := by
    rcases hOf.1 with h | h
    · addr_omega [h, hPr, hj, hO, hc]
    · addr_omega [h, hPr, hj, hO, hc, hfit]
  have o8 : t₂.getMem (s.getReg .x10 + 8) = 0 := by
    rw [keepW _ (by addr_omega [hO, hOs, hb]) (by simpa using hOP 8 (Or.inl rfl))]; exact ha.o8
  have o16 : t₂.getMem (s.getReg .x10 + 16) = 0 := by
    rw [keepW _ (by addr_omega [hO, hOs, hb]) (by simpa using hOP 16 (Or.inr rfl))]; exact ha.o16
  have hprod : eAt t₂ (s.getReg .x2 - 176) = prodJ (rp s) (st s i).2 ((cs s).getD i 0) (j + 1) := by
    rw [keepE _ (by addr_omega [hb]) (by addr_omega [hPr, hj, hfit, hab, hb]) (by addr_omega [hb])]
    exact ha.prod
  have hbuf (l : Nat) (hl : l < nn s) : eAt t₂ (P + BitVec.ofNat 64 (24 * l)) =
      if l < j + 1 then (st s i).2.getD l 0 * (st s i).2.getD l 0 else (st s i).2.getD l 0 := by
    simp only [nn] at hl
    by_cases hlj : l = j
    · subst hlj; simpa using hnew
    · rw [keepE _ (by addr_omega [hl, hPr, hfit, hab, hb]) (by addr_omega [hl, hlj, hj, hPr, hfit])
        (by addr_omega [hl, hPr, hfit]), ha.buf l (by simp only [nn]; exact hl)]
      by_cases hlt : l < j
      · simp only [hlt, ↓reduceIte, show l < j + 1 by omega]
      · simp only [hlt, ↓reduceIte, show ¬ l < j + 1 by omega]
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x20, .x21, .x22, .x23, .x24, .x25, .x26]) :
      t₂.getReg r = u.getReg r := by
    rw [k₂ r (mem_of_mem hr _), hpres₁ r (by unfold calleeSaved; exact mem_of_mem hr _)]
  have hregs : Regs s t₂ P := {
    x8 := (hreg .x8 (by decide)).trans ha.x8
    x9 := (hreg .x9 (by decide)).trans ha.x9
    x18 := (hreg .x18 (by decide)).trans ha.x18
    x24 := (hreg .x24 (by decide)).trans ha.x24
    x25 := (hreg .x25 (by decide)).trans ha.x25
    x26 := (hreg .x26 (by decide)).trans ha.x26 }
  have hacc : Model.limbs (st s i).1 = (t₂.getReg .x20, t₂.getReg .x23, t₂.getReg .x22) := by
    rw [hreg .x20 (by decide), hreg .x22 (by decide), hreg .x23 (by decide)]; exact ha.acc
  have hx26 := ha.x26
  by_cases hlast : j + 1 = nn s
  · obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000e0d4_spec
      (b8000e0b0_pc_not_taken h₂ (by
        rw [hx19₁, hpres₁.reg .x26, hx26]; simp only [nn] at hlast; addr_omega [hlast, hPr, hfit]))
      trivial
    have k₃ := b8000e0d4_keeps h₃
    refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inr ⟨hlast, {
      x8 := (k₃ .x8 (by decide)).trans hregs.x8
      x9 := (k₃ .x9 (by decide)).trans hregs.x9
      x18 := (k₃ .x18 (by decide)).trans hregs.x18
      x24 := (k₃ .x24 (by decide)).trans hregs.x24
      x25 := (k₃ .x25 (by decide)).trans hregs.x25
      x26 := (k₃ .x26 (by decide)).trans hregs.x26
      inv := inv₂.same (b8000e0d4_mem_same h₃) (k₃ .x2 (by decide)) (fun _ h ↦ by cases h)
      pc := b8000e0d4_pc h₃
      lt := ha.lt
      x21 := by rw [k₃ .x21 (by decide), hreg .x21 (by decide)]; exact ha.x21
      acc := by rw [k₃ .x20 (by decide), k₃ .x22 (by decide), k₃ .x23 (by decide)]; exact hacc
      prod := by
        simp only [eAt, b8000e0d4_mem_same h₃]
        rw [← hlast]; exact hprod
      buf := fun l hl ↦ by
        simp only [eAt, b8000e0d4_mem_same h₃]
        rw [st_succ_getD hlen ha.lt hl]
        have := hbuf l hl
        simp only [show l < j + 1 by omega, ↓reduceIte] at this
        exact this
      o8 := by rw [b8000e0d4_mem_same h₃]; exact o8
      o16 := by rw [b8000e0d4_mem_same h₃]; exact o16 }⟩)⟩
  · have hj1 : j + 1 < nn s := by simp only [nn] at hlast ⊢; omega
    refine ⟨t₂, hr₁.trans hr₂, Or.inr (Or.inl ⟨hj1, {
      toRegs := hregs
      inv := inv₂
      pc := b8000e0b0_pc_taken h₂ (by
        rw [hx19₁, hpres₁.reg .x26, hx26]; simp only [nn] at hj1; addr_omega [hj1, hPr, hfit])
      lt := ha.lt
      ltj := hj1
      x21 := by rw [hreg .x21 (by decide)]; exact ha.x21
      x19 := by rw [b8000e0b0_x19 h₂, hx19₁]; simp only [nn] at hj1; addr_omega [hj1, hPr, hfit]
      x27 := by
        rw [b8000e0b0_x27 h₂, hpres₁.reg .x27, ha.x27]
        have hRb := Region.bounds (hpre.rPrime.region.resolve_left (by omega))
        simp only [nn] at hj1; addr_omega [hj1, hRb]
      acc := hacc
      prod := hprod
      buf := hbuf
      o8 := o8
      o16 := o16 }⟩)⟩

end Rv64Verifier.Proofs.Pcs.RingEval
