import Rv64Verifier.Proofs.Pcs.BasisRing

/-!
# `<StackBasis>::evaluate`: a `PlacedRing` weight, at `0x8000d1e8`

`eq_above(x)` into `S - 144`, the bound check `variables ≤ x.len()` (`0x8000d204`, a trap past
it), `RingWeight::evaluate(&x[..variables])` into `S - 120`, their product into `S - 168`.
-/

namespace Rv64Verifier.Proofs.Pcs.Basis
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.MultilinearContracts Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F55
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem eListAt_take (s : MachineState) (p : Word) {k n : Nat} (h : k ≤ n) :
    (eListAt s p n).take k = eListAt s p k := by
  apply List.ext_getElem (by simp [eListAt_length]; omega)
  intro i h1 h2
  simp only [List.getElem_take, eListAt_getElem]

theorem placed_weight {s : MachineState} {k : Nat} (he : s.getMem (claimAddr s k) ≠ eqTag)
    (hr : s.getMem (claimAddr s k) ≠ ringTag) (hle : (s.getMem (claimAddr s k + 48)).toNat ≤ (s.getReg .x13).toNat) :
    weightOf s k = ((ringWeightAt s (claimAddr s k)).evaluate
      (eListAt s (s.getReg .x12) (s.getMem (claimAddr s k + 48)).toNat)).map
      (Model.PlacementRust.eqAbove ⟨(s.getMem (claimAddr s k + 48)).toNat, s.getMem (claimAddr s k + 56)⟩ (ptl s) * ·) := by
  simp only [weightOf, stackClaimAt, stackWeightAt]
  rw [ite_neg' he, ite_neg' hr]
  simp only [StackWeightRust.evaluate, ptl, eListAt_length]
  rw [ite_pos' hle, eListAt_take _ _ hle]

theorem evalPlaced (hR : RingEvalSpec) (hA : EqAboveSpec) (hMul : MulSpec)
    {s u : MachineState} {nx WP : Word} {k : Nat}
    (hpre : BasisPre s) (hh : Head s u nx WP k 0x8000d1e8)
    (he : s.getMem (claimAddr s k) ≠ eqTag) (htr : s.getMem (claimAddr s k) ≠ ringTag) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ ∃ nx', Got s v nx' WP k) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hk := hh.lt
  have hsp := hh.inv.sp
  have hCr := claims_region hpre hk
  have hC := Region.bounds hCr
  have hws : WeightSrc s basisStack (claimAddr s k) := hpre.weights k hk
  have hrs : RingSrc s basisStack (claimAddr s k) := by
    have h2 := hws.2
    change (if s.getMem (claimAddr s k) = eqTag then _ else _) at h2
    rw [ite_neg' he, ite_neg' htr] at h2
    exact h2
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hpS := hpre.point.stack
  have hpF := hpre.point.free
  have hpb := hpre.point.bound
  have hmp := hst.mapped (by decide) (by decide)
  simp only [stackLo, basisStack, ringEvalStack, mulStack] at hmp
  -- `eq_above`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000d1e8_spec hh.pc (by
    rv_eval [hh.x20]
    simp only [ncl] at hk
    and_intros <;> exact Region.valid hCr (by simp only [claimAddr]; addr_omega [hC, hk])
      (by simp only [claimAddr]; addr_omega [hC, hk]) (by simp only [claimAddr]; addr_omega [hC, hk]))
  have k₁ := b8000d1e8_keeps h₁
  have hm₁ := b8000d1e8_mem_same h₁
  have inv₁ := hh.inv.same hm₁ (k₁ .x2 (by decide)) (fun r hr ↦ by
    simp only [List.mem_singleton] at hr; subst hr; exact k₁ _ (by decide))
  have c48 := Inv.claim hpre hh.inv hk (o := 48) (by decide)
  have c56 := Inv.claim hpre hh.inv hk (o := 56) (by decide)
  rv_eval [] at c48 c56
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 192 := inv₁.sp
  have hx10 : t₁.getReg .x10 = s.getReg .x2 - 144 := by rw [b8000d1e8_x10 h₁, hsp]; rv_eval []
  have hx11 : t₁.getReg .x11 = s.getMem (claimAddr s k + 48) := by
    rw [b8000d1e8_x11 h₁, hh.x20, c48]
  have hx12 : t₁.getReg .x12 = s.getMem (claimAddr s k + 56) := by
    rw [b8000d1e8_x12 h₁, hh.x20, c56]
  have hx13 : t₁.getReg .x13 = s.getReg .x12 := by rw [b8000d1e8_x13 h₁, hh.x19]
  have hx14 : t₁.getReg .x14 = s.getReg .x13 := by rw [b8000d1e8_x14 h₁, hh.x18]
  have hslA : stackLo t₁ eqAboveStack = s.getReg .x2 - 1328 := by
    simp only [stackLo, hsp₁, eqAboveStack, mulStack, Nat.reduceAdd]; rv_eval []
  have hn₁ : heapNext s ≤ heapNext t₁ := by
    have := inv₁.mono; simp only [heapNext, inv₁.next] at this ⊢; exact this
  simp only [Outside] at hpF
  have hpreA : EqAbovePre t₁ := {
    heap := inv₁.heap hpre.heap
    ret := by rw [hx10]; valid_sub hst.valid [hb]
    point := by
      rw [hx13, hx14]
      rcases hpre.point.region with h0 | h0
      · intro i hi; omega
      · have := Region.bounds h0
        exact Region.vrange h0 (Nat.le_refl _) (by omega) this.2.2
    stack := hst.sub 192 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    retFree := by
      rw [hx10]; simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    pointFree := by
      rw [hx13, hx14]; simp only [Outside]
      refine ⟨?_, hpF.2⟩
      rcases hpF.1 with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr h0
    retStack := by rw [hx10, hslA]; addr_omega [hb]
    pointStack := by rw [hx13, hx14, hslA]; addr_omega [hpS, hb]
    rodata := Inv.rodata' hpre inv₁ }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpostA⟩ | hdead⟩ := hA.call hr₁ (b8000d1e8_pc h₁) hpreA
  swap
  · exact ⟨t₂, hr₂, Or.inl hdead⟩
  have hfrA : DFrame t₁ t₂ (EqAboveW t₁ t₂) := hpostA.frame
  have hfitA := hpostA.heap.hi
  have hsub₂ (a : Word) (ha : EqAboveW t₁ t₂ a) :
      Wr s basisStack (fun _ ↦ False) (t₂.getMem nextAddr) a := by
    simp only [EqAboveW, hx10, hslA] at ha
    rcases ha with ha | ha | ha | ha
    · exact Or.inr (Or.inl (by simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]))
    · exact Or.inr (Or.inl (by simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · refine Or.inr (Or.inr (Or.inr ⟨by simp only [Fresh, heapNext] at hn₁ ha ⊢; omega, ha.2⟩))
  have hslot₂ (a : Word) (ha : EqAboveW t₁ t₂ a) :
      ¬ Within a (s.getReg .x2 - BitVec.ofNat 64 96) 96 := by
    simp only [EqAboveW, hx10, hslA] at ha
    rcases ha with ha | ha | ha | ha
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx8]
    · simp only [Fresh] at ha; addr_omega [ha, hb, hab, hfitA]
  have inv₂ := Inv.step' hpre inv₁ hfrA hsub₂ hslot₂ rfl
    (by have := hpostA.mono; simp only [heapNext, inv₁.next] at this ⊢; exact this) hfitA
    (hpres₂.reg .x2) (hpres₂.reg .x27)
  have hA₂ := hpostA.value
  rw [hx10, hx11, hx12, hx13, hx14] at hA₂
  -- the bound check
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 192 := inv₂.sp
  have hx20₂ : t₂.getReg .x20 = claimAddr s k := by
    rw [hpres₂.reg .x20, k₁ .x20 (by decide), hh.x20]
  have c48₂ : t₂.getMem (claimAddr s k + 48) = s.getMem (claimAddr s k + 48) := by
    have := Inv.claim hpre inv₂ hk (o := 48) (by decide); rv_eval [] at this; exact this
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000d204_spec
    (by rw [hpc₂, returnAddress_eq, b8000d1e8_x1 h₁]; decide) (by
      rv_eval [hx20₂]
      simp only [ncl] at hk
      exact Region.valid hCr (by simp only [claimAddr]; addr_omega [hC, hk])
        (by simp only [claimAddr]; addr_omega [hC, hk]) (by simp only [claimAddr]; addr_omega [hC, hk]))
  have hx18₂ : t₂.getReg .x18 = s.getReg .x13 := by
    rw [hpres₂.reg .x18, k₁ .x18 (by decide), hh.x18]
  by_cases hle : (s.getMem (claimAddr s k + 48)).toNat ≤ (s.getReg .x13).toNat
  swap
  · refine ⟨t₃, hr₂.trans hr₃, Or.inl (dead_of_fetch ?_)⟩
    rw [b8000d204_pc_taken h₃ (by rw [hx18₂, hx20₂, c48₂]; omega)]
    exact trap
  have k₃ := b8000d204_keeps h₃
  have hm₃ := b8000d204_mem_same h₃
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000d20c_spec
    (b8000d204_pc_not_taken h₃ (by rw [hx18₂, hx20₂, c48₂]; exact hle)) trivial
  have k₄ := b8000d20c_keeps h₄
  have hm₄ := b8000d20c_mem_same h₄
  have inv₄ := (inv₂.same hm₃ (k₃ .x2 (by decide)) (fun r hr ↦ by
    simp only [List.mem_singleton] at hr; subst hr; exact k₃ _ (by decide))).same hm₄
    (k₄ .x2 (by decide)) (fun r hr ↦ by
    simp only [List.mem_singleton] at hr; subst hr; exact k₄ _ (by decide))
  -- `RingWeight::evaluate` on the first `variables` coordinates
  have hsp₄ : t₄.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 192 := inv₄.sp
  have hx10₄ : t₄.getReg .x10 = s.getReg .x2 - 120 := by
    rw [b8000d20c_x10 h₄, k₃ .x2 (by decide), hsp₂]; rv_eval []
  have hx11₄ : t₄.getReg .x11 = claimAddr s k := by
    rw [b8000d20c_x11 h₄, k₃ .x20 (by decide), hx20₂]
  have hx12₄ : t₄.getReg .x12 = s.getReg .x12 := by
    rw [b8000d20c_x12 h₄, k₃ .x19 (by decide), hpres₂.reg .x19, k₁ .x19 (by decide), hh.x19]
  have hx13₄ : t₄.getReg .x13 = s.getMem (claimAddr s k + 48) := by
    rw [k₄ .x13 (by decide), b8000d204_x13 h₃, hx20₂, c48₂]
  obtain ⟨hrc, hrw⟩ := ringSrc_callee hpre inv₄ hrs
  have hsl : stackLo t₄ ringEvalStack = s.getReg .x2 - 1392 := by
    simp only [stackLo, hsp₄, ringEvalStack, mulStack, Nat.reduceAdd]; rv_eval []
  have hn₄ : heapNext s ≤ heapNext t₄ := by
    have := inv₄.mono; simp only [heapNext, inv₄.next] at this ⊢; exact this
  have hlo : (stackLo s basisStack).toNat ≤ (stackLo t₄ ringEvalStack).toNat := by
    rw [hsl]; simp only [stackLo, basisStack, ringEvalStack, mulStack]; addr_omega [hb]
  have hhi : (stackLo t₄ ringEvalStack).toNat + ringEvalStack ≤
      (stackLo s basisStack).toNat + basisStack := by
    rw [hsl]; simp only [stackLo, basisStack, ringEvalStack, mulStack]; addr_omega [hb]
  have hkk : (stackLo s basisStack).toNat + basisStack ≤ 2 ^ 64 := by
    simp only [stackLo, basisStack, ringEvalStack, mulStack]; addr_omega [hb]
  have hselfS := hrs.self.stack
  have hptS := hrs.point.stack
  have hcoS := hrs.coeffs.stack
  obtain ⟨-, p0, l0⟩ := Inv.vecEs inv₄ (hrs.self.sub (Nat.le_refl _) (by omega)
    (Region.bounds (hrs.self.region.resolve_left (by decide))).2.2) hrs.point
  have hs24 : Src s basisStack (claimAddr s k + 24) 24 := by
    have := Region.bounds (hrs.self.region.resolve_left (by decide))
    exact hrs.self.sub (by addr_omega [this]) (by addr_omega [this]) (by addr_omega [this])
  obtain ⟨-, p1, l1⟩ := Inv.vecEs inv₄ hs24 hrs.coeffs
  have hpx : Src s basisStack (s.getReg .x12) (24 * (s.getMem (claimAddr s k + 48)).toNat) :=
    hpre.point.prefix (by omega)
  have hpxS := hpx.stack
  have hpreR : RingEvalPre t₄ := {
    heap := inv₄.heap hpre.heap
    stack := hst.sub 192 hsp₄ (by decide) (by decide) (by decide) (by decide) (by decide)
    rodata := Inv.rodata' hpre inv₄
    out := {
      region := by
        rw [hx10₄]
        simp only [Region, Mapped]
        constructor
        · right; addr_omega [hmp, hb]
        · addr_omega [hb]
      stack := by rw [hx10₄, hsl]; addr_omega [hb]
      free := by
        rw [hx10₄]; simp only [Outside]
        exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
      rodata := by rw [hx10₄]; addr_omega [hro, hb] }
    self := by rw [hx11₄]; exact hrc
    rPrime := by rw [hx12₄, hx13₄]; exact hpx.callee hlo hhi hkk hn₄
    outSelf := by rw [hx10₄, hx11₄]; addr_omega [hselfS, hb]
    outPoint := by rw [hx10₄, hx11₄, p0, l0]; addr_omega [hptS, hb]
    outCoeffs := by
      rw [hx10₄, hx11₄]
      rw [show claimAddr s k + 24 = claimAddr s k + 24 from rfl, p1, l1]; addr_omega [hcoS, hb]
    outRPrime := by rw [hx10₄, hx12₄, hx13₄]; addr_omega [hpxS, hb] }
  obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hdead⟩ := hR.call hr₄ (b8000d20c_pc h₄) hpreR
  swap
  · exact ⟨t₅, hr₂.trans (hr₃.trans hr₅), Or.inl hdead⟩
  have hfr₅ := hpost₅.frame
  rw [hx10₄, hsl] at hfr₅
  have hfit₅ := hpost₅.heap.hi
  have inv₅ := Inv.step' hpre inv₄ hfr₅
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inl (by simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]))
      · exact Or.inr (Or.inl (by simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · refine Or.inr (Or.inr (Or.inr ⟨?_, ha.2⟩))
        have h1 := ha.1; simp only [heapNext] at hn₄ h1 ⊢; omega)
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx8]
      · simp only [Fresh] at ha; addr_omega [ha, hb, hab, hfit₅])
    rfl (by have := hpost₅.mono; simp only [heapNext, inv₄.next] at this ⊢; exact this) hfit₅
    (hpres₅.reg .x2) (hpres₅.reg .x27)
  have hR₅ := hpost₅.value
  rw [hx10₄, hx11₄, hx12₄, hx13₄, hrw] at hR₅
  have eX : eListAt t₄ (s.getReg .x12) (s.getMem (claimAddr s k + 48)).toNat =
      eListAt s (s.getReg .x12) (s.getMem (claimAddr s k + 48)).toNat := Inv.eList inv₄ hpx
  rw [eX] at hR₅
  -- the product
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 192 := inv₅.sp
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000d220_spec
    (by rw [hpc₅, returnAddress_eq, b8000d20c_x1 h₄]; decide) trivial
  have k₆ := b8000d220_keeps h₆
  have hm₆ := b8000d220_mem_same h₆
  have inv₆ := inv₅.same hm₆ (k₆ .x2 (by decide)) (fun r hr ↦ by
    simp only [List.mem_singleton] at hr; subst hr; exact k₆ _ (by decide))
  have hx10₆ : t₆.getReg .x10 = s.getReg .x2 - 168 := by rw [b8000d220_x10 h₆, hsp₅]; rv_eval []
  have hx11₆ : t₆.getReg .x11 = s.getReg .x2 - 144 := by rw [b8000d220_x11 h₆, hsp₅]; rv_eval []
  have hx12₆ : t₆.getReg .x12 = s.getReg .x2 - 120 := by rw [b8000d220_x12 h₆, hsp₅]; rv_eval []
  have hsp₆ : t₆.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 192 := inv₆.sp
  have hslM : stackLo t₆ mulStack = s.getReg .x2 - 1216 := by
    simp only [stackLo, hsp₆, mulStack]; rv_eval []
  have hpreM : MulPre t₆ := {
    out := by rw [hx10₆]; valid_sub hst.valid [hb]
    lhs := by rw [hx11₆]; valid_sub hst.valid [hb]
    rhs := by rw [hx12₆]; valid_sub hst.valid [hb]
    stack := ⟨by rw [hslM]; valid_sub hst.valid [hb], by rw [hsp₆]; addr_omega [hb]⟩
    outLhs := by rw [hx10₆, hx11₆]; addr_omega [hb]
    outRhs := by rw [hx10₆, hx12₆]; addr_omega [hb]
    outStack := by rw [hx10₆, hslM]; addr_omega [hb]
    lhsStack := by rw [hx11₆, hslM]; addr_omega [hb]
    rhsStack := by rw [hx12₆, hslM]; addr_omega [hb]
    rodata := Inv.rodata' hpre inv₆
    stackRodata := by rw [hslM]; addr_omega [hro, hb] }
  obtain ⟨t₇, hr₇, ⟨hpc₇, hpres₇, hpost₇⟩ | hdead⟩ := hMul.call hr₆ (b8000d220_pc h₆) hpreM
  swap
  · exact ⟨t₇, hr₂.trans (hr₃.trans (hr₅.trans hr₇)), Or.inl hdead⟩
  have hfr₇ := hpost₇.frame
  rw [hx10₆, hslM] at hfr₇
  have inv₇ := Inv.step' hpre inv₆ (DFrame.of_two hfr₇)
    (fun a ha ↦ Or.inr (Or.inl (by
      simp only [basisStack, ringEvalStack, mulStack, stackLo]
      rcases ha with ha | ha <;> addr_omega [ha, hb])))
    (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb])
    ((hfr₇ _ (by addr_omega [hnx8, hb]) (by addr_omega [hnx8, hb])).trans inv₆.next)
    (Nat.le_refl _) inv₆.fits (hpres₇.reg .x2) (hpres₇.reg .x27)
  have hprod := hpost₇.value
  rw [hx10₆, hx11₆, hx12₆] at hprod
  have eA : eAt t₆ (s.getReg .x2 - 144) = eAt t₂ (s.getReg .x2 - 144) := by
    have : eAt t₅ (s.getReg .x2 - 144) = eAt t₄ (s.getReg .x2 - 144) :=
      DFrame.eAt' hfr₅ (fun x hx hX ↦ by
        rcases hX with hX | hX | hX | hX
        · addr_omega [hx, hX, hb]
        · addr_omega [hx, hX, hb]
        · addr_omega [hx, hX, hb, hnx8]
        · simp only [Fresh] at hX; addr_omega [hx, hX, hb, hab, hfit₅]) (by addr_omega [hb])
    simp only [eAt, hm₆] at this ⊢
    rw [this]
    simp only [hm₄, hm₃]
  have eR : eAt t₆ (s.getReg .x2 - 120) = eAt t₅ (s.getReg .x2 - 120) := by simp only [eAt, hm₆]
  rw [eA, eR, hA₂] at hprod
  -- back to the loop
  obtain ⟨t₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b8000d234_spec
    (by rw [hpc₇, returnAddress_eq, b8000d220_x1 h₆]; decide) trivial
  have k₈ := b8000d234_keeps h₈
  have hm₈ := b8000d234_mem_same h₈
  have hn₇ : heapNext t₁ ≤ (t₅.getMem nextAddr).toNat := by
    have := hpostA.mono; have h2 := hpost₅.mono
    simp only [heapNext, hm₃, hm₄] at this h2 ⊢; omega
  have eX₁ : eListAt t₁ (s.getReg .x12) (s.getReg .x13).toNat = ptl s := by
    rw [ptl, ← Inv.eList hh.inv hpre.point]; simp only [eListAt, eAt, hm₁]
  rw [eX₁] at hprod
  refine ⟨t₈, hr₂.trans (hr₃.trans (hr₅.trans (hr₇.trans hr₈))), Or.inr ⟨t₅.getMem nextAddr, {
    toRegs := hh.toRegs.of_eq fun r hr ↦ by
      rw [k₈ r (Runtime.mem_of_mem hr _),
        hpres₇ r (by unfold calleeSaved; exact Runtime.mem_of_mem hr _), k₆ r (Runtime.mem_of_mem hr _),
        hpres₅ r (by unfold calleeSaved; exact Runtime.mem_of_mem hr _), k₄ r (Runtime.mem_of_mem hr _),
        k₃ r (Runtime.mem_of_mem hr _),
        hpres₂ r (by unfold calleeSaved; exact Runtime.mem_of_mem hr _), k₁ r (Runtime.mem_of_mem hr _)]
    inv := inv₇.same hm₈ (k₈ .x2 (by decide)) (fun r hr ↦ by
      simp only [List.mem_singleton] at hr; subst hr; exact k₈ _ (by decide))
    pc := b8000d234_pc h₈
    lt := hk
    buf := ⟨hh.buf.align, by
      rcases hh.buf.range with h0 | h0
      · exact Or.inl h0
      · refine Or.inr ⟨h0.1, ?_⟩
        have h2 := hh.inv.next
        simp only [heapNext, hm₁, h2] at hn₇; omega⟩
    ws := fun l hl ↦ by
      rw [hh.ws l hl]
      congr 1
      have hnx : nx.toNat ≤ heapNext t₁ := by simp only [heapNext, hm₁, hh.inv.next]; exact le_refl _
      have e7 := ws_keep hpre hh.buf hh.inv.fits hk (DFrame.of_two hfr₇) (fun a ha ↦ by
        left; simp only [basisStack, ringEvalStack, mulStack, stackLo]
        rcases ha with ha | ha <;> addr_omega [ha, hb]) l hl
      have e5 := ws_keep hpre hh.buf hh.inv.fits hk hfr₅ (fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · left; simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]
        · left; simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]
        · exact Or.inr (Or.inl ha)
        · right; right; have h1 := ha.1
          have := hpostA.mono
          simp only [heapNext, hm₄, hm₃] at h1 this hnx; omega) l hl
      have e2 := ws_keep hpre hh.buf hh.inv.fits hk hfrA (fun a ha ↦ by
        simp only [EqAboveW, hx10, hslA] at ha
        rcases ha with ha | ha | ha | ha
        · left; simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]
        · left; simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]
        · exact Or.inr (Or.inl ha)
        · right; right; have h1 := ha.1; simp only [heapNext] at h1 hnx; omega) l hl
      simp only [eAt] at e7 e5 e2 ⊢
      simp only [hm₈, e7, hm₆, e5, hm₄, hm₃, e2, hm₁]
    w := by
      rw [placed_weight he htr hle, hR₅]
      simp only [Option.map_some, eAt, hm₈]
      simp only [eAt] at hprod
      rw [hprod] }⟩⟩

end Rv64Verifier.Proofs.Pcs.Basis
