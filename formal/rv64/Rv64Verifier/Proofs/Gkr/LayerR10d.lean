import Rv64Verifier.Proofs.Gkr.LayerR10c

/-!
# `keccak::verify_layer`: the second check, its products

`keccak.rs:171-176` at `0x8000fa34..0x8000fac0`: `scale * at_local` into `f + 1560`,
`kappa * t[0]` into `f + 1584` and `kappa + t[1]` into `f + 960`, `t` of length three (`c2a`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- `mulH` with its exact frame: the result and `mul`'s stack. -/
theorem mulF (hM : MulSpec) {s u₀ u : MachineState} (hpre : VerifyLayerPre s) (B : Base s u)
    (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x80008c48) (K : Nat)
    (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K) (hK : 128 ≤ K ∧ K ≤ 1712 ∧ K % 8 = 0)
    (hKw : ∀ a, Within a (s.getReg .x2 - BitVec.ofNat 64 K) 24 → W10 s a)
    (hl : ValidMemRange (u.getReg .x11) 3)
    (hlS : Apart (u.getReg .x11) 24 (s.getReg .x2 - 2736) 1024)
    (hlo : Apart (s.getReg .x2 - BitVec.ofNat 64 K) 24 (u.getReg .x11) 24)
    (hrr : ValidMemRange (u.getReg .x12) 3)
    (hrS : Apart (u.getReg .x12) 24 (s.getReg .x2 - 2736) 1024)
    (hro : Apart (s.getReg .x2 - BitVec.ofNat 64 K) 24 (u.getReg .x12) 24) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Base s v ∧
      DFrame u v (W10 s) ∧ heapNext v = heapNext u ∧
      DFrame u v (fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 K) 24 ∨
        Within a (s.getReg .x2 - 2736) 1024) ∧
      eAt v (s.getReg .x2 - BitVec.ofNat 64 K) = eAt u (u.getReg .x11) * eAt u (u.getReg .x12)) ∨
      Dead Image.code v) := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  simp only [stackLo] at hnx
  unfold verifyLayerStack at hb hnx
  obtain ⟨hK1, hK2, hK3⟩ := hK
  have hmp : MulPre u := mul_pre hpre B.x2 (B.rodata hpre) K hx10 (by omega) hK2 hK3 hl hlS
    (by rw [hx10]; exact hlo) hrr hrS (by rw [hx10]; exact hro)
  obtain ⟨v, hrv, ⟨hpc', hp, post⟩ | hd⟩ := hM.call hr hpc hmp
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have F := mul_frame B.x2 post
  rw [hx10] at F
  have V := post.value
  rw [hx10] at V
  have x2v : v.getReg .x2 = s.getReg .x2 - 1712 := (hp.reg .x2).trans B.x2
  have F10 : DFrame u v (W10 s) := F.mono fun a h ↦ by
    rcases h with h | h
    · exact hKw a h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [h, hb]))))
  have hN : v.getMem nextAddr = u.getMem nextAddr := F _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hi, hw, hb, hnx, hK1, hK2]
  have hN' : heapNext v = heapNext u := by simp only [heapNext, hN]
  have Bv : Base s v := B.next hpre x2v ⟨by rw [hN']; exact B.heap.lo, by rw [hN']; exact B.heap.hi⟩
    (le_of_eq hN'.symm) F10 fun a h ↦ w10_lw hpre h
  exact ⟨v, hrv, Or.inl ⟨hpc', hp, Bv, F10, hN', F, V⟩⟩

/-- An `E` in the frame apart from a `mul`'s result keeps its value. -/
theorem mulF_keep {s u v : MachineState} (hpre : VerifyLayerPre s) {K : Nat}
    (F : DFrame u v (fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 K) 24 ∨
      Within a (s.getReg .x2 - 2736) 1024)) (hK : K ≤ 1712) {y : Word}
    (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat) (h2 : y.toNat + 24 ≤ (s.getReg .x2).toNat)
    (hy : y.toNat + 24 ≤ (s.getReg .x2).toNat - K ∨ (s.getReg .x2).toNat - K + 24 ≤ y.toNat) :
    eAt v y = eAt u y := by
  have hb := bounds hpre
  exact F.eAt fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, h1, h2, hy, hb, hK]

/-- The second check's first products, at `0x8000fac0`. -/
structure P1 (s v : MachineState) (ip : Word) (c : E) (point : List E) (scale lv : E)
    (lp t : List E) (tp tn : Word) : Prop where
  pc : v.pc = 0x8000fac0
  base : Base s v
  fx : Fx s v ip c point scale lv lp t tp tn
  x8 : v.getReg .x8 = (limbs lv).1
  x21 : v.getReg .x21 = (limbs lv).2.1
  x9 : v.getReg .x9 = (limbs lv).2.2
  x22 : v.getReg .x22 = s.getReg .x11
  x26 : v.getReg .x26 = 16
  x24 : v.getReg .x24 = tp
  x19 : v.getReg .x19 = tn
  x25 : v.getReg .x25 = v.getMem (s.getReg .x2 - 1600)
  x18 : v.getReg .x18 = v.getMem (s.getReg .x2 - 1624)
  tn3 : tn.toNat = 3
  e1560 : eAt v (s.getReg .x2 - 152) =
    scale * atLocalRust (wOf s) (eqKernelRust (lp.take 6)) (eqKernelRust (lp.drop 6))
  e1584 : eAt v (s.getReg .x2 - 128) = sumE (instanceWeightsRust c) * t.getD 0 0
  e960 : eAt v (s.getReg .x2 - 752) = sumE (instanceWeightsRust c) + t.getD 1 0
  rest : Rest s v (rest10 s c point scale lv lp t)

set_option maxHeartbeats 16000000 in
/-- `0x8000fa34`: `at_local` into `f + 192`, `scale * at_local`; `0x8000fa58`: `kappa * t[0]`;
`0x8000fa88`: `kappa + t[1]`; `t` checked to have three elements. -/
theorem c2a (hM : MulSpec) {s v : MachineState} {ip : Word} {c : E} {point lp t : List E}
    {scale lv : E} {tp tn : Word} (hpre : VerifyLayerPre s)
    (K : K10 s v ip c point scale lv lp t tp tn) :
    ∃ u, Reaches Image.code v u ∧ (P1 s u ip c point scale lv lp t tp tn ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have B := K.base
  have X := K.fx
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hlo := hpre.heap.lo
  simp only [stackLo] at hab hnx
  unfold verifyLayerStack at hb hab hnx
  have tn3 : tn.toNat = 3 := by rw [← X.tl, ← X.tE, eListAt_length]
  have tB := X.tB
  rw [tn3] at tB
  have ta := tB.1
  have tb : heapNext s ≤ tp.toNat ∧ tp.toNat + 24 * 3 ≤ heapNext v := by
    rcases tB.2 with h | h
    · omega
    · exact h
  have hHv := B.heap.hi
  have tR : Region tp 72 := by simp only [Region, Mapped]; addr_omega [ta, tb, hHv, hlo]
  have tE := X.tE
  rw [tn3] at tE
  -- `0x8000fa34`: `at_local` into `f + 192`, `mul(f + 1560, scale, f + 192)`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000fa34_spec K.pc (by
    rv_eval [B.x2]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b8000fa34_keeps h₁
  have f₁ := b8000fa34_frame h₁ (by rw [B.x2]; addr_omega [hb])
  rw [B.x2] at f₁
  rv_eval [] at f₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ : Base s t₁ := B.slots hpre x2₁ f₁ (by addr_omega [hb]) (by addr_omega [hb])
  have hN₁ : heapNext t₁ = heapNext v := by
    simp only [heapNext]; rw [f₁ _ (by addr_omega [hb, hnx])]
  have F₁ : DFrame v t₁ (W10 s) := (DFrame.of_memFrame f₁).mono fun a h ↦
    Or.inl (by addr_omega [h, hb])
  have X₁ := X.keep hpre B.heap B₁.heap (le_of_eq hN₁.symm) F₁
  have m192 := b8000fa34_m_x2_192 h₁
  have m200 := b8000fa34_m_x2_200 h₁
  have m208 := b8000fa34_m_x2_208 h₁
  rw [B.x2] at m192 m200 m208
  rv_eval [] at m192 m200 m208
  have eA : eAt t₁ (s.getReg .x2 - 1520) =
      atLocalRust (wOf s) (eqKernelRust (lp.take 6)) (eqKernelRust (lp.drop 6)) :=
    eAt_eq_of_limbs (by rv_eval [m192, m200, m208]; exact K.acc)
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 152 := by rw [b8000fa34_x10 h₁, B.x2]; rv_eval []
  have x11₁ : t₁.getReg .x11 = s.getReg .x2 - 1472 := by rw [b8000fa34_x11 h₁, B.x2]; rv_eval []
  have x12₁ : t₁.getReg .x12 = s.getReg .x2 - 1520 := by rw [b8000fa34_x12 h₁, B.x2]; rv_eval []
  obtain ⟨t₂, hr₂, ⟨hpc₂, hp₂, B₂, F₂, hN₂, G₂, V₂⟩ | hd⟩ := mulF hM hpre B₁ hr₁ (b8000fa34_pc h₁)
    152 x10₁ (by decide) (fun a h ↦ Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))))
    (by rw [x11₁]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x11₁]; addr_omega [hb]) (by rw [x11₁]; addr_omega [hb])
    (by rw [x12₁]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x12₁]; addr_omega [hb]) (by rw [x12₁]; addr_omega [hb])
  swap
  · exact ⟨t₂, hr₂, Or.inr hd⟩
  have e1560₂ : eAt t₂ (s.getReg .x2 - 152) =
      scale * atLocalRust (wOf s) (eqKernelRust (lp.take 6)) (eqKernelRust (lp.drop 6)) := by
    refine V₂.trans ?_
    rw [x11₁, x12₁, eA, X₁.k8.scale]
  have X₂ := X₁.keep hpre B₁.heap B₂.heap (le_of_eq hN₂.symm) F₂
  have R₂ : Rest s t₂ (rest10 s c point scale lv lp t) :=
    (K.rest.body hpre B B₁ (F₁.mono fun a h ↦ w10_body hpre h)).body hpre B₁ B₂
      (F₂.mono fun a h ↦ w10_body hpre h)
  have r2 (r : Reg) (hr : r ∈ [Reg.x8, .x19, .x21, .x22, .x23, .x24, .x26, .x27]) :
      t₂.getReg r = v.getReg r := by
    rw [hp₂ r (reg_sub (by decide) hr), k₁ r (reg_sub (by decide) hr)]
  have tn0 : tn ≠ 0 := fun h ↦ by rw [h] at tn3; exact absurd tn3 (by decide)
  have tn1 : tn ≠ 1 := fun h ↦ by rw [h] at tn3; exact absurd tn3 (by decide)
  -- `0x8000fa54`: `t` not empty
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000fa54_spec
    (by rw [hpc₂, returnAddress_eq, b8000fa34_x1 h₁]; decide) trivial
  have pc₃ := b8000fa54_pc_not_taken h₃ (by rw [r2 .x27 (by decide), K.x27]; exact tn0)
  have k₃ := b8000fa54_keeps h₃
  have hm₃ := b8000fa54_mem_same h₃
  -- `0x8000fa58`: `mul(f + 1584, kappa, t[0])`
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000fa58_spec pc₃ trivial
  have k₄ := b8000fa58_keeps h₄
  have hm₄ := b8000fa58_mem_same h₄
  have hm24 (a : Word) : t₄.getMem a = t₂.getMem a := by rw [hm₄, hm₃]
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1712 := by
    rw [k₄ .x2 (by decide), k₃ .x2 (by decide), B₂.x2]
  have B₄ : Base s t₄ := B₂.same x2₄ hm24
  have hN₄ : heapNext t₄ = heapNext t₂ := by simp only [heapNext, hm24]
  have x10₄ : t₄.getReg .x10 = s.getReg .x2 - 128 := by
    rw [b8000fa58_x10 h₄, k₃ .x2 (by decide), B₂.x2]; rv_eval []
  have x11₄ : t₄.getReg .x11 = s.getReg .x2 - 800 := by
    rw [b8000fa58_x11 h₄, k₃ .x2 (by decide), B₂.x2]; rv_eval []
  have x12₄ : t₄.getReg .x12 = tp := by
    rw [b8000fa58_x12 h₄, k₃ .x24 (by decide), r2 .x24 (by decide), K.x24]
  have hN2v : heapNext t₂ = heapNext v := by rw [hN₂, hN₁]
  obtain ⟨t₅, hr₅, ⟨hpc₅, hp₅, B₅, F₅, hN₅, G₅, V₅⟩ | hd⟩ := mulF hM hpre B₄ hr₄ (b8000fa58_pc h₄)
    128 x10₄ (by decide) (fun a h ↦ Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))))
    (by rw [x11₄]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x11₄]; addr_omega [hb]) (by rw [x11₄]; addr_omega [hb])
    (by rw [x12₄]; exact heap_vmr (by addr_omega [tb, hlo]) (by addr_omega [tb, hHv]) ta)
    (by rw [x12₄]; addr_omega [tb, hHv, hab, hb]) (by rw [x12₄]; addr_omega [tb, hHv, hab, hb])
  swap
  · exact ⟨t₅, hr₂.trans (hr₃.trans hr₅), Or.inr hd⟩
  have X₄ := X₂.keep hpre B₂.heap B₄.heap (le_of_eq hN₄.symm) (DFrame.of_same hm24 _)
  have tE₄ : eListAt t₄ tp 3 = t := by rw [← tn3]; exact X₄.tE
  have e1584₅ : eAt t₅ (s.getReg .x2 - 128) = sumE (instanceWeightsRust c) * t.getD 0 0 := by
    refine V₅.trans ?_
    rw [x11₄, x12₄, X₄.k8.kappa, ← tE₄, eListAt_getD_lt _ _ (by decide : 0 < 3), Nat.mul_zero,
      add_ofNat_zero]
  have e1560₅ : eAt t₅ (s.getReg .x2 - 152) = scale *
      atLocalRust (wOf s) (eqKernelRust (lp.take 6)) (eqKernelRust (lp.drop 6)) := by
    rw [mulF_keep hpre G₅ (by decide) (by addr_omega [hb]) (by addr_omega [hb])
      (Or.inl (by addr_omega [hb])), eAt_of_same hm24]
    exact e1560₂
  have X₅ := X₄.keep hpre B₄.heap B₅.heap (le_of_eq hN₅.symm) F₅
  have R₅ : Rest s t₅ (rest10 s c point scale lv lp t) :=
    (R₂.keep fun T hT ↦ transcriptAt_congr hm24 hT).body hpre B₄ B₅
      (F₅.mono fun a h ↦ w10_body hpre h)
  have r5 (r : Reg) (hr : r ∈ [Reg.x8, .x21, .x22, .x23, .x24, .x26, .x27]) :
      t₅.getReg r = v.getReg r := by
    rw [hp₅ r (reg_sub (by decide) hr), k₄ r (reg_sub (by decide) hr),
      k₃ r (reg_sub (by decide) hr), r2 r (reg_sub (by decide) hr)]
  have x19₅ : t₅.getReg .x19 = tn := by
    rw [hp₅.reg .x19, b8000fa58_x19 h₄, k₃ .x27 (by decide), r2 .x27 (by decide), K.x27]
  have x2₅ : t₅.getReg .x2 = s.getReg .x2 - 1712 := B₅.x2
  -- `0x8000fa70`: the value's limbs and `eq_lane` back in registers, `t` of at least two
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000fa70_spec
    (by rw [hpc₅, returnAddress_eq, b8000fa58_x1 h₄]; decide) (by
      rv_eval [x2₅]; and_intros <;> valid_access hpre.stack.valid [hb])
  have pc₆ := b8000fa70_pc_not_taken h₆ (by rw [r5 .x27 (by decide), K.x27]; exact tn1)
  have k₆ := b8000fa70_keeps h₆
  have hm₆ := b8000fa70_mem_same h₆
  -- `0x8000fa88`: `kappa + t[1]` into `f + 960`, `t` of at least three
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000fa88_spec pc₆ (by
    rv_eval [k₆ .x2 (by decide), x2₅, k₆ .x24 (by decide), r5 .x24 (by decide), K.x24]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid tR ?_ ?_ ?_ <;> addr_omega [tR]))
  have pc₇ := b8000fa88_pc_not_taken h₇ (by
    rw [k₆ .x19 (by decide), x19₅, tn3]; decide)
  have k₇ := b8000fa88_keeps h₇
  have f₇ := b8000fa88_frame h₇ (by rw [k₆ .x2 (by decide), x2₅]; addr_omega [hb])
  rw [k₆ .x2 (by decide), x2₅] at f₇
  rv_eval [] at f₇
  have x2₇ : t₇.getReg .x2 = s.getReg .x2 - 1712 := by rw [k₇ .x2 (by decide), k₆ .x2 (by decide), x2₅]
  have B₆ : Base s t₆ := B₅.same (by rw [k₆ .x2 (by decide), x2₅]) hm₆
  have B₇ : Base s t₇ := B₆.slots hpre x2₇ f₇ (by addr_omega [hb]) (by addr_omega [hb])
  have hN₆ : heapNext t₆ = heapNext t₅ := by simp only [heapNext, hm₆]
  have hN₇ : heapNext t₇ = heapNext t₆ := by
    simp only [heapNext]; rw [f₇ _ (by addr_omega [hb, hnx])]
  have F₇ : DFrame t₆ t₇ (W10 s) := (DFrame.of_memFrame f₇).mono fun a h ↦
    Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
  have X₆ := X₅.keep hpre B₅.heap B₆.heap (le_of_eq hN₆.symm) (DFrame.of_same hm₆ _)
  have X₇ := X₆.keep hpre B₆.heap B₇.heap (le_of_eq hN₇.symm) F₇
  have m960 := b8000fa88_m_x2_960 h₇
  have m968 := b8000fa88_m_x2_968 h₇
  have m976 := b8000fa88_m_x2_976 h₇
  have x24₆ : t₆.getReg .x24 = tp := by rw [k₆ .x24 (by decide), r5 .x24 (by decide), K.x24]
  rw [k₆ .x2 (by decide), x2₅, x24₆] at m960 m968 m976
  rv_eval [hm₆] at m960 m968 m976
  have tE₅ : eListAt t₅ tp 3 = t := by rw [← tn3]; exact X₅.tE
  have lk := limbs_eAt t₅ (s.getReg .x2 - 800)
  rw [X₅.k8.kappa] at lk
  have ht1 : eAt t₅ (tp + 24) = t.getD 1 0 := by
    have := eListAt_getD_lt t₅ tp (by decide : 1 < 3)
    rw [tE₅] at this
    exact this.symm
  have lt1 := limbs_eAt t₅ (tp + 24)
  rw [ht1] at lt1
  rv_eval [] at lk lt1
  have e960₇ : eAt t₇ (s.getReg .x2 - 752) = sumE (instanceWeightsRust c) + t.getD 1 0 := by
    apply eAt_eq_of_limbs
    rw [limbs_add, lk, lt1]
    rv_eval [m960, m968, m976]
  refine ⟨t₇, hr₂.trans (hr₃.trans (hr₅.trans (hr₆.trans hr₇))), Or.inl {
    pc := pc₇
    base := B₇
    fx := X₇
    x8 := by rw [k₇ .x8 (by decide), k₆ .x8 (by decide), r5 .x8 (by decide), K.x8]
    x21 := by rw [k₇ .x21 (by decide), b8000fa70_x21 h₆, x2₅]; rv_eval [X₅.m8]
    x9 := by rw [k₇ .x9 (by decide), b8000fa70_x9 h₆, x2₅]; rv_eval [X₅.m16]
    x22 := by rw [k₇ .x22 (by decide), k₆ .x22 (by decide), r5 .x22 (by decide), K.x22]
    x26 := by rw [k₇ .x26 (by decide), k₆ .x26 (by decide), r5 .x26 (by decide), K.x26]
    x24 := by rw [k₇ .x24 (by decide), x24₆]
    x19 := by rw [k₇ .x19 (by decide), k₆ .x19 (by decide), x19₅]
    x25 := by
      rw [k₇ .x25 (by decide), b8000fa70_x25 h₆, x2₅, f₇ (s.getReg .x2 - 1600) (by addr_omega [hb]),
        hm₆]
      rv_eval []
    x18 := by
      rw [k₇ .x18 (by decide), b8000fa70_x18 h₆, x2₅, f₇ (s.getReg .x2 - 1624) (by addr_omega [hb]),
        hm₆]
      rv_eval []
    tn3 := tn3
    e1560 := by
      rw [(DFrame.of_memFrame f₇).eAt (fun i hi hw ↦ by addr_omega [hw, hi, hb]), eAt_of_same hm₆]
      exact e1560₅
    e1584 := by
      rw [(DFrame.of_memFrame f₇).eAt (fun i hi hw ↦ by addr_omega [hw, hi, hb]), eAt_of_same hm₆]
      exact e1584₅
    e960 := e960₇
    rest := (R₅.keep fun T hT ↦ transcriptAt_congr hm₆ hT).body hpre B₆ B₇
      (F₇.mono fun a h ↦ w10_body hpre h) }⟩

end Rv64Verifier.Gkr.Layer
