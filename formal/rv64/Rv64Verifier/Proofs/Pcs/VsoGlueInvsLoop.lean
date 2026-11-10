import Rv64Verifier.Proofs.Pcs.VsoGlueBase
import Rv64Verifier.Proofs.Field.Contracts

/-!
# `verify_stacked_opening`'s final level: the roots' inverses, the loop

At `0x8000be28` the loop stores `K::inv` of root `k` (at `s2`, from `s5`) into the inverses' buffer
(at `s0`, from `ip`), until `s2` reaches `s1`, the roots' end. `IL` is its invariant: the first `k`
inverses written, the roots and `GK2` kept.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  Rv64Verifier.FieldContracts LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

section
variable {s v w : MachineState}

/-- One more step whose writes are the loop's, the heap from `v` on. -/
theorem GS.stepV (hpre : VsoPre s) (h : GS s v w) {w' : MachineState} {X : Word → Prop}
    (hX : DFrame w w' X) (hXs : ∀ a, X a → GLW s (heapNext v) (w'.getMem nextAddr) a)
    (hheap : HeapOk w') (hmono : heapNext w ≤ heapNext w') (hsp : w'.getReg .x2 = w.getReg .x2) :
    GS s v w' := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsv := h.sv
  have hhi := hheap.hi
  refine ⟨Inv.step' hpre h.inv hX (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl hmono hhi hsp,
    (h.fr.mono fun a ha ↦ ha.mono (Nat.le_refl _) hmono).trans hX (fun a ha ↦ hXs a ha), hheap,
    Nat.le_trans h.mono hmono, hsp.trans h.sp, h.sv⟩
  · rcases hXs a ha with ha | ha | ha | ha | ha | ha | ha
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨Nat.le_trans hsv ha.1, ha.2⟩))
  · rcases hXs a ha with ha | ha | ha | ha | ha | ha | ha
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx]
    · have hab := hpre.stack.above
      rw [stackLo_vso] at hab
      simp only [heapEnd] at hhi hab
      addr_omega [ha.2, hb, hhi, hab]

end

/-- At `0x8000be28` (or `0x8000be44`), `k` inverses written from `ip`. -/
structure IL (s v w t : MachineState) (n : ℕ) (ip : Word) (k : ℕ) : Prop where
  gs : GS s v t
  fr : DFrame w t (GLW s (heapNext w) (t.getMem nextAddr))
  wt : heapNext w ≤ heapNext t
  kle : k ≤ n + 1
  x8 : t.getReg .x8 = ip + BitVec.ofNat 64 (8 * k)
  x18 : t.getReg .x18 = w.getReg .x21 + BitVec.ofNat 64 (8 * k)
  x9 : t.getReg .x9 = w.getReg .x21 + BitVec.ofNat 64 (8 * (n + 1))
  x19 : t.getReg .x19 = w.getReg .x19
  x20 : t.getReg .x20 = w.getReg .x20
  x21 : t.getReg .x21 = w.getReg .x21
  x23 : t.getReg .x23 = w.getReg .x23
  x26 : t.getReg .x26 = w.getReg .x26
  x22 : t.getReg .x22 = 0
  m784 : t.getMem (s.getReg .x2 - 784) = ip
  ipb : ip.toNat % 8 = 0 ∧ heapNext w ≤ ip.toNat ∧ ip.toNat + 8 * (n + 1) ≤ heapNext t
  done : ∀ i < k, BF64.ofBitVec (t.getMem (ip + BitVec.ofNat 64 (8 * i))) =
    (BF64.ofBitVec (w.getMem (w.getReg .x21 + BitVec.ofNat 64 (8 * i))))⁻¹
  keep : ∀ y, GK2 s y → t.getMem y = w.getMem y

/-- One inverse: `0x8000be28`, `K::inv`, `0x8000be34`. -/
theorem invStep (hK : KInvSpec) {s v w t : MachineState} {n : ℕ} {ip : Word} {k : ℕ} {rs : List K}
    (hpre : VsoPre s) (hB : QB s v w n rs) (h : IL s v w t n ip k) (hpc : t.pc = 0x8000be28)
    (hk : k < n + 1) :
    ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨ (IL s v w t' n ip (k + 1) ∧
      t'.pc = if k + 1 = n + 1 then 0x8000be44 else 0x8000be28)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.gs.sp
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  have hro := hst.rodata
  rw [stackLo_vso] at hro
  have hhs := hpre.heap.lo
  have hsv := h.gs.sv
  have hvw := hB.gs.mono
  have hhw := hB.gs.heap.hi
  have hht := h.gs.heap.hi
  simp only [heapEnd] at hhw hht
  have hwt := h.wt
  obtain ⟨hr8, hr1, hr2⟩ := hB.x21
  obtain ⟨hi8, hi1, hi2⟩ := h.ipb
  obtain ⟨rp, hrp⟩ : ∃ rp, w.getReg .x21 = rp := ⟨_, rfl⟩
  have hx18 := h.x18
  have hx9 := h.x9
  have hdone := h.done
  rw [hrp] at hr8 hr1 hr2 hx18 hx9 hdone
  have hRr : Region rp (8 * (n + 1)) := heap_region
    (by simp only [heapStart] at hhs; omega) (by simp only [heapEnd]; omega) hr8
  have hRi : Region ip (8 * (n + 1)) := heap_region
    (by simp only [heapStart] at hhs; omega) (by simp only [heapEnd]; omega) hi8
  -- `0x8000be28`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000be28_spec hpc (by
    rv_eval [hx18]
    exact Region.valid hRr (by addr_omega [hr2, hhw, hk]) (by addr_omega [hr2, hhw, hk])
      (by addr_omega [hr2, hhw, hr8, hk]))
  have hm₁ := b8000be28_mem_same h₁
  have k₁ := b8000be28_keeps h₁
  have G₁ := h.gs.same hpre hm₁ (k₁ .x2 (by decide))
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₁.sp
  have hsl : stackLo t₁ kInvStack = s.getReg .x2 - 1184 := by
    simp only [stackLo, sp₁, kInvStack, baseMulStack, Nat.reduceAdd]; rv_eval []
  have hpreK : KInvPre t₁ := {
    stack := ⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [sp₁]; addr_omega [hb]⟩
    pool := poolOk_of_rodata (InvR.rodata' hpre G₁.inv) (by
      rw [hsl]; simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack,
        nextScalarsStack, shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack,
        memStack] at hro; addr_omega [hro, hb]) }
  obtain ⟨t₂, r₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hK.call (Reaches.refl t₁) (b8000be28_pc h₁) hpreK
  swap
  · exact ⟨t₂, r₁.trans r₂, Or.inl hdead⟩
  have F₂ := DFrame.of_memFrame hpost₂.frame
  rw [hsl] at F₂
  obtain ⟨G₂, n₂⟩ := G₁.stepS hpre F₂ (fun y hy ↦ Or.inr (Or.inr (Or.inr (Or.inr (by
    addr_omega [hy, hb]))))) (hpres₂ .x2 (by decide))
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₂.sp
  have x8₂ : t₂.getReg .x8 = ip + BitVec.ofNat 64 (8 * k) := by
    rw [hpres₂ .x8 (by decide), k₁ .x8 (by decide), h.x8]
  have x18₂ : t₂.getReg .x18 = rp + BitVec.ofNat 64 (8 * k) := by
    rw [hpres₂ .x18 (by decide), k₁ .x18 (by decide), hx18]
  have x9₂ : t₂.getReg .x9 = rp + BitVec.ofNat 64 (8 * (n + 1)) := by
    rw [hpres₂ .x9 (by decide), k₁ .x9 (by decide), hx9]
  have hn₂ : heapNext t₂ = heapNext t := by simp only [heapNext, n₂, hm₁]
  -- `0x8000be34`
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000be34_spec
    (by rw [hpc₂, returnAddress_eq, b8000be28_x1 h₁]; decide) (by
      rv_eval [x8₂]
      exact Region.valid hRi (by addr_omega [hi2, hht, hk]) (by addr_omega [hi2, hht, hk])
        (by addr_omega [hi2, hht, hi8, hk]))
  have k₃ := b8000be34_keeps h₃
  have F₃ : DFrame t₂ t₃ fun y ↦ Within y (ip + BitVec.ofNat 64 (8 * k)) 8 := by
    have := DFrame.of_memFrame (b8000be34_frame h₃ (by rw [x8₂]; addr_omega [hi2, hht, hk]))
    rw [x8₂] at this; exact this
  have nx₃ : t₃.getMem nextAddr = t₂.getMem nextAddr := F₃ _ fun i hi hw ↦ by
    addr_omega [hw, hi, hi2, hht, hk]
  have hn₃ : heapNext t₃ = heapNext t := by simp only [heapNext, nx₃]; exact hn₂
  have hXv (y : Word) (hy : Within y (ip + BitVec.ofNat 64 (8 * k)) 8) :
      GLW s (heapNext w) (t₃.getMem nextAddr) y :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hy, hi1, hi2, hht, hk],
      by have : heapNext t₃ = (t₃.getMem nextAddr).toNat := rfl; addr_omega [hy, hi1, hi2, hht, hk, hn₃, this]⟩)))))
  have G₃ := G₂.stepV hpre F₃ (fun y hy ↦ (hXv y hy).mono hvw (Nat.le_refl _))
    ⟨by rw [hn₃]; exact h.gs.heap.lo, by rw [hn₃]; exact h.gs.heap.hi⟩ (by rw [hn₃, hn₂])
    (k₃ .x2 (by decide))
  -- the frame from `w`
  have F : DFrame w t₃ (GLW s (heapNext w) (t₃.getMem nextAddr)) := by
    have e : t₃.getMem nextAddr = t.getMem nextAddr := by rw [nx₃, n₂, hm₁]
    refine ((h.fr.mono fun a ha ↦ ?_).trans ((DFrame.of_same hm₁ _).trans F₂ fun a h ↦ h) ?_).trans
      F₃ hXv
    · rw [e]; exact ha
    · intro a ha; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))
  have kt (y : Word) (hy : ¬ Within y (ip + BitVec.ofNat 64 (8 * k)) 8)
      (hy' : y.toNat + 8 ≤ (s.getReg .x2 - 1184).toNat ∨ (s.getReg .x2 - 1040).toNat ≤ y.toNat)
      (h8 : y.toNat % 8 = 0) (hk8 : (ip + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0) :
      t₃.getMem y = t.getMem y := by
    rw [F₃ y fun i hi hw ↦ hy (by addr_omega [hw, hi, h8, hk8]), F₂ y fun i hi hw ↦ by
      rcases hy' with hy' | hy' <;> addr_omega [hw, hi, hy', hb, h8], hm₁]
  have hk8 : (ip + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := by addr_omega [hi8, hi2, hht, hk]
  have hpc₃ := b8000be34_pc_taken h₃
  have hpc₃' := b8000be34_pc_not_taken h₃
  rw [x18₂, x9₂] at hpc₃ hpc₃'
  refine ⟨t₃, r₁.trans (r₂.trans r₃), Or.inr ⟨{
    gs := G₃
    fr := F
    wt := by rw [hn₃]; exact hwt
    kle := by omega
    x8 := by rw [b8000be34_x8 h₃, x8₂]; addr_omega [hi2, hht, hk]
    x18 := by rw [b8000be34_x18 h₃, x18₂, hrp]; addr_omega [hr2, hhw, hk]
    x9 := by rw [k₃ .x9 (by decide), x9₂, hrp]
    x19 := by rw [k₃ .x19 (by decide), hpres₂ .x19 (by decide), k₁ .x19 (by decide), h.x19]
    x20 := by rw [k₃ .x20 (by decide), hpres₂ .x20 (by decide), k₁ .x20 (by decide), h.x20]
    x21 := by rw [k₃ .x21 (by decide), hpres₂ .x21 (by decide), k₁ .x21 (by decide), h.x21]
    x23 := by rw [k₃ .x23 (by decide), hpres₂ .x23 (by decide), k₁ .x23 (by decide), h.x23]
    x26 := by rw [k₃ .x26 (by decide), hpres₂ .x26 (by decide), k₁ .x26 (by decide), h.x26]
    x22 := by rw [k₃ .x22 (by decide), hpres₂ .x22 (by decide), k₁ .x22 (by decide), h.x22]
    m784 := by
      rw [kt _ (by addr_omega [hi2, hht, hk, hab, hb]) (Or.inr (by addr_omega [hb]))
        (by addr_omega [hb]) hk8]
      exact h.m784
    ipb := ⟨hi8, hi1, by rw [hn₃]; exact hi2⟩
    done := fun i hi ↦ by
      by_cases hik : i = k
      · subst hik
        have m := b8000be34_m_x8_0 h₃
        rw [x8₂, hpost₂.value, b8000be28_x10 h₁, hx18] at m
        rw [hrp, m, h.fr _ fun j hj ↦ GLW.low hpre
          (by simp only [heapEnd]; omega) (by addr_omega [hj, hr2, hhw, hk])]
        simp
      · rw [kt _ (by addr_omega [hi2, hht, hk, hi, hik]) (Or.inl (by addr_omega [hi2, hht, hk, hab, hb, hi]))
          (by addr_omega [hi8, hi2, hht, hk, hi]) hk8]
        exact h.done i (by omega)
    keep := fun y hy ↦ by
      have hy' := hy
      simp only [GK2, GK] at hy'
      have H : ¬ Within y (ip + BitVec.ofNat 64 (8 * k)) 8 ∧ (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
          y.toNat % 8 = 0 := by
        rcases hy' with (hy' | hy' | hy' | hy' | hy' | hy' | hy' | hy' | hy') | hy' | hy' | hy' | hy' <;>
          subst hy' <;> exact ⟨by addr_omega [hi2, hht, hk, hab, hb], by addr_omega [hb],
            by addr_omega [hb]⟩
      rw [kt _ H.1 (Or.inr H.2.1) H.2.2 hk8]
      exact h.keep y hy }, ?_⟩⟩
  by_cases he : k + 1 = n + 1
  · simp only [he, ↓reduceIte]
    exact hpc₃' (by rw [show k = n by omega]; addr_omega [hr2, hhw])
  · simp only [he, ↓reduceIte]
    exact hpc₃ (by addr_omega [hr2, hhw, hk, he])

end Rv64Verifier.Proofs.Pcs.Vso
