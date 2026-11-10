import Rv64Verifier.Proofs.Gkr.OpenMid
import Rv64Verifier.Proofs.Gkr.OpenRow

/-!
# `keccak::open`: the zeroed row, and the way into the loops

`0x80010360` zeroes the row at `f + 168` (`zero_loop`); `0x80010374` and `0x8001037c` skip the
loops when `count` or the weights are empty (the row is then `openRow`'s already), and
`0x80010388` sets the loops' registers (`dispatch`). Everything from here to the end writes the
frame only, in the ranges of `LW`, which keep `Mid` (`Mid.keep`).
-/

namespace Rv64Verifier.Gkr.Open
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F75
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- What the rest of `open` writes before the copy out: the loops' slots `f + 40 .. f + 112`
(but `first` and `count`), the row, the scale at `f + 1728` and the callees' stack. -/
@[rv_addr] def LW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1816) 24 ∨ Within a (s.getReg .x2 - 1776) 32 ∨
    Within a (s.getReg .x2 - 1688) 1536 ∨ Within a (s.getReg .x2 - 128) 24 ∨
    Within a (stackLo s openStack) 1632

theorem Mid.keep {s m u v : MachineState} (hpre : OpenPre s) (h : Mid s m u)
    (hf : DFrame u v (LW s)) (hx2 : v.getReg .x2 = s.getReg .x2 - 1856) : Mid s m v := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hHu := h.heap.hi
  have keep (y : Word) (h1 : (s.getReg .x2).toNat - 1856 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h3 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1816 ∨
        (s.getReg .x2).toNat - 1792 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 1776 ∨
        (s.getReg .x2).toNat - 1744 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 1688 ∨
        (s.getReg .x2).toNat - 152 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 128 ∨
        (s.getReg .x2).toNat - 104 ≤ y.toNat) :
      v.getMem y = u.getMem y :=
    hf y fun i hi hw ↦ by addr_omega [hw, hi, h1, h2, h3, hb]
  have hN : v.getMem nextAddr = u.getMem nextAddr :=
    hf _ fun i hi hw ↦ by addr_omega [hw, hi, hb, hnx]
  have hNe : heapNext v = heapNext u := by simp only [heapNext, hN]
  have hhead (a : Word) (h1 : (s.getReg .x2).toNat - 1744 ≤ a.toNat)
      (h2 : a.toNat + 24 ≤ (s.getReg .x2).toNat - 1688) :
      ∀ i < 24, ¬ LW s (a + BitVec.ofNat 64 i) := fun i hi hw ↦ by addr_omega [hw, hi, h1, h2, hb]
  have hheap : ∀ y : Word, y.toNat < heapNext u → ¬ LW s y := fun y hy hw ↦ by
    addr_omega [hw, hy, hb, hab, hHu]
  have hv := h.value
  unfold Rv64Verifier.eAt at hv
  exact {
    x2 := hx2
    saved := h.saved.keep (by addr_omega [hb]) fun y h1 h2 ↦
      keep y (by addr_omega [h1, hb]) h2 (by omega)
    cap := (keep _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans
      h.cap
    ptr := (keep _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans
      h.ptr
    len := (keep _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans
      h.len
    out := (keep _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans
      h.out
    first := (keep _ (by addr_omega [hb]) (by addr_omega [hb])
      (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))).trans h.first
    count := (keep _ (by addr_omega [hb]) (by addr_omega [hb])
      (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))).trans h.count
    value := by
      unfold Rv64Verifier.eAt
      rw [keep _ (by addr_omega [hb]) (by addr_omega [hb])
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)))),
        keep (s.getReg .x2 - 152 + 8) (by addr_omega [hb]) (by addr_omega [hb])
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)))),
        keep (s.getReg .x2 - 152 + 16) (by addr_omega [hb]) (by addr_omega [hb])
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))))]
      exact hv
    sg := newVecE_keep' h.sg hf (le_of_eq hNe.symm)
      (hhead _ (by addr_omega [hb]) (by addr_omega [hb])) hheap
    sl := newVecE_keep' h.sl hf (le_of_eq hNe.symm)
      (hhead _ (by addr_omega [hb]) (by addr_omega [hb])) hheap
    heap := ⟨hNe ▸ h.heap.lo, hNe ▸ h.heap.hi⟩
    mono := hNe ▸ h.mono
    frame := (h.frame.mono fun a ha ↦ SW.mono (le_refl _) (le_of_eq hNe.symm) ha).trans hf
      fun a ha ↦ Or.inl (by addr_omega [ha, hb]) }

theorem limbs_zero : Model.limbs (0 : E) = (0, 0, 0) := by
  decide +kernel

/-- The zeroing loop's head, `k` elements zeroed. -/
structure ZI (s m u : MachineState) (k : Nat) : Prop where
  pc : u.pc = 0x80010360
  mid : Mid s m u
  x10 : u.getReg .x10 = s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * k)
  x11 : u.getReg .x11 = s.getReg .x2 - 152
  x21 : u.getReg .x21 = s.getReg .x14
  lt : k < 64
  zeros : ∀ j < k, eAt u (s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * j)) = 0

/-- Past the zeroing loop. -/
structure ZD (s m u : MachineState) : Prop where
  pc : u.pc = 0x80010374
  mid : Mid s m u
  x21 : u.getReg .x21 = s.getReg .x14
  row : eListAt u (s.getReg .x2 - 1688) 64 = List.replicate 64 0

theorem zero_loop {s m : MachineState} (hpre : OpenPre s) :
    ∀ u, (∃ k, ZI s m u k) → ∃ v, Reaches Image.code u v ∧ ZD s m v := by
  have hb := bounds hpre
  refine Reaches.loop _ (fun u ↦ (s.getReg .x2 - 152 - u.getReg .x10).toNat) (ZD s m) ?_
  rintro u ⟨k, Z⟩
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b80010360_spec Z.pc (by
    rv_eval [Z.x10]
    have := Z.lt
    and_intros <;> valid_access hpre.stack.valid [hb, this])
  have kp := b80010360_keeps h
  have f := b80010360_frame h (by rw [Z.x10]; addr_omega [hb, Z.lt])
  rw [Z.x10] at f
  have m0 := b80010360_m_x10_0 h
  have m8 := b80010360_m_x10_8 h
  have m16 := b80010360_m_x10_16 h
  rw [Z.x10] at m0 m8 m16
  have x2v : v.getReg .x2 = s.getReg .x2 - 1856 := (kp .x2 (by decide)).trans Z.mid.x2
  have M : Mid s m v := Z.mid.keep hpre ((DFrame.of_memFrame f).mono fun a ha ↦ by
    have := Z.lt
    addr_omega [ha, hb, this]) x2v
  have zk : eAt v (s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * k)) = 0 := by
    apply eAt_eq_of_limbs
    rw [limbs_zero, m0, m8, m16]
  have zs : ∀ j < k + 1, eAt v (s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * j)) = 0 := by
    intro j hj
    by_cases hjk : j = k
    · rw [hjk]; exact zk
    · rw [f.eAt (by have := Z.lt; addr_omega [hb, this, hj, hjk])
        (by have := Z.lt; addr_omega [hb, this, hj])]
      exact Z.zeros j (by omega)
  have x21v : v.getReg .x21 = s.getReg .x14 := (kp .x21 (by decide)).trans Z.x21
  have x11v : v.getReg .x11 = s.getReg .x2 - 152 := (kp .x11 (by decide)).trans Z.x11
  by_cases hk : k + 1 = 64
  · refine Or.inl ⟨v, hr, ⟨b80010360_pc_not_taken h (by rw [Z.x10, Z.x11]; addr_omega [hb, hk]),
      M, x21v, ?_⟩⟩
    apply List.ext_getElem (by simp [eListAt_length])
    intro j h1 _
    rw [eListAt_getElem, List.getElem_replicate]
    exact zs j (by rw [eListAt_length] at h1; omega)
  · refine Or.inr ⟨v, hr, ⟨k + 1, ⟨b80010360_pc_taken h
      (by rw [Z.x10, Z.x11]; have := Z.lt; addr_omega [hb, this, hk]), M,
      by rw [b80010360_x10 h, Z.x10]; have := Z.lt; addr_omega [hb, this],
      x11v, x21v, by have := Z.lt; omega, zs⟩⟩, ?_⟩
    rw [b80010360_x10 h, Z.x10]
    have := Z.lt
    addr_omega [hb, this, hk]

/-! ## The claim, still in place -/

theorem claim_keep {s m u : MachineState} (hpre : OpenPre s) (P : P2 s m) (M : Mid s m u) :
    (∀ y : Word, (s.getReg .x14).toNat ≤ y.toNat → y.toNat + 8 ≤ (s.getReg .x14).toNat + 96 →
      u.getMem y = s.getMem y) ∧
    eListAt u (s.getMem (s.getReg .x14 + 56)) (s.getMem (s.getReg .x14 + 64)).toNat =
      (claimAt s (oClaim s)).weights := by
  have hc := hpre.claim
  have hHm := P.heap
  have hHu := M.heap
  have mc : Misses (OpenW s m) (oClaim s) 96 := missOpenW hHm hpre.claimOut hpre.claimValue
    hpre.claimSelf hpre.claimStack hpre.claimFree (by addr_omega [hc])
  have mc' : Misses (SW s m u) (oClaim s) 96 := missSW hHu hpre.claimStack
    (outside_mono hpre.claimFree P.mono) (by addr_omega [hc])
  have wR := hpre.weights
  have wS := hpre.weightsStack
  have wF := hpre.weightsFree
  have wO := hpre.weightsOut
  have wV := hpre.weightsValue
  have wP := hpre.weightsSelf
  simp only [VecRegion, VecApart, VecOutside, vecPtr, vecLen, oClaim, oOut, oValue, oP] at wR wS wF wO wV wP
  rv_eval [] at wR wS wF wO wV wP
  refine ⟨fun y h1 h2 ↦ ?_, ?_⟩
  · rw [M.frame y (mc'.bytes h1 h2 (by addr_omega [hc])), P.frame y (mc.bytes h1 h2 (by addr_omega [hc]))]
  · have e : (claimAt s (oClaim s)).weights =
        eListAt s (s.getMem (s.getReg .x14 + 56)) (s.getMem (s.getReg .x14 + 64)).toNat := by
      simp only [claimAt, vecEs, vecPtr, vecLen, oClaim]; rv_eval []
    rw [e]
    rcases wR with h0 | hR
    · rw [h0]; rfl
    · rw [M.frame.eListAt fun i hi ↦ missSW hHu wS (outside_mono wF P.mono)
          (by addr_omega [hR]) _ (by addr_omega [hi, hR]),
        P.frame.eListAt fun i hi ↦ missOpenW hHm wO wV wP wS wF (by addr_omega [hR]) _
          (by addr_omega [hi, hR])]

/-- What the loops keep, at every head. -/
structure LF (s m u : MachineState) : Prop where
  mid : Mid s m u
  x18 : u.getReg .x18 = s.getReg .x2 - 1672
  x19 : u.getReg .x19 = u.getMem (s.getReg .x2 - 1720)
  x20 : u.getReg .x20 = u.getMem (s.getReg .x2 - 1704)
  x23 : u.getReg .x23 = u.getMem (s.getReg .x2 - 1696)
  sgp : u.getMem (s.getReg .x2 - 1816) = u.getMem (s.getReg .x2 - 1728)
  wp : u.getMem (s.getReg .x2 - 1808) = s.getMem (s.getReg .x14 + 56)
  wl : u.getMem (s.getReg .x2 - 1800) = s.getMem (s.getReg .x14 + 64)

/-- The outer loop's head, `g` segments done. -/
structure OI (s m u : MachineState) (g : Nat) : Prop extends LF s m u where
  pc : u.pc = 0x800103ac
  x26 : u.getReg .x26 = BitVec.ofNat 64 g
  lt : g < (s.getReg .x16).toNat
  wne : (s.getMem (s.getReg .x14 + 64)).toNat ≠ 0
  row : eListAt u (s.getReg .x2 - 1688) 64 =
    outRow (sgOf s) (slOf s m) (claimAt s (oClaim s)).weights (s.getReg .x15).toNat g

theorem atFinal_of_mid {s m x : MachineState} (M : Mid s m x) (hpc : x.pc = 0x800104a0)
    (hrow : eListAt x (s.getReg .x2 - 1688) 64 =
      openRow (sgOf s) (slOf s m) (claimAt s (oClaim s)).weights (s.getReg .x15).toNat
        (s.getReg .x16).toNat) : AtFinal s m x :=
  ⟨hpc, M.x2, M.saved, M.out, M.cap, M.ptr, M.len, M.value, hrow, M.heap, M.mono, M.frame⟩

theorem dispatch {s m z : MachineState} (hpre : OpenPre s) (P : P2 s m) (Z : ZD s m z) :
    ∃ x, Reaches Image.code z x ∧ (AtFinal s m x ∨ OI s m x 0) := by
  have hb := bounds hpre
  have hc := hpre.claim
  have x2z := Z.mid.x2
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80010374_spec Z.pc (by
    rv_eval [x2z]; valid_access hpre.stack.valid [hb])
  have hm₁ := b80010374_mem_same h₁
  have k₁ := b80010374_keeps h₁
  have x2₁ : z₁.getReg .x2 = s.getReg .x2 - 1856 := (k₁ .x2 (by decide)).trans x2z
  have M₁ := Z.mid.keep hpre (DFrame.of_same hm₁ _) x2₁
  have hcnt : z.getMem (z.getReg .x2 + 72) = s.getReg .x16 := by
    rw [x2z]; rv_eval []; exact Z.mid.count
  have row₁ : eListAt z₁ (s.getReg .x2 - 1688) 64 = List.replicate 64 0 := by
    rw [← Z.row]; simp only [eListAt, eAt, hm₁]
  by_cases hc0 : s.getReg .x16 = 0
  · refine ⟨z₁, hr₁, Or.inl (atFinal_of_mid M₁ (b80010374_pc_taken h₁ (by rw [hcnt]; exact hc0)) ?_)⟩
    rw [row₁, hc0]; rfl
  have ck := (claim_keep hpre P M₁).1
  have x21₁ : z₁.getReg .x21 = s.getReg .x14 := (k₁ .x21 (by decide)).trans Z.x21
  obtain ⟨z₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8001037c_spec
    (b80010374_pc_not_taken h₁ (by rw [hcnt]; exact hc0)) (by
      rv_eval [x2₁, x21₁]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc]))
  have k₂ := b8001037c_keeps h₂
  have f₂ := b8001037c_frame h₂ (by rw [x2₁]; addr_omega [hb])
  rw [x2₁] at f₂
  have x2₂ : z₂.getReg .x2 = s.getReg .x2 - 1856 := (k₂ .x2 (by decide)).trans x2₁
  have M₂ := M₁.keep hpre ((DFrame.of_memFrame f₂).mono fun a ha ↦ by addr_omega [ha, hb]) x2₂
  have hw : z₁.getMem (s.getReg .x14 + 64) = s.getMem (s.getReg .x14 + 64) :=
    ck _ (by addr_omega [hc]) (by addr_omega [hc])
  have row₂ : eListAt z₂ (s.getReg .x2 - 1688) 64 = List.replicate 64 0 := by
    rw [← row₁]
    exact (DFrame.of_memFrame f₂).eListAt fun i hi h ↦ by addr_omega [h, hi, hb]
  by_cases hw0 : s.getMem (s.getReg .x14 + 64) = 0
  · refine ⟨z₂, hr₁.trans hr₂,
      Or.inl (atFinal_of_mid M₂ (b8001037c_pc_taken h₂ (by rw [x21₁, hw]; exact hw0)) ?_)⟩
    rw [row₂, ← (claim_keep hpre P M₂).2, hw0]
    exact (openRow_nil _ _ _ _).symm
  obtain ⟨q, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80010388_spec
    (b8001037c_pc_not_taken h₂ (by rw [x21₁, hw]; exact hw0)) (by
      rv_eval [x2₂, (k₂ .x21 (by decide)).trans x21₁]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc]))
  have k₃ := b80010388_keeps h₃
  have f₃ := b80010388_frame h₃ (by rw [x2₂]; addr_omega [hb])
  rw [x2₂] at f₃
  have x2q : q.getReg .x2 = s.getReg .x2 - 1856 := (k₃ .x2 (by decide)).trans x2₂
  have Mq := M₂.keep hpre ((DFrame.of_memFrame f₃).mono fun a ha ↦ by addr_omega [ha, hb]) x2q
  have kq (y : Word) (h1 : (s.getReg .x2).toNat - 1856 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h3 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1816 ∨ (s.getReg .x2).toNat - 1800 ≤ y.toNat) :
      q.getMem y = z₂.getMem y := f₃ y (by addr_omega [h1, h2, h3, hb])
  have kz (y : Word) (h1 : (s.getReg .x2).toNat - 1856 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h3 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1800 ∨ (s.getReg .x2).toNat - 1792 ≤ y.toNat) :
      z₂.getMem y = z₁.getMem y := f₂ y (by addr_omega [h1, h2, h3, hb])
  have ck2 := (claim_keep hpre P M₂).1
  refine ⟨q, hr₁.trans (hr₂.trans hr₃), Or.inr {
    mid := Mq
    x18 := by rw [b80010388_x18 h₃, x2₂]; rv_eval []
    x19 := by
      rw [b80010388_x19 h₃, x2₂, kq _ (by addr_omega [hb]) (by addr_omega [hb])
        (Or.inr (by addr_omega [hb]))]; rv_eval []
    x20 := by
      rw [b80010388_x20 h₃, x2₂, kq _ (by addr_omega [hb]) (by addr_omega [hb])
        (Or.inr (by addr_omega [hb]))]; rv_eval []
    x23 := by
      rw [b80010388_x23 h₃, x2₂, kq _ (by addr_omega [hb]) (by addr_omega [hb])
        (Or.inr (by addr_omega [hb]))]; rv_eval []
    sgp := by
      have := b80010388_m_x2_40 h₃
      rw [x2₂] at this; rv_eval [] at this
      rw [this, kq _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inr (by addr_omega [hb]))]
    wp := by
      have := b80010388_m_x2_48 h₃
      rw [x2₂, (k₂ .x21 (by decide)).trans x21₁] at this; rv_eval [] at this
      rw [this, ck2 _ (by addr_omega [hc]) (by addr_omega [hc])]
    wl := by
      have := b8001037c_m_x2_56 h₂
      rw [x2₁, x21₁, hw] at this; rv_eval [] at this
      rw [kq _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inr (by addr_omega [hb])), this]
    pc := b80010388_pc h₃
    x26 := b80010388_x26 h₃
    lt := by
      have : (s.getReg .x16).toNat ≠ 0 := fun h ↦ hc0 (BitVec.eq_of_toNat_eq h)
      omega
    wne := fun h ↦ hw0 (BitVec.eq_of_toNat_eq h)
    row := by
      rw [show outRow (sgOf s) (slOf s m) (claimAt s (oClaim s)).weights (s.getReg .x15).toNat 0 =
        List.replicate 64 0 from rfl, ← row₂]
      exact (DFrame.of_memFrame f₃).eListAt fun i hi h ↦ by addr_omega [h, hi, hb] }⟩

end Rv64Verifier.Gkr.Open
