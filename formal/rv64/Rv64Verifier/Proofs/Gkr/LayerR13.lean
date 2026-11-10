import Rv64Verifier.Proofs.Gkr.LayerR14
import Rv64Verifier.Proofs.Multilinear.Contracts

/-!
# `keccak::verify_layer`: the next value, `g`

`keccak.rs:196` at `0x8000fd7c..0x8000fe14`: `t`'s length checked, `t[0] + beta * (t[1] + beta *
t[2])` into `s3`, `s4`, `s5`; then `linear_transpose`'s `g = vec![ZERO; 1600]` at `f + 1560`
(`from_elem`) and its loop (`LayerR14.lean`), to `0x8000fed8` (`J15`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-! ## What `SW2` misses -/

theorem sw2_slot {s : MachineState} (hpre : VerifyLayerPre s) {H N : Nat} (hN : N ≤ heapEnd)
    {y : Word} (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
    (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 752 ∨
      (s.getReg .x2).toNat - 728 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 152 ∨
      (s.getReg .x2).toNat - 104 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
    ∀ i < 8, ¬ SW2 s H N (y + BitVec.ofNat 64 i) := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  simp only [stackLo] at hnx hab
  unfold verifyLayerStack at hb hnx hab
  intro i hi hw
  simp only [SW2] at hw
  rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hi, h1, h2, hb, hnx, hab, hN]

theorem sw2_buf {s : MachineState} (hpre : VerifyLayerPre s) {H N : Nat} (hH : H ≤ heapEnd)
    {p : Word} {n : Nat} (hp : p.toNat + n ≤ H) : ∀ i < n, ¬ SW2 s H N (p + BitVec.ofNat 64 i) := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  simp only [stackLo] at hnx hab
  unfold verifyLayerStack at hb hnx hab
  intro i hi hw
  simp only [SW2] at hw
  rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hi, hp, hb, hnx, hab, hH]

/-- After `g`, at `0x8000fed8`: the next value in `s3`, `s4`, `s5`, `g` in `s7` (length in `s6`). -/
structure J15 (s u v : MachineState) (eqZ eqLane t : List E) (beta : E) : Prop where
  pc : v.pc = 0x8000fed8
  base : Base s v
  mono : heapNext u ≤ heapNext v
  frame : DFrame u v (SW2 s (heapNext u) (heapNext v))
  x22 : v.getReg .x22 = 1600
  gbuf : heapNext u ≤ (v.getReg .x23).toNat ∧ (v.getReg .x23).toNat + 38400 ≤ heapNext v ∧
    (v.getReg .x23).toNat % 8 = 0
  gE : ∀ p < 1600, eAt v (v.getReg .x23 + BitVec.ofNat 64 (24 * p)) =
    gOf (nextWeightsRust eqZ eqLane beta) p
  val : (v.getReg .x19, v.getReg .x20, v.getReg .x21) =
    limbs (t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0))
  x26 : v.getReg .x26 = u.getReg .x26
  x27 : v.getReg .x27 = 0x3333333333333334

theorem zero_vmr : ValidMemRange (0xa0000068 : Word) 3 := by
  intro i hi
  interval_cases i <;> decide

theorem value_eq (t0 t1 t2 beta : E) : beta * (beta * t2 + t1) + t0 = t0 + beta * (t1 + beta * t2) := by
  ring

set_option maxHeartbeats 32000000 in
theorem value_g (hM : MulSpec) (hFE : MultilinearContracts.FromElemSpec) {s u w : MachineState}
    {mu point eqZ eqLane t : List E} {beta : E} (hpre : VerifyLayerPre s)
    (J : J12 s u mu point eqZ eqLane t beta) (K : J13 s u w eqZ eqLane beta) :
    ∃ v, Reaches Image.code w v ∧ (J15 s u v eqZ eqLane t beta ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := K.base
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  simp only [stackLo] at hnx hab hrs
  unfold verifyLayerStack at hb hnx hab hrs
  have hHw := B.heap.hi
  have hHu := J.base.heap.hi
  have hsu := J.base.mono
  have hH0 := hpre.heap.lo
  have hwb := K.wbuf
  have hkm := K.mono
  have slot (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 752 ∨
        (s.getReg .x2).toNat - 728 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 152 ∨
        (s.getReg .x2).toNat - 104 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      w.getMem y = u.getMem y := K.frame y (sw2_slot hpre hHw h1 h2)
  -- `t`'s buffer
  obtain ⟨tp, htp⟩ : ∃ tp, u.getMem (s.getReg .x2 - 1656) = tp := ⟨_, rfl⟩
  obtain ⟨tn, htn⟩ : ∃ tn, u.getMem (s.getReg .x2 - 1688) = tn := ⟨_, rfl⟩
  have tB := J.tBuf
  have tE := J.tE
  have t2 := J.t2
  rw [htp, htn] at tB tE
  rw [htp] at t2
  simp only [NewBuf] at tB
  have w24 : w.getMem (s.getReg .x2 - 1688) = tn := by
    rw [slot _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), htn]
  have w56 : w.getMem (s.getReg .x2 - 1656) = tp := by
    rw [slot _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), htp]
  have w32 : w.getMem (s.getReg .x2 - 1680) = tp + 48 := by
    rw [slot _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), t2]
  -- `0x8000fd7c..0x8000fd94`: `t.len() > 2`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000fd7c_spec K.pc (by
    rv_eval [B.x2]; valid_access hpre.stack.valid [hb])
  have e24 : w.getMem (w.getReg .x2 + 24) = tn := by rw [B.x2]; rv_eval [w24]
  by_cases h0 : tn = 0
  · exact ⟨t₁, hr₁, Or.inr (dead_of_fetch (by rw [b8000fd7c_pc_taken h₁ (by rw [e24, h0])]; exact trap))⟩
  have x11₁ : t₁.getReg .x11 = tn := by rw [b8000fd7c_x11 h₁, e24]
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000fd84_spec (b8000fd7c_pc_not_taken h₁ (by rw [e24]; exact h0)) trivial
  by_cases h1 : tn = 1
  · exact ⟨t₂, hr₁.trans hr₂, Or.inr (dead_of_fetch (by rw [b8000fd84_pc_taken h₂ (by rw [x11₁, h1])]; exact trap))⟩
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000fd8c_spec (b8000fd84_pc_not_taken h₂ (by rw [x11₁]; exact h1)) trivial
  have x11₂ : t₂.getReg .x11 = tn := by rw [b8000fd84_keeps h₂ .x11 (by decide), x11₁]
  have h01 : tn.toNat ≠ 0 ∧ tn.toNat ≠ 1 := ⟨fun h ↦ h0 (BitVec.eq_of_toNat_eq (by simp [h])),
    fun h ↦ h1 (BitVec.eq_of_toNat_eq (by simp [h]))⟩
  by_cases h2 : tn.toNat ≤ 2
  · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr (dead_of_fetch (by
      rw [b8000fd8c_pc_taken h₃ (by rw [x11₂]; exact h2)]; exact trap))⟩
  have pc₃ := b8000fd8c_pc_not_taken h₃ (by rw [x11₂]; show 2 < tn.toNat; omega)
  have hm13 (a : Word) : t₃.getMem a = w.getMem a := by
    rw [b8000fd8c_mem_same h₃, b8000fd84_mem_same h₂, b8000fd7c_mem_same h₁]
  have r13 (r : Reg) (hr : r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26,
      .x27]) : t₃.getReg r = w.getReg r := by
    rw [b8000fd8c_keeps h₃ r (mem_of_mem hr _), b8000fd84_keeps h₂ r (mem_of_mem hr _),
      b8000fd7c_keeps h₁ r (mem_of_mem hr _)]
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := by rw [r13 .x2 (by decide), B.x2]
  have hTb : heapStart ≤ tp.toNat ∧ tp.toNat + 24 * tn.toNat ≤ heapNext u := by
    rcases tB.2 with h | h
    · omega
    · exact ⟨by simp only [heapStart] at hH0 ⊢; omega, h.2⟩
  have hTV : ValidMemRange tp (3 * tn.toNat) := heap_vmr hTb.1 (by omega) tB.1
  -- `t`'s limbs at `w`
  have tw (i : Nat) (hi : i < tn.toNat) : eAt w (tp + BitVec.ofNat 64 (24 * i)) = t.getD i 0 := by
    rw [← tE, getD_eListAt _ _ hi]
    exact K.frame.eAt fun k hk ↦ by
      rw [add_ofNat_add]; exact sw2_buf hpre hHu (n := 24 * tn.toNat) hTb.2 _ (by omega)
  -- `0x8000fd94`: `t[0]`, `t[1]` loaded, `beta * t[2]`
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000fd94_spec pc₃ (by
    rv_eval [x2₃, hm13, w56, w32]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | valid_access hTV [hTb, h2, tB])
  have k₄ := b8000fd94_keeps h₄
  have hm₄ := b8000fd94_mem_same h₄
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1712 := by rw [k₄ .x2 (by decide), x2₃]
  have x10₄ : t₄.getReg .x10 = s.getReg .x2 - 752 := by rw [b8000fd94_x10 h₄, x2₃]; rv_eval []
  have x11₄ : t₄.getReg .x11 = s.getReg .x2 - 776 := by rw [b8000fd94_x11 h₄, x2₃]; rv_eval []
  have x12₄ : t₄.getReg .x12 = tp + 48 := by rw [b8000fd94_x12 h₄, x2₃]; rv_eval [hm13, w32]
  have B₄ : Base s t₄ := B.same x2₄ fun a ↦ by rw [hm₄, hm13]
  have hmp : MulPre t₄ := mul_pre hpre x2₄ (B₄.rodata hpre) 752 x10₄ (by decide) (by decide)
    (by decide)
    (by rw [x11₄]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x11₄]; addr_omega [hb])
    (by rw [x10₄, x11₄]; addr_omega [hb])
    (by rw [x12₄]; valid_sub hTV [hTb, h2, tB])
    (by rw [x12₄]; addr_omega [hb, hab, hTb, h2, hHu])
    (by rw [x10₄, x12₄]; addr_omega [hb, hab, hTb, h2, hHu])
  obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hd⟩ :=
    hM.call (hr₁.trans (hr₂.trans (hr₃.trans hr₄))) (b8000fd94_pc h₄) hmp
  swap
  · exact ⟨_, hr₅, Or.inr hd⟩
  have G₅ := mul_frame x2₄ hpost₅
  rw [x10₄] at G₅
  have v₅ := hpost₅.value
  have hbeta : eAt t₄ (s.getReg .x2 - 776) = beta := by
    unfold Rv64Verifier.eAt; rw [hm₄, hm₄, hm₄, hm13, hm13, hm13]
    rw [← J.bt]; unfold Rv64Verifier.eAt
    rw [slot _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])),
      slot _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])),
      slot _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))]
  have ht2 : eAt t₄ (tp + 48) = t.getD 2 0 := by
    rw [← tw 2 (by omega)]
    unfold Rv64Verifier.eAt; rw [hm₄, hm₄, hm₄, hm13, hm13, hm13]; rfl
  rw [x10₄, x11₄, x12₄, hbeta, ht2] at v₅
  have x2₅ : t₅.getReg .x2 = s.getReg .x2 - 1712 := (hpres₅.reg .x2).trans x2₄
  have hN₅ : t₅.getMem nextAddr = t₄.getMem nextAddr := G₅ _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hi, hw, hb, hnx]
  have B₅ : Base s t₅ := B₄.next hpre x2₅
    ⟨by simp only [heapNext, hN₅]; exact B₄.heap.lo, by simp only [heapNext, hN₅]; exact B₄.heap.hi⟩
    (by simp only [heapNext, hN₅]; exact le_refl _) G₅ fun a h ↦ by
      refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> rcases h with h | h <;> addr_omega [h, hb]
  have c5 (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27]) :
      t₅.getReg r = t₄.getReg r :=
    hpres₅.reg r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  -- `0x8000fdc4`: `beta * t[2] + t[1]` into `f + 1584`, `beta` times it
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000fdc4_spec
    (by rw [hpc₅, returnAddress_eq, b8000fd94_x1 h₄]; decide) (by
      rv_eval [x2₅]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₆ := b8000fdc4_keeps h₆
  have f₆ := b8000fdc4_frame h₆ (by rw [x2₅]; addr_omega [hb])
  rw [x2₅] at f₆
  rv_eval [] at f₆
  have x2₆ : t₆.getReg .x2 = s.getReg .x2 - 1712 := (k₆ .x2 (by decide)).trans x2₅
  have B₆ : Base s t₆ := B₅.slots hpre x2₆ f₆ (by addr_omega [hb]) (by addr_omega [hb])
  have lt1 : limbs (t.getD 1 0) = (w.getMem (tp + 24), w.getMem (tp + 32), w.getMem (tp + 40)) := by
    rw [← tw 1 (by omega), limbs_eAt, show BitVec.ofNat 64 (24 * 1) = (24 : Word) from rfl]; rv_eval []
  have lt0 : limbs (t.getD 0 0) = (w.getMem tp, w.getMem (tp + 8), w.getMem (tp + 16)) := by
    rw [← tw 0 (by omega), limbs_eAt, Nat.mul_zero, add_ofNat_zero]
  have tmp : eAt t₆ (s.getReg .x2 - 128) = beta * t.getD 2 0 + t.getD 1 0 := by
    apply eAt_eq_of_limbs
    rw [limbs_add, ← v₅, lt1, limbs_eAt]
    have n0 := b8000fdc4_m_x2_1584 h₆
    have n8 := b8000fdc4_m_x2_1592 h₆
    have n16 := b8000fdc4_m_x2_1600 h₆
    rw [x2₅, c5 .x19 (by decide), b8000fd94_x19 h₄, x2₃] at n0
    rw [x2₅, c5 .x20 (by decide), b8000fd94_x20 h₄, x2₃] at n8
    rw [x2₅, c5 .x22 (by decide), b8000fd94_x22 h₄, x2₃] at n16
    rv_eval [hm13, w56] at n0 n8 n16
    rv_eval [n0, n8, n16]
  have x10₆ : t₆.getReg .x10 = s.getReg .x2 - 752 := by rw [b8000fdc4_x10 h₆, x2₅]; rv_eval []
  have x11₆ : t₆.getReg .x11 = s.getReg .x2 - 776 := by rw [b8000fdc4_x11 h₆, x2₅]; rv_eval []
  have x12₆ : t₆.getReg .x12 = s.getReg .x2 - 128 := by rw [b8000fdc4_x12 h₆, x2₅]; rv_eval []
  have hmp₆ : MulPre t₆ := mul_pre hpre x2₆ (B₆.rodata hpre) 752 x10₆ (by decide) (by decide)
    (by decide)
    (by rw [x11₆]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x11₆]; addr_omega [hb])
    (by rw [x10₆, x11₆]; addr_omega [hb])
    (by rw [x12₆]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x12₆]; addr_omega [hb])
    (by rw [x10₆, x12₆]; addr_omega [hb])
  obtain ⟨t₇, hr₇, ⟨hpc₇, hpres₇, hpost₇⟩ | hd⟩ := hM.call hr₆ (b8000fdc4_pc h₆) hmp₆
  swap
  · exact ⟨_, hr₅.trans hr₇, Or.inr hd⟩
  have G₇ := mul_frame x2₆ hpost₇
  rw [x10₆] at G₇
  have v₇ := hpost₇.value
  have hbeta₆ : eAt t₆ (s.getReg .x2 - 776) = beta := by
    rw [f₆.eAt (by addr_omega [hb]) (by addr_omega [hb]),
      G₅.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb], hbeta]
  rw [x10₆, x11₆, x12₆, hbeta₆, tmp] at v₇
  have x2₇ : t₇.getReg .x2 = s.getReg .x2 - 1712 := (hpres₇.reg .x2).trans x2₆
  have hN₇ : t₇.getMem nextAddr = t₆.getMem nextAddr := G₇ _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hi, hw, hb, hnx]
  have B₇ : Base s t₇ := B₆.next hpre x2₇
    ⟨by simp only [heapNext, hN₇]; exact B₆.heap.lo, by simp only [heapNext, hN₇]; exact B₆.heap.hi⟩
    (by simp only [heapNext, hN₇]; exact le_refl _) G₇ fun a h ↦ by
      refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> rcases h with h | h <;> addr_omega [h, hb]
  have c7 (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x21, .x23, .x25, .x26, .x27]) :
      t₇.getReg r = t₄.getReg r := by
    rw [hpres₇.reg r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k₆ r (mem_of_mem hr _), c5 r (mem_of_mem hr _)]
  -- `0x8000fdfc`: the value, `from_elem(f + 1560, ZERO, 1600)`
  obtain ⟨t₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b8000fdfc_spec
    (by rw [hpc₇, returnAddress_eq, b8000fdc4_x1 h₆]; decide) (by
      rv_eval [x2₇]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₈ := b8000fdfc_keeps h₈
  have hm₈ := b8000fdfc_mem_same h₈
  have x2₈ : t₈.getReg .x2 = s.getReg .x2 - 1712 := (k₈ .x2 (by decide)).trans x2₇
  have B₈ : Base s t₈ := B₇.same x2₈ hm₈
  have val₈ : (t₈.getReg .x19, t₈.getReg .x20, t₈.getReg .x21) =
      limbs (t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0)) := by
    rw [← value_eq, limbs_add, ← v₇, lt0, limbs_eAt, b8000fdfc_x19 h₈, b8000fdfc_x20 h₈,
      b8000fdfc_x21 h₈, c7 .x9 (by decide), c7 .x18 (by decide), c7 .x21 (by decide),
      b8000fd94_x9 h₄, b8000fd94_x18 h₄, b8000fd94_x21 h₄, x2₇, x2₃]
    rv_eval [hm13, w56]
  have x10₈ : t₈.getReg .x10 = s.getReg .x2 - 152 := by rw [b8000fdfc_x10 h₈, x2₇]; rv_eval []
  have x11₈ : t₈.getReg .x11 = 0xa0000068 := b8000fdfc_x11 h₈
  have x12₈ : t₈.getReg .x12 = 1600 := b8000fdfc_x12 h₈
  have hfe : MultilinearContracts.FromElemPre t₈ := {
    heap := B₈.heap
    out := by rw [x10₈]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    elem := by rw [x11₈]; exact zero_vmr
    stack := hpre.stack.sub 1712 x2₈ (by unfold verifyLayerStack MultilinearContracts.fromElemStack tryAllocStack; decide)
      (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [x10₈]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    outStack := by
      rw [x10₈]; simp only [stackLo, x2₈, MultilinearContracts.fromElemStack, tryAllocStack]
      addr_omega [hb]
    elemFree := by rw [x11₈]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega []
    elemStack := by
      rw [x11₈]; simp only [stackLo, x2₈, MultilinearContracts.fromElemStack, tryAllocStack]
      addr_omega [hb, hrs]
    elemOut := by rw [x11₈, x10₈]; addr_omega [hb, hrs] }
  obtain ⟨t₉, hr₉, ⟨hpc₉, hpres₉, FE⟩ | hd⟩ := hFE.call hr₈ (b8000fdfc_pc h₈) hfe
  swap
  · exact ⟨_, hr₅.trans (hr₇.trans hr₉), Or.inr hd⟩
  have x2₉ : t₉.getReg .x2 = s.getReg .x2 - 1712 := (hpres₉.reg .x2).trans x2₈
  have fev := FE.vec.raw
  have fel := FE.len
  have fef := FE.fresh
  simp only [x10₈, x12₈, RawVecOk, Buf, vecPtr, vecCap, vecLen, NewBuf] at fev fel fef
  rv_eval [] at fev
  rv_eval [] at fel
  rv_eval [] at fef
  have hN₈ : heapNext t₈ = heapNext w := by
    have : t₈.getMem nextAddr = w.getMem nextAddr := by
      rw [hm₈, hN₇, f₆ _ (by addr_omega [hb, hnx]), hN₅, hm₄, hm13]
    simp only [heapNext, this]
  have B₉ : Base s t₉ := B₈.next hpre x2₉ FE.heap FE.mono (DFrame.of_byteFrame FE.frame)
    fun a ha ↦ cframe_lw hpre B₈ 152 (by decide) (by decide)
      (by unfold MultilinearContracts.fromElemStack tryAllocStack sumcheckStack; decide) FE.heap x10₈ a ha
  have hH9 := FE.heap.hi
  have hm9 := FE.mono
  obtain ⟨G, hGd⟩ : ∃ G, t₉.getMem (s.getReg .x2 - 144) = G := ⟨_, rfl⟩
  rw [hGd] at fev fef
  have hG : heapNext w ≤ G.toNat ∧ G.toNat + 38400 ≤ heapNext t₉ := by
    rcases fef.2 with h | h
    · omega
    · rw [hN₈] at h; exact h
  -- the frame since `w`
  have F₈ : DFrame w t₈ (SW2 s (heapNext w) (heapNext t₉)) :=
    ((((((DFrame.of_same hm13 _).trans (DFrame.of_same hm₄ _) fun _ h ↦ h).trans G₅ fun a h ↦ by
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h).trans (DFrame.of_memFrame f₆) fun a h ↦
        Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))).trans G₇ fun a h ↦ by
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h).trans (DFrame.of_same hm₈ _) fun _ h ↦ h)
  have F₉ : DFrame w t₉ (SW2 s (heapNext w) (heapNext t₉)) :=
    F₈.trans (DFrame.of_byteFrame FE.frame) fun a h ↦ by
      simp only [Fresh, stackLo, x10₈, x2₈, MultilinearContracts.fromElemStack, tryAllocStack] at h
      rcases h with h | h | h | h
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
      · exact Or.inl (by addr_omega [h, hb])
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [← hN₈]; exact h.1, h.2⟩)))
  -- `0x8000fe2c`: the loop's registers
  obtain ⟨w₀, hr₁₀, h₁₀⟩ := Sym.BlockSpec.reaches b8000fe2c_spec
    (by rw [hpc₉, returnAddress_eq, b8000fdfc_x1 h₈]; decide) (by
      rv_eval [x2₉]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁₀ := b8000fe2c_keeps h₁₀
  have hm₁₀ := b8000fe2c_mem_same h₁₀
  have x2₁₀ : w₀.getReg .x2 = s.getReg .x2 - 1712 := (k₁₀ .x2 (by decide)).trans x2₉
  have B₁₀ : Base s w₀ := B₉.same x2₁₀ hm₁₀
  have hN₁₀ : heapNext w₀ = heapNext t₉ := by simp only [heapNext, hm₁₀]
  have F₁₀ : DFrame w w₀ (SW2 s (heapNext w) (heapNext w₀)) := by
    rw [hN₁₀]; exact F₉.trans (DFrame.of_same hm₁₀ _) fun _ h ↦ h
  have reg (r : Reg) (hr : r ∈ [Reg.x8, .x25, .x26, .x27]) : w₀.getReg r = w.getReg r := by
    rw [k₁₀ r (mem_of_mem hr _), hpres₉.reg r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      k₈ r (mem_of_mem hr _), c7 r (mem_of_mem hr _), k₄ r (mem_of_mem hr _), r13 r (mem_of_mem hr _)]
  have C : TC w₀ G (w.getReg .x25) (nw eqZ eqLane beta) := {
    ro := B₁₀.rodata hpre
    x8 := by rw [reg .x8 (by decide), K.x8]
    x11 := b8000fe2c_x11 h₁₀
    x12 := b8000fe2c_x12 h₁₀
    x13 := b8000fe2c_x13 h₁₀
    x22 := by rw [b8000fe2c_x22 h₁₀, x2₉]; rv_eval [fel]
    x25 := reg .x25 (by decide)
    w := fun i hi ↦ by
      rw [F₁₀.eAt fun k hk ↦ by
        rw [add_ofNat_add]; exact sw2_buf hpre hHw (n := 38400) hwb.2.1 _ (by omega)]
      exact K.wE i hi
    gp := ⟨fev.1, by simp only [heapStart] at hH0 ⊢; omega, by omega⟩
    pp := ⟨hwb.2.2, by simp only [heapStart] at hH0 ⊢; omega, by omega⟩ }
  have O₀ : TO w₀ w₀ G (nw eqZ eqLane beta) 0 := {
    regs := fun _ _ ↦ rfl
    x10 := b8000fe2c_x10 h₁₀
    x14 := by rw [b8000fe2c_x14 h₁₀, x2₉, Nat.mul_zero, add_ofNat_zero]; rv_eval [hGd]
    x15 := b8000fe2c_x15 h₁₀
    frame := DFrame.refl _ _
    g := fun p hp ↦ absurd hp (Nat.not_lt_zero p)
    lt := by decide }
  obtain ⟨v, hr₁₁, ⟨X, hpc₁₁⟩ | hd⟩ := lane_loop' C 25 0 w₀ rfl O₀ (b8000fe2c_pc h₁₀)
  swap
  · exact ⟨v, hr₅.trans (hr₇.trans (hr₉.trans (hr₁₀.trans hr₁₁))), Or.inr hd⟩
  have hNv : v.getMem nextAddr = w₀.getMem nextAddr := X.frame _ fun i hi hw ↦ by
    addr_omega [hw, hi, hG, hH9]
  have hNv' : heapNext v = heapNext w₀ := by simp only [heapNext, hNv]
  have Bv : Base s v := B₁₀.next hpre ((X.regs .x2 (by decide)).trans x2₁₀)
    ⟨by rw [hNv']; exact B₁₀.heap.lo, by rw [hNv']; exact B₁₀.heap.hi⟩ (le_of_eq hNv'.symm)
    X.frame fun a h ↦ ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [h, hG, hsu, hkm],
      by rw [hNv', hN₁₀]; addr_omega [h, hG]⟩))), by addr_omega [h, hb, hG, hH9, hab]⟩
  have x23v : v.getReg .x23 = G := by
    rw [X.regs .x23 (by decide), b8000fe2c_x23 h₁₀, x2₉]; rv_eval [hGd]
  have r19 (r : Reg) (hr : r ∈ [Reg.x19, .x20, .x21]) : v.getReg r = t₈.getReg r := by
    rw [X.regs r (mem_of_mem hr _), k₁₀ r (mem_of_mem hr _),
      hpres₉.reg r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)]
  refine ⟨v, hr₅.trans (hr₇.trans (hr₉.trans (hr₁₀.trans hr₁₁))), Or.inl {
    pc := hpc₁₁
    base := Bv
    mono := by rw [hNv', hN₁₀]; omega
    frame := (K.frame.mono fun a h ↦ sw2_mono (by rw [hNv', hN₁₀]; omega) h).trans
      (F₁₀.trans X.frame fun a h ↦ Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [h, hG],
        by rw [hN₁₀]; addr_omega [h, hG]⟩)))) fun a h ↦ by
      simp only [SW2] at h ⊢
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by rw [hNv']; exact h.2⟩)))
    x22 := by rw [X.regs .x22 (by decide), C.x22]
    gbuf := by rw [x23v, hNv', hN₁₀]; exact ⟨by omega, hG.2, fev.1⟩
    gE := fun p hp ↦ by
      rw [x23v, X.g p hp, show gOf (nextWeightsRust eqZ eqLane beta) p =
        (nextWeightsRust eqZ eqLane beta).getD (src (p / 64) (p % 64)) 0 from rfl,
        nextWeights_getD _ _ _ (src_lt (by omega))]
    val := by rw [r19 .x19 (by decide), r19 .x20 (by decide), r19 .x21 (by decide), val₈]
    x26 := by rw [X.regs .x26 (by decide), reg .x26 (by decide), K.x26]
    x27 := by rw [X.regs .x27 (by decide), reg .x27 (by decide), K.x27] }⟩

end Rv64Verifier.Gkr.Layer
