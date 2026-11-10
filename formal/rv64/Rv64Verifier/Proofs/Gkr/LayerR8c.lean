import Rv64Verifier.Proofs.Gkr.LayerR8b

/-!
# `keccak::verify_layer`: a pack round's push, the pack loop

`0x8000f6d0..0x8000f5ec`: `scale` stored, the `Vec` of challenges grown by `grow_one` when full
(`pk_store`), the challenge pushed and the loop's exit test (`pk_push`); the loop (`pack_loop`) and
`J7` to `J8` (`pack`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript
  Rv64Verifier.Contracts Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- What a round writes before the push: `W8`, `scale`, the push slot and the `Vec`'s capacity
and pointer. -/
@[rv_addr] def W8e (s w v : MachineState) (a : Word) : Prop :=
  W8 s w v a ∨ Within a (s.getReg .x2 - 1472) 24 ∨ Within a (s.getReg .x2 - 1600) 8 ∨
    Within a (s.getReg .x2 - 848) 16

/-- Room for the challenge, at `0x8000f5bc`. -/
structure Q3 (s w t : MachineState) (ip : Word) (c : E) (k : Nat) (acc : E × E × List E)
    (ch nv : E) : Prop where
  pc : t.pc = 0x8000f5bc
  base : Base s t
  mono : heapNext w ≤ heapNext t
  frame : DFrame w t (W8e s w t)
  x19 : t.getReg .x19 = s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k)
  regs : ∀ r ∈ [Reg.x9, .x23, .x26], t.getReg r = w.getReg r
  chL : limbs ch = (t.getReg .x18, t.getReg .x25, t.getReg .x20)
  value : eAt t (s.getReg .x2 - 1592) = nv
  scale : eAt t (s.getReg .x2 - 1472) = acc.2.1 * (1 + rOf s k + ch)
  push : t.getMem (s.getReg .x2 - 1600) = t.getMem (s.getReg .x2 - 840)
  ptCap : k < (t.getMem (s.getReg .x2 - 848)).toNat
  ptBuf : (t.getMem (s.getReg .x2 - 840)).toNat % 8 = 0 ∧
    ip.toNat + 24 * (w.getMem (s.getReg .x2 - 1672)).toNat ≤ (t.getMem (s.getReg .x2 - 840)).toNat ∧
    (t.getMem (s.getReg .x2 - 840)).toNat + (t.getMem (s.getReg .x2 - 848)).toNat * 24 ≤ heapNext t
  ptE : eListAt t (t.getMem (s.getReg .x2 - 840)) k = acc.2.2
  rest : Rest s t (packR s c (k + 1) (nv, acc.2.1 * (1 + rOf s k + ch), acc.2.2 ++ [ch]))

theorem w8e_mono {s w v v' : MachineState} (h : heapNext v ≤ heapNext v') {a : Word}
    (ha : W8e s w v a) : W8e s w v' a := by
  simp only [W8e] at ha ⊢
  rcases ha with ha | ha
  · exact Or.inl (w8_mono h ha)
  · exact Or.inr ha

set_option maxHeartbeats 16000000 in
/-- `0x8000f6d0`: `scale` stored; a full `Vec` grown (`0x8000f6f0`, `0x8000f6fc`). -/
theorem pk_store (hG : GrowOneFreshSpec 0x80011c78 24 8) {s w t : MachineState} {ip : Word}
    {c : E} {k : Nat} {acc : E × E × List E} {ch nv : E} (hpre : VerifyLayerPre s)
    (P : PK s w ip c k acc) (Q : Q2 s w t c k acc ch nv) :
    ∃ v, Reaches Image.code t v ∧ (Q3 s w v ip c k acc ch nv ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := Q.base
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  simp only [stackLo] at hnx hab hss
  unfold verifyLayerStack at hb hnx hab hss
  have hHt := B.heap.hi
  have hsw := P.base.mono
  have hHs := hpre.heap.lo
  have hwt := Q.mono
  have pb := P.ptBuf
  have pc := P.ptCap
  have ib := P.ibuf
  have kq (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1592 ∨
        (s.getReg .x2).toNat - 1568 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 1448 ∨
        (s.getReg .x2).toNat - 1424 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 752 ∨
        (s.getReg .x2).toNat - 720 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 128) :
      t.getMem y = w.getMem y :=
    Q.frame y fun i hi hw ↦ by
      simp only [W8, Fresh] at hw
      rcases hw with hw | hw | hw | hw | hw | hw | hw | hw <;>
        addr_omega [hw, hi, h1, h2, hb, hss, hS, hnx, hab, hHt]
  have cap₀ : t.getMem (s.getReg .x2 - 848) = w.getMem (s.getReg .x2 - 848) :=
    kq _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)))
  have ptr₀ : t.getMem (s.getReg .x2 - 840) = w.getMem (s.getReg .x2 - 840) :=
    kq _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)))
  have push₀ : t.getMem (s.getReg .x2 - 1600) = w.getMem (s.getReg .x2 - 1600) :=
    kq _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))
  have icap₀ : t.getMem (s.getReg .x2 - 1672) = w.getMem (s.getReg .x2 - 1672) :=
    kq _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))
  -- the challenges so far, kept from `w`
  have ptE₀ : eListAt t (w.getMem (s.getReg .x2 - 840)) k = acc.2.2 := by
    rw [← P.ptE]
    exact Q.frame.eListAt fun j hj hw ↦ by
      simp only [W8, Fresh] at hw
      rcases hsf.1 with hs1 | hs1 <;>
      rcases hw with hw | hw | hw | hw | hw | hw | hw | hw <;>
        addr_omega [hw, hj, hb, hss, hS, hnx, hab, hHt, pb, pc, hs1, hsw, ib, hwt]
  -- `0x8000f6d0`: `scale` stored, the `Vec` full or not
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f6d0_spec Q.pc (by
    rv_eval [B.x2]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b8000f6d0_keeps h₁
  have f₁ := b8000f6d0_frame h₁ (by rw [B.x2]; addr_omega [hb])
  rw [B.x2] at f₁
  rv_eval [] at f₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ : Base s t₁ := B.slots hpre x2₁ f₁ (by addr_omega [hb]) (by addr_omega [hb])
  have m240 := b8000f6d0_m_x2_240 h₁
  have m248 := b8000f6d0_m_x2_248 h₁
  have m256 := b8000f6d0_m_x2_256 h₁
  rw [B.x2] at m240 m248 m256
  rv_eval [] at m240 m248 m256
  have scale₁ : eAt t₁ (s.getReg .x2 - 1472) = acc.2.1 * (1 + rOf s k + ch) := by
    rw [← Q.sc]
    exact eAt_congr (by rv_eval [m240]) (by rv_eval [m248]) (by rv_eval [m256])
  have x23₁ : t₁.getReg .x23 = BitVec.ofNat 64 k := by
    rw [k₁ .x23 (by decide), Q.regs .x23 (by decide), P.x23]
  have F₁ : DFrame t t₁ (Within · (s.getReg .x2 - 1472) 24) := DFrame.of_memFrame f₁
  have hN₁ : heapNext t₁ = heapNext t := by
    simp only [heapNext]; rw [f₁ _ (by addr_omega [hb, hnx])]
  have k1 (y : Word) (h : ¬ Within y (s.getReg .x2 - 1472) 24) : t₁.getMem y = t.getMem y := f₁ y h
  have hk64 : k < 2 ^ 64 := by have := (w.getMem (s.getReg .x2 - 848)).isLt; omega
  have x23t : t.getReg .x23 = BitVec.ofNat 64 k := by rw [Q.regs .x23 (by decide), P.x23]
  have rt (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x20, .x23, .x25, .x26]) :
      t₁.getReg r = t.getReg r := k₁ r (mem_of_mem hr _)
  by_cases hfull : k = (w.getMem (s.getReg .x2 - 848)).toNat
  swap
  · -- room left
    have hlt : k < (w.getMem (s.getReg .x2 - 848)).toNat := by omega
    refine ⟨t₁, hr₁, Or.inl {
      pc := b8000f6d0_pc_taken h₁ (by
        rw [B.x2, x23t]; rv_eval []; rw [cap₀]
        intro h; apply hfull; rw [← h, BitVec.toNat_ofNat]; omega)
      base := B₁
      mono := by rw [hN₁]; exact hwt
      frame := (Q.frame.mono fun a h ↦ Or.inl (w8_mono (le_of_eq hN₁.symm) h)).trans F₁
        fun a h ↦ Or.inr (Or.inl h)
      x19 := by rw [rt .x19 (by decide), Q.x19]
      regs := fun r hr ↦ by
        rw [rt r (mem_sub (by decide) hr),
          Q.regs r hr]
      chL := by rw [rt .x18 (by decide), rt .x25 (by decide), rt .x20 (by decide)]; exact Q.chL
      value := by rw [← Q.value]; exact F₁.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb]
      scale := scale₁
      push := by rw [k1 _ (by addr_omega [hb]), k1 _ (by addr_omega [hb]), push₀, ptr₀, P.push]
      ptCap := by rw [k1 _ (by addr_omega [hb]), cap₀]; exact hlt
      ptBuf := by
        rw [k1 _ (by addr_omega [hb]), k1 _ (by addr_omega [hb]), cap₀, ptr₀, hN₁]
        rcases pb.2 with h | h
        · omega
        · exact ⟨pb.1, h.1, by omega⟩
      ptE := by
        rw [k1 _ (by addr_omega [hb]), ptr₀, ← ptE₀]
        exact F₁.eListAt fun j hj hw ↦ by
          rcases pb.2 with h | h
          · omega
          · addr_omega [hw, hj, hb, h, hHt, hab, hwt, hlt]
      rest := Q.rest.body hpre B B₁ (F₁.mono fun a h ↦ slots_body hpre (by addr_omega [hb])
        (by addr_omega [hb]) h) }⟩
  -- full: `grow_one`
  have pc₁ : t₁.pc = 0x8000f6f0 := b8000f6d0_pc_not_taken h₁ (by
    rw [B.x2, x23t]; rv_eval []; rw [cap₀]
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega)
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f6f0_spec pc₁ trivial
  have k₂ := b8000f6f0_keeps h₂
  have hm₂ := b8000f6f0_mem_same h₂
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := (k₂ .x2 (by decide)).trans x2₁
  have B₂ : Base s t₂ := B₁.same x2₂ hm₂
  have x10₂ : t₂.getReg .x10 = s.getReg .x2 - 848 := by rw [b8000f6f0_x10 h₂, x2₁]; rv_eval []
  have cap₂ : t₂.getMem (s.getReg .x2 - 848) = w.getMem (s.getReg .x2 - 848) := by
    rw [hm₂, k1 _ (by addr_omega [hb]), cap₀]
  have ptr₂ : t₂.getMem (s.getReg .x2 - 840) = w.getMem (s.getReg .x2 - 840) := by
    rw [hm₂, k1 _ (by addr_omega [hb]), ptr₀]
  have hN₂ : heapNext t₂ = heapNext t := by simp only [heapNext, hm₂]; exact hN₁
  have pre : GrowOnePre 24 8 t₂ := {
    heap := B₂.heap
    self := by rw [x10₂]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    raw := by
      rw [x10₂]
      simp only [RawVecOk, Buf, vecPtr, vecCap]
      rv_eval [cap₂, ptr₂]
      rw [hN₂]
      rcases pb.2 with h | h
      · exact ⟨pb.1, Or.inl h⟩
      · exact ⟨pb.1, Or.inr ⟨by omega, by omega⟩⟩
    stack := hpre.stack.sub 1712 x2₂ (by unfold verifyLayerStack; decide) (by decide) (by decide)
      (by decide) (by decide)
    selfFree := by rw [x10₂]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    selfStack := by rw [x10₂]; simp only [stackLo, x2₂]; addr_omega [hb] }
  obtain ⟨t₃, hr₃, ⟨hpc₃, hp₃, GP, NB⟩ | hd⟩ := hG.call (hr₁.trans hr₂) (b8000f6f0_pc h₂) pre
  swap
  · exact ⟨_, hr₃, Or.inr hd⟩
  have G₃ := DFrame.of_byteFrame GP.frame
  rw [x10₂] at G₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (hp₃.reg .x2).trans x2₂
  have B₃ : Base s t₃ := B₂.next hpre x2₃ GP.heap GP.mono G₃ fun a ha ↦
    cframe_lw hpre B₂ 848 (by decide) (by decide) (by decide) GP.heap rfl a ha
  simp only [stackLo, x2₂] at G₃
  have hcap := GP.cap
  have hbytes := GP.bytes
  have hmono := GP.mono
  have hH₃ := GP.heap.hi
  rw [x10₂] at hcap hbytes NB
  simp only [vecPtr, vecCap, NewBuf] at hcap hbytes NB
  rv_eval [cap₂, ptr₂] at hcap hbytes NB
  -- `0x8000f6fc`: the new pointer into the push slot
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000f6fc_spec
    (by rw [hpc₃, returnAddress_eq, b8000f6f0_x1 h₂]; decide) (by
      rv_eval [x2₃]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₄ := b8000f6fc_keeps h₄
  have f₄ := b8000f6fc_frame h₄ (by rw [x2₃]; addr_omega [hb])
  rw [x2₃] at f₄
  rv_eval [] at f₄
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1712 := (k₄ .x2 (by decide)).trans x2₃
  have B₄ : Base s t₄ := B₃.slots hpre x2₄ f₄ (by addr_omega [hb]) (by addr_omega [hb])
  have m112 := b8000f6fc_m_x2_112 h₄
  rw [x2₃] at m112
  rv_eval [] at m112
  have k4 (y : Word) (h : ¬ Within y (s.getReg .x2 - 1600) 8) : t₄.getMem y = t₃.getMem y := f₄ y h
  have hN₄ : heapNext t₄ = heapNext t₃ := by
    simp only [heapNext]; rw [k4 _ (by addr_omega [hb, hnx])]
  have k3 (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 848 ∨ (s.getReg .x2).toNat - 832 ≤ y.toNat ∧
        y.toNat + 8 ≤ (s.getReg .x2).toNat - 104) : t₃.getMem y = t₂.getMem y :=
    G₃ y fun i hi hw ↦ by
      simp only [Fresh] at hw
      rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hi, h1, h2, hb, hnx, hab, hH₃]
  have Gt : DFrame t t₄ (W8e s w t₄) :=
    ((((F₁.mono (w' := W8e s w t₄) fun a h ↦ Or.inr (Or.inl h)).trans (DFrame.of_same hm₂ _)
      fun _ h ↦ h).trans G₃ fun a h ↦ by
        simp only [W8e, W8, Fresh] at h ⊢
        rcases h with h | h | h | h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb]))))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨by omega, by omega⟩)))))))).trans (DFrame.of_memFrame f₄)
      fun a h ↦ Or.inr (Or.inr (Or.inl h)))
  have rt₄ (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x20, .x23, .x25, .x26]) :
      t₄.getReg r = t.getReg r := by
    rw [k₄ r (mem_of_mem hr _), hp₃.reg r (mem_of_mem hr _), k₂ r (mem_of_mem hr _),
      k₁ r (mem_of_mem hr _)]
  have hle : heapNext t ≤ heapNext t₄ := by rw [hN₄, ← hN₂]; exact hmono
  refine ⟨t₄, hr₃.trans hr₄, Or.inl {
    pc := b8000f6fc_pc h₄
    base := B₄
    mono := le_trans hwt hle
    frame := (Q.frame.mono fun a h ↦ Or.inl (w8_mono hle h)).trans Gt fun _ h ↦ h
    x19 := by rw [rt₄ .x19 (by decide), Q.x19]
    regs := fun r hr ↦ by
      rw [rt₄ r (mem_sub (by decide) hr),
        Q.regs r hr]
    chL := by rw [rt₄ .x18 (by decide), rt₄ .x25 (by decide), rt₄ .x20 (by decide)]; exact Q.chL
    value := by
      rw [← Q.value]
      refine eAt_congr ?_ ?_ ?_ <;> (try rv_eval []) <;>
        rw [k4 _ (by addr_omega [hb]), k3 _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), hm₂,
          k1 _ (by addr_omega [hb])]
    scale := by
      rw [← scale₁]
      refine eAt_congr ?_ ?_ ?_ <;> (try rv_eval []) <;>
        rw [k4 _ (by addr_omega [hb]), k3 _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), hm₂]
    push := by rw [m112, k4 _ (by addr_omega [hb])]
    ptCap := by rw [k4 _ (by addr_omega [hb])]; omega
    ptBuf := by
      rw [k4 _ (by addr_omega [hb]), k4 _ (by addr_omega [hb]), hN₄]
      rcases NB.2 with h | h
      · omega
      · exact ⟨NB.1, by rw [hN₂] at h; omega, h.2⟩
    ptE := by
      rw [k4 _ (by addr_omega [hb]), ← ptE₀,
        (DFrame.of_memFrame f₄).eListAt fun j hj hw ↦ by
          rcases NB.2 with h | h
          · omega
          · addr_omega [hw, hj, hb, h, hH₃, hab, hcap, hfull]]
      have e := eListAt_eq_of_bytesAt (n := k) (a := t₃.getMem (s.getReg .x2 - 840))
        (b := w.getMem (s.getReg .x2 - 840)) (by rw [hfull, Nat.mul_comm]; exact hbytes) NB.1 pb.1
      rw [e]
      exact (F₁.trans (DFrame.of_same hm₂ _) fun _ h ↦ h).eListAt fun j hj hw ↦ by
        rcases pb.2 with h | h
        · omega
        · addr_omega [hw, hj, hb, h, hHt, hab, hwt, hfull]
    rest := Q.rest.body hpre B B₄ ((((F₁.mono (w' := BodyW s t t₄) fun a h ↦
      slots_body hpre (by addr_omega [hb]) (by addr_omega [hb]) h).trans (DFrame.of_same hm₂ _)
      fun _ h ↦ h).trans G₃ fun a h ↦ by
        simp only [BodyW, Fresh] at h ⊢
        unfold verifyLayerStack
        rcases h with h | h | h | h
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)).trans (DFrame.of_memFrame f₄)
      fun a h ↦ slots_body hpre (by addr_omega [hb]) (by addr_omega [hb]) h) }⟩

theorem ofNat_succ24 (k : Nat) :
    BitVec.ofNat 64 (24 * k) + 24 = BitVec.ofNat 64 (24 * (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h : (24 : Word).toNat = 24 := rfl
  rw [h]; omega

theorem ofNat_succ1 (k : Nat) : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h : (1 : Word).toNat = 1 := rfl
  rw [h]; omega

set_option maxHeartbeats 16000000 in
/-- `0x8000f5bc`: the challenge pushed, the next round or the exit. -/
theorem pk_push {s w t : MachineState} {ip : Word} {c : E} {k : Nat} {acc : E × E × List E}
    {ch nv : E} (hpre : VerifyLayerPre s) (P : PK s w ip c k acc)
    (Q : Q3 s w t ip c k acc ch nv) :
    ∃ v, Reaches Image.code t v ∧
      (PK s v ip c (k + 1) (nv, acc.2.1 * (1 + rOf s k + ch), acc.2.2 ++ [ch]) ∨
        J8 s v ip c (nv, acc.2.1 * (1 + rOf s k + ch), acc.2.2 ++ [ch])) := by
  have hb := bounds hpre
  have B := Q.base
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  simp only [stackLo] at hnx hab hss
  unfold verifyLayerStack at hb hnx hab hss
  have hHt := B.heap.hi
  have hsw := P.base.mono
  have hwt := Q.mono
  have hHs := hpre.heap.lo
  have ib := P.ibuf
  have qb := Q.ptBuf
  have qc := Q.ptCap
  have hk := P.lt
  have pR := hpre.point
  simp only [VecRegion, vecPtr, vecLen, lClaim] at pR
  rv_eval [] at pR
  have hR : Region (s.getMem (s.getReg .x15 + 32)) (24 * (s.getMem (s.getReg .x15 + 40)).toNat) := by
    rcases pR with h0 | h0
    · omega
    · exact h0
  -- what the round kept of `w`'s slots
  have kq (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1600 ∨
        (s.getReg .x2).toNat - 1568 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 1472 ∨
        (s.getReg .x2).toNat - 1424 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 848 ∨
        (s.getReg .x2).toNat - 832 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 752 ∨
        (s.getReg .x2).toNat - 720 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 128) :
      t.getMem y = w.getMem y :=
    Q.frame y fun i hi hw ↦ by
      simp only [W8e, W8, Fresh] at hw
      rcases hw with (hw | hw | hw | hw | hw | hw | hw | hw) | hw | hw | hw <;>
        addr_omega [hw, hi, h1, h2, hb, hss, hS, hnx, hab, hHt]
  have hbuf : ValidMemRange (t.getMem (s.getReg .x2 - 840))
      (3 * (t.getMem (s.getReg .x2 - 848)).toNat) :=
    heap_vmr (by omega) (by omega) qb.1
  have x9t : t.getReg .x9 = BitVec.ofNat 64 (24 * k) := by rw [Q.regs .x9 (by decide), P.x9]
  have x23t : t.getReg .x23 = BitVec.ofNat 64 k := by rw [Q.regs .x23 (by decide), P.x23]
  -- `0x8000f5bc`
  obtain ⟨v, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f5bc_spec Q.pc (by
    rv_eval [B.x2, Q.push, x9t]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | valid_access hbuf [qb, qc, hHt]
      | addr_omega [hb, qb, qc, hHt, hab])
  have k₁ := b8000f5bc_keeps h₁
  have x2₁ : v.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have F₁ : DFrame t v fun a ↦ Within a (s.getReg .x2 - 832) 8 ∨
      Within a (t.getMem (s.getReg .x2 - 840) + BitVec.ofNat 64 (24 * k)) 24 :=
    dframe_of_writes h₁ (by rv_eval [B.x2, Q.push, x9t]; and_intros <;> addr_omega [hb, qb, qc, hHt])
  have hN₁ : v.getMem nextAddr = t.getMem nextAddr := F₁ _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hnx, qb, qc, hHt]
  have hNv : heapNext v = heapNext t := by simp only [heapNext, hN₁]
  have hW (a : Word) (ha : Within a (s.getReg .x2 - 832) 8 ∨
      Within a (t.getMem (s.getReg .x2 - 840) + BitVec.ofNat 64 (24 * k)) 24) :
      ¬ Within a (s.getReg .x11) 368 ∧ LW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
    simp only [LW, Fresh, stackLo]
    unfold verifyLayerStack
    rcases ha with ha | ha
    · exact ⟨by addr_omega [ha, hb, hss, hS], Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))),
        by addr_omega [ha, hb]⟩
    · refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))), ?_⟩
      · rcases hsf.1 with h | h <;> addr_omega [ha, h, qb, qc, ib, hsw, hwt, hHt, hS]
      · addr_omega [ha, qb, qc, ib, hsw, hwt, hHt]
      · rw [hNv]; addr_omega [ha, qb, qc, hHt]
      · addr_omega [ha, qb, qc, hHt, hb, hab]
  have B₁ : Base s v := B.next hpre x2₁
    ⟨by rw [hNv]; exact B.heap.lo, by rw [hNv]; exact B.heap.hi⟩ (le_of_eq hNv.symm) F₁
    fun a ha ↦ ⟨(hW a ha).2.1, (hW a ha).2.2⟩
  have R₁ := Q.rest.keep fun T hT ↦ B.tat hpre B₁.heap F₁ (fun a ha ↦ ⟨(hW a ha).1, (hW a ha).2.1⟩) hT
  have kv (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 832 ∨ (s.getReg .x2).toNat - 824 ≤ y.toNat ∧
        y.toNat + 8 ≤ (s.getReg .x2).toNat - 104) : v.getMem y = t.getMem y :=
    F₁ y fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, h1, h2, hb, qb, qc, hHt, hab]
  have kw (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1600) : v.getMem y = w.getMem y :=
    (kv y h1 (Or.inl (le_trans h2 (Nat.sub_le_sub_left (by decide) _)))).trans (kq y h1 (Or.inl h2))
  have m3 := b8000f5bc_m3 h₁
  have m2 := b8000f5bc_m2 h₁
  have m1 := b8000f5bc_m1 h₁
  have m880 := b8000f5bc_m_x2_880 h₁
  rv_eval [B.x2, Q.push, x9t] at m3 m2 m1
  rw [x23t, ofNat_succ1] at m880
  rv_eval [B.x2] at m880
  have hlen : (s.getMem (s.getReg .x15 + 40)).toNat < 2 ^ 59 := by addr_omega [hR]
  have ptE₁ : eListAt v (t.getMem (s.getReg .x2 - 840)) (k + 1) = acc.2.2 ++ [ch] := by
    rw [eListAt_snoc, ← Q.ptE, F₁.eListAt fun j hj hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hj, hb, qb, qc, hHt, hab]]
    congr 2
    apply eAt_eq_of_limbs
    rw [Q.chL]
    rv_eval [m1, m2, m3]
  have eV (a : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ a.toNat)
      (h2 : a.toNat + 24 ≤ (s.getReg .x2).toNat - 832 ∨ (s.getReg .x2).toNat - 824 ≤ a.toNat ∧
        a.toNat + 24 ≤ (s.getReg .x2).toNat - 104) : eAt v a = eAt t a :=
    F₁.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, h1, h2, hb, qb, qc, hHt, hab]
  have eW (a : Word) (h1 : (s.getReg .x2).toNat - 824 ≤ a.toNat)
      (h2 : a.toNat + 24 ≤ (s.getReg .x2).toNat - 752) : eAt v a = eAt w a := by
    rw [eV a (le_trans (Nat.sub_le_sub_left (by decide) _) h1)
      (Or.inr ⟨h1, le_trans h2 (Nat.sub_le_sub_left (by decide) _)⟩)]
    exact Q.frame.eAt fun j hj hw ↦ by
      simp only [W8e, W8, Fresh] at hw
      rcases hw with (hw | hw | hw | hw | hw | hw | hw | hw) | hw | hw | hw <;>
        addr_omega [hw, hj, h1, h2, hb, hss, hS, hnx, hab, hHt]
  have iwv : eListAt v ip 16 = instanceWeightsRust c := by
    rw [← P.iw, F₁.eListAt fun j hj hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hj, hb, qb, qc, ib, hHt, hab]]
    exact Q.frame.eListAt fun j hj hw ↦ by
      simp only [W8e, W8, Fresh] at hw
      rcases hsf.1 with h | h <;>
      rcases hw with (hw | hw | hw | hw | hw | hw | hw | hw) | hw | hw | hw <;>
        addr_omega [hw, hj, hb, hss, hS, hnx, hab, hHt, ib, hsw, h, hwt]
  have icapv : v.getMem (s.getReg .x2 - 1672) = w.getMem (s.getReg .x2 - 1672) :=
    kw _ (by addr_omega [hb]) (by addr_omega [hb])
  have capv : v.getMem (s.getReg .x2 - 848) = t.getMem (s.getReg .x2 - 848) :=
    kv _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))
  have ptrv : v.getMem (s.getReg .x2 - 840) = t.getMem (s.getReg .x2 - 840) :=
    kv _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))
  have endt : t.getMem (s.getReg .x2 - 1632) = s.getMem (s.getReg .x15 + 32) +
      BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x15 + 40)).toNat) := by
    rw [kq _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), P.endM]
  have regs (r : Reg) (hr : r ∈ [Reg.x26]) : v.getReg r = w.getReg r := by
    rw [k₁ r (mem_of_mem hr _), Q.regs r (mem_of_mem hr _)]
  have x20v : v.getReg .x20 = s.getReg .x11 := by
    rw [b8000f5bc_x20 h₁, B.x2]; rv_eval []
    rw [kq _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), P.p]
  by_cases hlast : k + 1 = (s.getMem (s.getReg .x15 + 40)).toNat
  · refine ⟨v, hr₁, Or.inr {
      pc := b8000f5bc_pc_taken h₁ (by rw [B.x2, Q.x19]; rv_eval [endt]; addr_omega [hR, hlast])
      base := B₁
      out := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb]), P.out]
      claim := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb]), P.claim]
      sponge := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb]), P.sponge]
      p := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb]), P.p]
      ipM := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb]), P.ipM]
      x20 := x20v
      x26 := by rw [regs .x26 (by decide), P.x26]
      iw := iwv
      ibuf := by rw [icapv, hNv]; exact ⟨ib.1, ib.2.1, ib.2.2.1, by omega⟩
      kappa := by rw [eW _ (by addr_omega [hb]) (by addr_omega [hb])]; exact P.kappa
      value := by rw [eV _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))]; exact Q.value
      scale := by rw [eV _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))]; exact Q.scale
      ptLen := by
        rw [m880, hlast]; exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega)
      ptCap := by rw [capv]; omega
      ptBuf := by rw [capv, ptrv, icapv, hNv]; exact ⟨qb.1, Or.inr qb.2⟩
      ptE := by rw [ptrv, ← hlast]; exact ptE₁
      rest := by
        have e := packRest_end (claimAt s (lClaim s)) (instanceWeightsRust c)
          (sumE (instanceWeightsRust c)) (nv, acc.2.1 * (1 + rOf s k + ch), acc.2.2 ++ [ch])
        rw [claim_point_length, ← hlast] at e
        rw [← e]; exact R₁ }⟩
  · refine ⟨v, hr₁, Or.inl {
      pc := b8000f5bc_pc_not_taken h₁ (by
        rw [B.x2, Q.x19]; rv_eval [endt]; intro h; apply hlast; addr_omega [hR, h, hk])
      base := B₁
      out := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb]), P.out]
      claim := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb]), P.claim]
      sponge := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb]), P.sponge]
      p := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb]), P.p]
      ipM := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb]), P.ipM]
      endM := by rw [kv _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), endt]
      cpM := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb]), P.cpM]
      push := by
        rw [kv _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), ptrv]; exact Q.push
      x9 := by rw [b8000f5bc_x9 h₁, x9t, ofNat_succ24]
      x23 := by rw [b8000f5bc_x23 h₁, x23t, ofNat_succ1]
      x20 := x20v
      x26 := by rw [regs .x26 (by decide), P.x26]
      lt := by omega
      iw := iwv
      ibuf := by rw [icapv, hNv]; exact ⟨ib.1, ib.2.1, ib.2.2.1, by omega⟩
      kappa := by rw [eW _ (by addr_omega [hb]) (by addr_omega [hb])]; exact P.kappa
      value := by rw [eV _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))]; exact Q.value
      scale := by rw [eV _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))]; exact Q.scale
      ptLen := m880
      ptCap := by rw [capv]; omega
      ptBuf := by rw [capv, ptrv, icapv, hNv]; exact ⟨qb.1, Or.inr qb.2⟩
      ptE := by rw [ptrv]; exact ptE₁
      rest := R₁ }⟩

/-- The pack loop from its head to its exit, an `Err` return or a dead end. -/
theorem pack_loop (hRP : RoundPolySpec) (hD : DuplexSpec) (hPE : MultilinearContracts.PolyEvalSpec)
    (hM : MulSpec) (hG : GrowOneFreshSpec 0x80011c78 24 8) {s : MachineState} {ip : Word} {c : E}
    (hpre : VerifyLayerPre s) :
    ∀ n k w acc, k + n = (s.getMem (s.getReg .x15 + 40)).toNat → PK s w ip c k acc →
      ∃ v acc', Reaches Image.code w v ∧ (J8 s v ip c acc' ∨ Ret s v ∨ Dead Image.code v)
  | 0, k, w, acc, hn, P => absurd P.lt (by omega)
  | n + 1, k, w, acc, hn, P => by
    obtain ⟨t₁, hr₁, ⟨msg, Q⟩ | hret | hd⟩ := pk_round hRP hpre P
    rotate_left
    · exact ⟨t₁, acc, hr₁, Or.inr (Or.inl hret)⟩
    · exact ⟨t₁, acc, hr₁, Or.inr (Or.inr hd)⟩
    obtain ⟨t₂, hr₂, ⟨ch, nv, Q₂⟩ | hd⟩ := pk_mid hD hPE hM hpre P Q
    swap
    · exact ⟨t₂, acc, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩
    obtain ⟨t₃, hr₃, Q₃ | hd⟩ := pk_store hG hpre P Q₂
    swap
    · exact ⟨t₃, acc, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inr hd)⟩
    obtain ⟨v, hr₄, P' | J⟩ := pk_push hpre P Q₃
    · obtain ⟨x, acc', hr, hx⟩ := pack_loop hRP hD hPE hM hG hpre n (k + 1) v _ (by omega) P'
      exact ⟨x, acc', hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr))), hx⟩
    · exact ⟨v, _, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl J⟩

/-- `J7` to the pack rounds' exit `J8`, an `Err` return or a dead end. -/
theorem pack (hRP : RoundPolySpec) (hD : DuplexSpec) (hPE : MultilinearContracts.PolyEvalSpec)
    (hM : MulSpec) (hG : GrowOneFreshSpec 0x80011c78 24 8) {s u : MachineState} {ip : Word}
    {product : List E} {c : E} (hpre : VerifyLayerPre s) (J : J7 s u ip product c) :
    ∃ v acc, Reaches Image.code u v ∧ (J8 s v ip c acc ∨ Ret s v ∨ Dead Image.code v) := by
  obtain ⟨w, hr, P | J'⟩ := pack_enter hpre J
  · obtain ⟨v, acc, hr', hv⟩ := pack_loop hRP hD hPE hM hG hpre _ 0 w _ (Nat.zero_add _) P
    exact ⟨v, acc, hr.trans hr', hv⟩
  · exact ⟨w, _, hr, Or.inl J'⟩

end Rv64Verifier.Gkr.Layer
