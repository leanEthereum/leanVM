import Rv64Verifier.Proofs.Gkr.LayerR16
import Rv64Verifier.Proofs.Gkr.Layer

/-!
# `keccak::verify_layer`: the claim returned

`0x800100e8..0x8001013c`: `Ok(KeccakClaim { mu, point, weights, value })` stored into the result
(`mu` and `point` from the frame, `weights` the `Vec` at `f + 960`, the value from `s3`, `s4`,
`s5`), then the epilogue (`exit`). With `R12..R16` this is `SecondHalf`.
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- A `Vec` stored into the result: its buffer new since `s`. -/
theorem newVecE_of {s t : MachineState} {a : Word} {cap ptr len : Word} {xs : List E}
    (hs : HeapOk s) (hc : t.getMem a = cap) (hp : t.getMem (a + 8) = ptr)
    (hl : t.getMem (a + 16) = len) (hlc : len.toNat ≤ cap.toNat)
    (hb : NewBuf s t ptr (cap.toNat * 24) 8) (he : eListAt t ptr len.toNat = xs) :
    NewVecE s t a xs := by
  have h0 := hs.lo
  simp only [NewBuf] at hb
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [RawVecOk, Buf, vecPtr, vecCap, hc, hp]; omega
  · simp only [vecLen, vecCap, hc, hl]; exact hlc
  · simp only [NewBuf, vecPtr, vecCap, hc, hp]; omega
  · simp only [vecEs, vecPtr, vecLen, hp, hl]; exact he

set_option maxHeartbeats 32000000 in
theorem finish {s u v : MachineState} {mu point eqZ eqLane t : List E} {beta : E}
    (hpre : VerifyLayerPre s) (J : J12 s u mu point eqZ eqLane t beta)
    (K : J17 s u v eqZ eqLane t beta) : ∃ w, Reaches Image.code v w ∧ Ret s w := by
  have hb := bounds hpre
  have B := K.base
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  simp only [stackLo] at hnx hab
  unfold verifyLayerStack at hb hnx hab
  have ho := hpre.out
  have hos := hpre.outStack
  have hof := hpre.outFree
  have hHv := B.heap.hi
  have hHu := J.base.heap.hi
  have hsu := J.base.mono
  have hkm := K.mono
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hosf := hpre.outSelf
  simp only [stackLo] at hos hss
  unfold verifyLayerStack at hos hss
  have slot (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 752) : v.getMem y = u.getMem y :=
    K.frame y (sw2_slot hpre hHv h1 (Or.inl h2))
  have hout : v.getMem (s.getReg .x2 - 1664) = s.getReg .x10 := by
    rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), J.out]
  -- `0x800100e8`: the result's stores
  obtain ⟨w₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800100e8_spec K.pc (by
    rv_eval [B.x2, hout]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho])
      | addr_omega [hb, ho, hos])
  have f₁ : MemFrame v w₁ (s.getReg .x10) 96 := h₁.memFrame (by
    rv_eval [B.x2, hout]; and_intros <;> addr_omega [ho])
  have x2₁ : w₁.getReg .x2 = s.getReg .x2 - 1712 := (b800100e8_keeps h₁ .x2 (by decide)).trans B.x2
  have hN₁ : w₁.getMem nextAddr = v.getMem nextAddr := f₁ _ (by addr_omega [ho, hof])
  have hN₁' : heapNext w₁ = heapNext v := by simp only [heapNext, hN₁]
  have B₁ : Base s w₁ := B.next hpre x2₁ ⟨by rw [hN₁']; exact B.heap.lo, by rw [hN₁']; exact hHv⟩
    (le_of_eq hN₁'.symm) (DFrame.of_memFrame f₁) fun a ha ↦
      ⟨Or.inl (by addr_omega [ha]), by addr_omega [ha, hos, hb]⟩
  have m (k : Nat) (hk : k ≤ 88) : w₁.getMem (s.getReg .x10 + BitVec.ofNat 64 k) =
      w₁.getMem (v.getMem (v.getReg .x2 + 48) + BitVec.ofNat 64 k) := by
    rw [B.x2]; rv_eval [hout]
  -- the frame from `u`, and what it keeps
  have F : DFrame u w₁ fun a ↦ BodyW s u w₁ a ∨ Within a (s.getReg .x10) 96 :=
    (K.frame.mono fun a h ↦ Or.inl (by
      simp only [SW2, BodyW, Fresh] at h ⊢
      unfold verifyLayerStack
      rcases h with h | h | h | h | h
      · exact Or.inl (by addr_omega [h, hb])
      · exact Or.inl (by addr_omega [h, hb])
      · exact Or.inl (by addr_omega [h, hb])
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h.1, by rw [hN₁']; exact h.2⟩))).trans
      (DFrame.of_memFrame f₁) fun a h ↦ Or.inr h
  have miss (p : Word) (n : Nat) (hp : p.toNat + n ≤ heapNext u) (hp0 : heapNext s ≤ p.toNat) :
      ∀ i < n, ¬ (BodyW s u w₁ (p + BitVec.ofNat 64 i) ∨ Within (p + BitVec.ofNat 64 i) (s.getReg .x10) 96) :=
    fun i hi hw ↦ by
      rcases hw with hw | hw
      · simp only [BodyW, Fresh] at hw
        unfold verifyLayerStack at hw
        rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hp, hb, hab, hnx, hHu]
      · rcases hof.1 with h | h <;> addr_omega [hw, hi, hp, h, hp0, hsu, hHu]
  have keepL (p : Word) (n : Nat) (hb' : NewBuf s u p (n * 24) 8) (k : Nat) (hk : k ≤ n) :
      eListAt w₁ p k = eListAt u p k := by
    simp only [NewBuf] at hb'
    rcases hb'.2 with h0 | ⟨h1, h2⟩
    · have : k = 0 := by omega
      subst this; rfl
    · exact F.eListAt fun i hi ↦ miss p (n * 24) h2 h1 i (by omega)
  -- the stores
  have e0 := b800100e8_m0 h₁
  have e1 := b800100e8_m1 h₁
  have e2 := b800100e8_m2 h₁
  have e3 := b800100e8_m3 h₁
  have e4 := b800100e8_m4 h₁
  have e5 := b800100e8_m5 h₁
  have e6 := b800100e8_m6 h₁
  have e7 := b800100e8_m7 h₁
  have e8 := b800100e8_m8 h₁
  have e9 := b800100e8_m9 h₁
  have e10 := b800100e8_m10 h₁
  have e11 := b800100e8_m11 h₁
  rw [B.x2] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  rv_eval [hout, K.x10, K.x11, K.x26] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  have sl (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 752) : w₁.getMem y = u.getMem y := by
    rw [f₁ _ (by addr_omega [h1, h2, hb, hos, ho]), slot y h1 h2]
  -- `mu`
  have muB := J.muBuf
  have hmu : NewVecE s w₁ (s.getReg .x10) mu := by
    refine newVecE_of hpre.heap (cap := u.getMem (s.getReg .x2 - 1672))
      (ptr := u.getMem (s.getReg .x2 - 1648)) (len := u.getReg .x26)
      (by rw [e7, slot _ (by addr_omega [hb]) (by addr_omega [hb])])
      (by rv_eval [e6, slot (s.getReg .x2 - 1648) (by addr_omega [hb]) (by addr_omega [hb])]) (by rv_eval [e5])
      J.muLen ?_ ?_
    · simp only [NewBuf] at muB ⊢; rw [hN₁']; omega
    · rw [keepL _ _ muB _ J.muLen, J.muE]
  have hcap : w₁.getMem (s.getReg .x10) ≠ errNiche := by
    rw [e7, slot _ (by addr_omega [hb]) (by addr_omega [hb])]
    intro h
    simp only [NewBuf, h, errNiche] at muB
    have := hHu
    simp only [heapEnd] at this
    rcases muB.2 with h0 | h0 <;>
      rw [show (0xffffffffffffffff : Word).toNat = 18446744073709551615 from rfl] at h0 <;> omega
  -- `point`
  obtain ⟨⟨pR, pL⟩, pB, pE⟩ := J.ptV
  simp only [RawVecOk, vecLen, vecCap, vecPtr, vecEs] at pR pL pB pE
  rv_eval [] at pR pL pB pE
  have hpt : NewVecE s w₁ (s.getReg .x10 + 24) point := by
    refine newVecE_of hpre.heap (cap := u.getMem (s.getReg .x2 - 848))
      (ptr := u.getMem (s.getReg .x2 - 840)) (len := u.getMem (s.getReg .x2 - 832))
      (by rv_eval [e4, slot (s.getReg .x2 - 848) (by addr_omega [hb]) (by addr_omega [hb])])
      (by rv_eval [e11, slot (s.getReg .x2 - 840) (by addr_omega [hb]) (by addr_omega [hb])])
      (by rv_eval [e10, slot (s.getReg .x2 - 832) (by addr_omega [hb]) (by addr_omega [hb])]) pL ?_ ?_
    · simp only [NewBuf] at pB ⊢; rw [hN₁']; omega
    · rw [keepL _ _ pB _ pL, pE]
  -- `weights`
  have ob := K.obuf
  have hw : NewVecE s w₁ (s.getReg .x10 + 48) (linearTransposeRust (nextWeightsRust eqZ eqLane beta)) := by
    refine newVecE_of hpre.heap (cap := v.getMem (s.getReg .x2 - 752))
      (ptr := v.getMem (s.getReg .x2 - 744)) (len := 1600) (by rv_eval [e9]) (by rv_eval [e8])
      (by rv_eval [e3]) (by rw [show (1600 : Word).toNat = 1600 from rfl]; exact K.ocap) ?_ ?_
    · simp only [NewBuf]; rw [hN₁']; exact ⟨ob.2.2, Or.inr ⟨by omega, ob.2.1⟩⟩
    · rw [show (1600 : Word).toNat = 1600 from rfl, ← K.oE]
      exact (DFrame.of_memFrame f₁).eListAt fun i hi hw ↦ by
        have := K.ocap
        rcases hof.1 with h | h <;> addr_omega [hw, hi, h, ob, hsu, hkm, hHv, this]
  have hval : eAt w₁ (s.getReg .x10 + 72) = t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0) := by
    apply eAt_eq_of_limbs
    rw [← K.val]; rv_eval [e0, e1, e2]
  have hrest : Rest s w₁ (pure ⟨t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0), mu, point,
      linearTransposeRust (nextWeightsRust eqZ eqLane beta)⟩) :=
    J.rest.keep fun T hT ↦ J.base.tat hpre B₁.heap F (fun a h ↦ by
      rcases h with h | h
      · exact bodyW_tat hpre J.base B₁.heap h
      · exact ⟨by addr_omega [h, hosf, ho, hS], Or.inl h⟩) hT
  obtain ⟨w₂, hr₂, pc₂, pres₂, same₂⟩ := exit hpre (b800100e8_pc h₁) x2₁ B₁.saved
  generalize linearTransposeRust (nextWeightsRust eqZ eqLane beta) = L at hw hrest
  generalize t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0) = V at hval hrest
  have hc : ClaimOut s w₁ (s.getReg .x10) ⟨V, mu, point, L⟩ := ⟨hmu, hpt, hw, hval⟩
  exact ⟨w₂, hr₁.trans hr₂, pc₂, pres₂, post_ok B₁ hcap hrest hc same₂⟩

/-! ## `SecondHalf` -/

theorem second_half (hA : AllocSpec) (hR : ReserveFreshSpec 0x80008a10 24 8) (hM : MulSpec)
    (hFE : MultilinearContracts.FromElemSpec) : SecondHalf := by
  intro s u mu point eqZ eqLane t beta hpre J
  have hsu := J.base.mono
  obtain ⟨v₁, hr₁, K₁ | hd⟩ := next_weights hA hR hM hpre J
  swap
  · exact ⟨v₁, hr₁, Or.inr hd⟩
  obtain ⟨v₂, hr₂, K₂ | hd⟩ := value_g hM hFE hpre J K₁
  swap
  · exact ⟨v₂, hr₁.trans hr₂, Or.inr hd⟩
  obtain ⟨v₃, hr₃, K₃ | hd⟩ := columns hFE hpre hsu K₂
  swap
  · exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inr hd⟩
  obtain ⟨v₄, hr₄, K₄ | hd⟩ := output hA hR hpre hsu K₃
  swap
  · exact ⟨v₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr hd⟩
  obtain ⟨v₅, hr₅, hret⟩ := finish hpre J K₄
  exact ⟨v₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inl hret⟩

end Rv64Verifier.Gkr.Layer
