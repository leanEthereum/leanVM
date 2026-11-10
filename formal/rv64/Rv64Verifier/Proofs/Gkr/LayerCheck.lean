import Rv64Verifier.Proofs.Gkr.LayerIota

/-!
# `keccak::verify_layer`: the first check

`keccak.rs:136-146`: the point's length checked and `eq_kernel` of its segment part into
`f + 1560` (`to_iota`), the segment loop (`LayerIota.lean`), then `projected + iota * sum(mu)`
against the claim's value (`check`): on a mismatch `Err(KeccakProduct)` returned (`err_exit`), on
a match the state at `0x8000f294` (`J3`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- `verify_layer` returned. -/
def Ret (s t : MachineState) : Prop :=
  t.pc = returnAddress s ∧ Preserves s t ∧ VerifyLayerPost s t

/-- The segments' weights. -/
def segsOf (s : MachineState) : List E :=
  eqKernelRust ((claimAt s (lClaim s)).point.drop ((s.getReg .x12).toNat - 4))

/-- What a stretch of the body writes: the frame and the callees' stacks below it, `NEXT`, and
what it allocates. -/
@[rv_addr] def BodyW (s u v : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - BitVec.ofNat 64 verifyLayerStack) verifyLayerStack ∨
    Within a nextAddr 8 ∨ Fresh u v a

theorem bodyW_tat {s u v : MachineState} (hpre : VerifyLayerPre s) (B : Base s u) (hH : HeapOk v)
    {a : Word} (h : BodyW s u v a) : ¬ Within a (s.getReg .x11) 368 ∧ LW s v a := by
  have hb := bounds hpre
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hm := B.mono
  have := hH.hi
  unfold verifyLayerStack at hb hss
  simp only [BodyW, LW, Fresh] at h ⊢
  rcases h with h | h | h
  · exact ⟨by addr_omega [h, hb, hss, hS], Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))⟩
  · exact ⟨by addr_omega [h, hsf.2, hS], Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
  · exact ⟨by addr_omega [h, hsf.1, hm, this, hS], Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h.2⟩)))⟩

/-- The transcript is kept by a stretch of the body. -/
theorem Base.tat' {s u v : MachineState} (hpre : VerifyLayerPre s) (B : Base s u) (Bv : Base s v)
    (F : DFrame u v (BodyW s u v)) {T : TState} (hT : TranscriptAt u (s.getReg .x11) T) :
    TranscriptAt v (s.getReg .x11) T :=
  B.tat hpre Bv.heap F (fun _ h ↦ bodyW_tat hpre B Bv.heap h) hT

theorem Rest.body {s u v : MachineState} {k : TM KeccakClaim} (hpre : VerifyLayerPre s)
    (B : Base s u) (Bv : Base s v) (F : DFrame u v (BodyW s u v)) (h : Rest s u k) : Rest s v k :=
  h.keep fun _ hT ↦ B.tat' hpre Bv F hT

/-- A callee's frame: its result in the frame's slots at `f + 1712 - K`, its stack below the
frame, `NEXT` and what it allocates. -/
theorem cframe_lw {s u v : MachineState} (hpre : VerifyLayerPre s) (B : Base s u) {n k : Nat}
    (K : Nat) (hK : n + 104 ≤ K) (hK' : K ≤ 1712) (hk : k ≤ sumcheckStack) (hH : HeapOk v)
    {lo : Word} (hlo : lo = s.getReg .x2 - BitVec.ofNat 64 K) (a : Word)
    (ha : Within a lo n ∨ Within a (stackLo u k) k ∨ Within a nextAddr 8 ∨ Fresh u v a) :
    LW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hm := B.mono
  have := hH.hi
  rw [hlo] at ha
  simp only [stackLo, B.x2] at ha
  simp only [LW, Fresh] at ha ⊢
  unfold verifyLayerStack at hb hnx hab ⊢
  rcases ha with h | h | h | h
  · exact ⟨Or.inr (Or.inr (Or.inl (by addr_omega [h, hb, hK, hK']))), by addr_omega [h, hb, hK, hK']⟩
  · exact ⟨Or.inr (Or.inr (Or.inl (by addr_omega [h, hb, hk]))), by addr_omega [h, hb, hk]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl h))), by addr_omega [h, hb, hnx]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h.2⟩))), by addr_omega [h, hb, hab, this]⟩

/-- The same callee's frame is a stretch of the body. -/
theorem cframe_body {s u v u₀ v₀ : MachineState} (hpre : VerifyLayerPre s) (B : Base s u)
    {n k : Nat} (K : Nat) (hK : n ≤ K) (hK' : K ≤ 1712) (hk : k ≤ sumcheckStack)
    (hu : heapNext u₀ ≤ heapNext u) (hv : heapNext v ≤ heapNext v₀)
    {lo : Word} (hlo : lo = s.getReg .x2 - BitVec.ofNat 64 K) (a : Word)
    (ha : Within a lo n ∨ Within a (stackLo u k) k ∨ Within a nextAddr 8 ∨ Fresh u v a) :
    BodyW s u₀ v₀ a := by
  have hb := bounds hpre
  rw [hlo] at ha
  simp only [stackLo, B.x2] at ha
  simp only [BodyW, Fresh] at ha ⊢
  unfold verifyLayerStack at hb ⊢
  rcases ha with h | h | h | h
  · exact Or.inl (by addr_omega [h, hb, hK, hK'])
  · exact Or.inl (by addr_omega [h, hb, hk])
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

theorem bodyW_mono {s u v u' v' : MachineState} (hu : heapNext u ≤ heapNext u')
    (hv : heapNext v' ≤ heapNext v) {a : Word} (h : BodyW s u' v' a) : BodyW s u v a := by
  simp only [BodyW, Fresh] at h ⊢
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

/-- Writes to the frame's slots are a stretch of the body. -/
theorem slots_body {s u v : MachineState} (hpre : VerifyLayerPre s) {a lo : Word} {n : Nat}
    (h1 : (s.getReg .x2).toNat - 1712 ≤ lo.toNat) (h2 : lo.toNat + n ≤ (s.getReg .x2).toNat)
    (ha : Within a lo n) : BodyW s u v a := by
  have hb := bounds hpre
  unfold verifyLayerStack at hb
  exact Or.inl (by unfold verifyLayerStack; addr_omega [hb, h1, h2, ha])

/-! ## `eq_kernel` of the segment part -/

/-- At the segment loop's head `0x8000f93c`, before the first segment. -/
structure I0 (s o : MachineState) (sg pp : Word) (product : List E) : Prop where
  pc : o.pc = 0x8000f93c
  ok : QOk s o (vecPtr s (lClaim s + 48)) sg (segsOf s) (claimAt s (lClaim s)).weights
  q : QO s o o sg (segsOf s) (claimAt s (lClaim s)).weights 0
  mp : o.getMem (s.getReg .x2 - 1680) = vecPtr s (lClaim s)
  plenM : o.getMem (s.getReg .x2 - 1672) = 47
  out : o.getMem (s.getReg .x2 - 1664) = s.getReg .x10
  claim : o.getMem (s.getReg .x2 - 1656) = s.getReg .x15
  p : o.getMem (s.getReg .x2 - 1608) = s.getReg .x11
  ppM : o.getMem (s.getReg .x2 - 1600) = pp
  x8 : o.getReg .x8 = vecLen s (lClaim s)
  acc : (o.getReg .x27, o.getReg .x26, o.getReg .x25) =
    limbs (projectedRust (claimAt s (lClaim s)).mu product)
  plen : product.length = 47
  prod : eListAt o pp 47 = product
  pbuf : heapNext s ≤ pp.toNat ∧ pp.toNat + 24 * 47 ≤ heapNext o
  rest : Rest s o (TM.require (check1 (shapeOf s) (s.getReg .x14).toNat (claimAt s (lClaim s))
    product) >>= fun _ ↦ stage2 (claimAt s (lClaim s)) product)

set_option maxHeartbeats 8000000 in
theorem to_iota (hEK : EqKernelSpec) {s u : MachineState} {pp : Word} {product : List E}
    (hpre : VerifyLayerPre s) (J : J1 s u pp product) :
    ∃ o sg, Reaches Image.code u o ∧ (I0 s o sg pp product ∨ Dead Image.code o) := by
  have hb := bounds hpre
  have B := J.base
  have S := J.slots
  have hc := hpre.claim
  have hcs := hpre.claimStack
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hrs := hpre.stack.rodata
  unfold verifyLayerStack at hb hsm hab hnx hrs hcs
  have kc (y : Word) (h1 : (lClaim s).toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ (lClaim s).toNat + 96) :
      u.getMem y = s.getMem y :=
    B.keep (missClaim hpre B.heap) (by addr_omega [hc]) h1 h2
  -- the point
  have pR := hpre.point
  have pS := hpre.pointStack
  have pF := hpre.pointFree
  have pO := hpre.pointOut
  simp only [VecRegion, VecApart, VecOutside, vecPtr, vecLen, lClaim] at pR pS pF pO
  rv_eval [] at pR pS pF pO
  unfold verifyLayerStack at pS
  have cvec : (claimAt s (lClaim s)).point =
      eListAt s (s.getMem (s.getReg .x15 + 32)) (s.getMem (s.getReg .x15 + 40)).toNat := by
    simp only [claimAt, vecEs, vecPtr, vecLen, lClaim]; rv_eval []
  -- `0x8000f1cc`: the slice bound
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f1cc_spec J.pc (by
    rv_eval [B.x2, S.claim]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc]))
  have k₁ := b8000f1cc_keeps h₁
  have hm₁ := b8000f1cc_mem_same h₁
  have hlen : u.getMem (s.getReg .x15 + 40) = s.getMem (s.getReg .x15 + 40) :=
    kc _ (by addr_omega [hc]) (by addr_omega [hc])
  by_cases hlt : (s.getMem (s.getReg .x15 + 40)).toNat < (s.getReg .x12 - 4).toNat
  · refine ⟨t₁, 0, hr₁, Or.inr (dead_of_fetch ?_)⟩
    rw [b8000f1cc_pc_taken h₁ (by rw [B.x2, J.x24]; rv_eval [S.claim, hlen]; exact hlt)]
    exact trap
  have hpb : 4 ≤ (s.getReg .x12).toNat ∧ (s.getReg .x12 - 4).toNat = (s.getReg .x12).toNat - 4 := by
    have hsub : (s.getReg .x12 - 4).toNat = ((s.getReg .x12).toNat + (2 ^ 64 - 4)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub, show (4 : Word).toNat = 4 from rfl]; omega
    have := (s.getReg .x12).isLt
    rcases pR with h0 | hR
    · rw [h0] at hlt; omega
    · have hR' : (s.getMem (s.getReg .x15 + 40)).toNat < 2 ^ 59 := by addr_omega [hR]
      omega
  obtain ⟨hpb4, hpbn⟩ := hpb
  have hPs : (s.getReg .x12).toNat - 4 ≤ (s.getMem (s.getReg .x15 + 40)).toNat := by omega
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have x9₁ : t₁.getReg .x9 = s.getReg .x15 := by rw [b8000f1cc_x9 h₁, B.x2]; rv_eval [S.claim]
  have x10₁ : t₁.getReg .x10 = s.getMem (s.getReg .x15 + 40) := by
    rw [b8000f1cc_x10 h₁, B.x2]; rv_eval [S.claim, hlen]
  have x24₁ : t₁.getReg .x24 = s.getReg .x12 - 4 := by rw [b8000f1cc_x24 h₁, J.x24]
  -- `0x8000f1dc`: `eq_kernel(&claim.point[pack_bits..])` into `f + 1560`
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f1dc_spec
    (b8000f1cc_pc_not_taken h₁ (by rw [B.x2, J.x24]; rv_eval [S.claim, hlen]; omega)) (by
      rv_eval [x9₁]
      refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc])
  have k₂ := b8000f1dc_keeps h₂
  have hm₂ := b8000f1dc_mem_same h₂
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := (k₂ .x2 (by decide)).trans x2₁
  have hc32 : t₁.getMem (s.getReg .x15 + 32) = s.getMem (s.getReg .x15 + 32) := by
    rw [hm₁, kc _ (by addr_omega [hc]) (by addr_omega [hc])]
  have x10₂ : t₂.getReg .x10 = s.getReg .x2 - 152 := by rw [b8000f1dc_x10 h₂, x2₁]; rv_eval []
  have x11₂ : t₂.getReg .x11 = s.getMem (s.getReg .x15 + 32) +
      BitVec.ofNat 64 (24 * ((s.getReg .x12).toNat - 4)) := by
    rw [b8000f1dc_x11 h₂, x9₁, hc32, x24₁, Open.mul24, hpbn]
  have x12₂ : (t₂.getReg .x12).toNat = (s.getMem (s.getReg .x15 + 40)).toNat -
      ((s.getReg .x12).toNat - 4) := by
    rw [b8000f1dc_x12 h₂, x10₁, x24₁, BitVec.toNat_sub, hpbn]
    have := (s.getMem (s.getReg .x15 + 40)).isLt
    omega
  have hm12 (a : Word) : t₂.getMem a = u.getMem a := by rw [hm₂, hm₁]
  have B₂ : Base s t₂ := B.same x2₂ hm12
  have mp0 := missVec B₂.heap hpre.point hpre.pointOut hpre.pointSelf hpre.pointStack hpre.pointFree
  simp only [vecPtr, vecLen, lClaim] at mp0
  rv_eval [] at mp0
  have hek : EqKernelPre t₂ := {
    heap := B₂.heap
    out := by rw [x10₂]; addr_omega [hb, hsm]
    point := by
      rw [x12₂, x11₂]
      rcases pR with h0 | hR
      · left; omega
      · by_cases h0 : (s.getMem (s.getReg .x15 + 40)).toNat - ((s.getReg .x12).toNat - 4) = 0
        · left; exact h0
        · right; addr_omega [hR, hPs, h0]
    stack := hpre.stack.sub 1712 x2₂ (by unfold verifyLayerStack; decide) (by decide) (by decide)
      (by decide) (by decide)
    outFree := by rw [x10₂]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    pointFree := by
      rw [x12₂, x11₂]
      right
      have hmono := B₂.mono
      rcases pR with h0 | hR
      · rw [show (s.getReg .x12).toNat - 4 = 0 by omega, h0]
        refine ⟨?_, Or.inl rfl⟩
        have := pF.1
        addr_omega [this, hmono]
      · addr_omega [pF, hmono, hR, hPs]
    outStack := by rw [x10₂]; simp only [stackLo, x2₂]; addr_omega [hb]
    pointStack := by
      rw [x12₂, x11₂]; simp only [stackLo, x2₂]
      rcases pR with h0 | hR
      · rw [show (s.getReg .x12).toNat - 4 = 0 by omega, h0]; exact Or.inl rfl
      · addr_omega [pS, hR, hPs, hb]
    pointOut := by
      rw [x12₂, x11₂, x10₂]
      rcases pR with h0 | hR
      · rw [show (s.getReg .x12).toNat - 4 = 0 by omega, h0]; exact Or.inl rfl
      · addr_omega [pS, hR, hPs, hb]
    rodata := B₂.rodata hpre
    outRodata := by rw [x10₂]; addr_omega [hrs, hb] }
  obtain ⟨e₁, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hd⟩ := hEK.call (hr₁.trans hr₂) (b8000f1dc_pc h₂) hek
  swap
  · exact ⟨_, 0, hr₃, Or.inr hd⟩
  have G₃ := hpost₃.frame
  have V₃ := hpost₃.value
  rw [x10₂] at G₃ V₃
  rw [x11₂, x12₂] at V₃
  have hH₃ := hpost₃.heap
  have hH3 := hH₃.hi
  have mono₃ := hpost₃.mono
  have x2e : e₁.getReg .x2 = s.getReg .x2 - 1712 := (hpres₃.reg .x2).trans x2₂
  have B₃ : Base s e₁ := B₂.next hpre x2e hH₃ mono₃ G₃ fun a ha ↦
    cframe_lw hpre B₂ 152 (by decide) (by decide) (by decide) hH₃ rfl a ha
  have F₃ : DFrame t₂ e₁ (BodyW s u e₁) := G₃.mono fun a ha ↦
    cframe_body hpre B₂ 152 (by decide) (by decide) (by decide)
      (by simp only [heapNext, hm12]; exact le_refl _) (le_refl _) rfl a ha
  simp only [stackLo, x2₂] at G₃
  have sgv : eqKernelRust (eListAt t₂ (s.getMem (s.getReg .x15 + 32) +
      BitVec.ofNat 64 (24 * ((s.getReg .x12).toNat - 4)))
      ((s.getMem (s.getReg .x15 + 40)).toNat - ((s.getReg .x12).toNat - 4))) = segsOf s := by
    rw [segsOf, cvec, Open.eListAt_drop]
    congr 1
    rcases pR with h0 | hR
    · simp only [h0, Nat.zero_sub]; rfl
    · rw [B₂.eListAt (lo := s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * ((s.getReg .x12).toNat - 4)))
        (n := (s.getMem (s.getReg .x15 + 40)).toNat - ((s.getReg .x12).toNat - 4)) (fun y hy ↦ mp0 y (by addr_omega [hy, hR, hPs])) (Or.inr (by addr_omega [hR, hPs]))]
  have hsg : NewVecE t₂ e₁ (s.getReg .x2 - 152) (segsOf s) := by rw [← sgv]; exact V₃
  have hsl : (vecLen e₁ (s.getReg .x2 - 152)).toNat = (segsOf s).length := by
    rw [← hsg.elems]; simp only [vecEs, eListAt_length]
  have hsl1 : 1 ≤ (segsOf s).length := by
    rw [segsOf, eqKernelRust_eq, eqKernel_length]; exact Nat.one_le_two_pow
  have sgE := hsg.elems
  have sgB := hsg.buf
  have sgL := hsg.vec.len
  simp only [vecEs, vecPtr, vecLen, vecCap, NewBuf] at sgE sgB sgL hsl
  rv_eval [] at sgE sgB sgL hsl
  -- what the call kept
  have keepE (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 152) : e₁.getMem y = u.getMem y := by
    rw [G₃ y fun i hi h ↦ by
      rcases h with h | h | h | h <;> addr_omega [h, hi, h1, h2, hb, hnx, hab, hH3], hm12]
  have dep : e₁.getMem (s.getReg .x2 - 1616) = 12 := by
    rw [keepE _ (by addr_omega [hb]) (by addr_omega [hb]), S.depth, hpre.depth]
  -- `0x8000f200`: `24 / depth` segments, at least one
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000f200_spec
    (by rw [hpc₃, returnAddress_eq, b8000f1dc_x1 h₂]; decide) (by
      rv_eval [x2e]; valid_access hpre.stack.valid [hb])
  have k₄ := b8000f200_keeps h₄
  have hm₄ := b8000f200_mem_same h₄
  have pc₄ : t₄.pc = 0x8000f89c := b8000f200_pc_taken h₄ (by rw [x2e]; rv_eval [dep]; try decide)
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1712 := (k₄ .x2 (by decide)).trans x2e
  have B₄ : Base s t₄ := B₃.same x2₄ hm₄
  have x9₄ : t₄.getReg .x9 = s.getReg .x15 := by
    rw [k₄ .x9 (by decide), hpres₃.reg .x9, k₂ .x9 (by decide), x9₁]
  have kc4 (y : Word) (h1 : (lClaim s).toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ (lClaim s).toNat + 96) :
      t₄.getMem y = s.getMem y :=
    B₄.keep (missClaim hpre B₄.heap) (by addr_omega [hc]) h1 h2
  have c56 : t₄.getMem (s.getReg .x15 + 56) = vecPtr s (lClaim s + 48) :=
    (kc4 (s.getReg .x15 + 56) (by addr_omega [hc]) (by addr_omega [hc])).trans
      (by simp only [vecPtr, lClaim]; rv_eval [])
  have c64 : t₄.getMem (s.getReg .x15 + 64) = vecLen s (lClaim s + 48) :=
    (kc4 (s.getReg .x15 + 64) (by addr_omega [hc]) (by addr_omega [hc])).trans
      (by simp only [vecLen, lClaim]; rv_eval [])
  -- `0x8000f89c`: the segment loop's slots
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000f89c_spec pc₄ (by
    rv_eval [x2₄, x9₄]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc])
      | addr_omega [hb, hcs, hc])
  have k₅ := b8000f89c_keeps h₅
  have f₅ := b8000f89c_frame h₅ (by rw [x2₄]; addr_omega [hb])
  rw [x2₄] at f₅
  rv_eval [] at f₅
  have x2₅ : t₅.getReg .x2 = s.getReg .x2 - 1712 := (k₅ .x2 (by decide)).trans x2₄
  have B₅ : Base s t₅ := B₄.slots hpre x2₅ f₅ (by addr_omega [hb]) (by addr_omega [hb])
  have x10₄ : t₄.getReg .x10 = 24 := b8000f200_x10 h₄
  have x13₄ : t₄.getReg .x13 = 12 := by rw [b8000f200_x13 h₄, x2e]; rv_eval [dep]
  have x21₅ : t₅.getReg .x21 = 2 := h₅.reg_eq .x21 rfl (by rv_eval [x10₄, x13₄]; decide)
  have m64 := b8000f89c_m_x2_64 h₅
  have m72 := b8000f89c_m_x2_72 h₅
  have m80 := b8000f89c_m_x2_80 h₅
  have m88 := b8000f89c_m_x2_88 h₅
  rw [x2₄] at m64 m72 m80 m88
  rw [x9₄] at m72
  rv_eval [] at m64 m72 m80 m88
  have m5 (y : Word) (h : ¬ Within y (s.getReg .x2 - 1648) 32) : t₅.getMem y = e₁.getMem y := by
    rw [f₅ y h, hm₄]
  have hN5 : heapNext t₅ = heapNext e₁ := by
    simp only [heapNext]; rw [m5 _ (by addr_omega [hb, hnx])]
  have hNu : heapNext u ≤ heapNext t₅ := by
    rw [hN5]; have := mono₃; simp only [heapNext, hm12] at this ⊢; exact this
  have Fu5 : DFrame u t₅ (BodyW s u t₅) :=
    ((((DFrame.of_same hm12 _).trans F₃ fun a h ↦ bodyW_mono (le_refl _) (le_of_eq hN5.symm) h).trans
      (DFrame.of_same hm₄ _) fun _ h ↦ h).trans (DFrame.of_memFrame f₅) fun a h ↦
        slots_body hpre (by addr_omega [hb]) (by addr_omega [hb]) h)
  -- the segments' weights
  have sgE5 : eListAt t₅ (e₁.getMem (s.getReg .x2 - 144)) (segsOf s).length = segsOf s := by
    rw [← hsl, ← sgE]
    exact ((DFrame.of_same hm₄ _).trans (DFrame.of_memFrame f₅) fun _ h ↦ h).eListAt
      fun i hi hw ↦ by addr_omega [hi, hw, sgB, sgL, hH3, hb, hab, hsl, hsl1]
  -- the claim's position weights
  have hwR := hpre.weights
  have hwS := hpre.weightsStack
  unfold verifyLayerStack at hwS
  have hwlen : (claimAt s (lClaim s)).weights.length = (vecLen s (lClaim s + 48)).toNat := by
    simp only [claimAt, vecEs, eListAt_length]
  have ew : eListAt t₅ (vecPtr s (lClaim s + 48)) (vecLen s (lClaim s + 48)).toNat =
      (claimAt s (lClaim s)).weights := by
    rw [B₅.eListAt (missVec B₅.heap hpre.weights hpre.weightsOut hpre.weightsSelf
      hpre.weightsStack hpre.weightsFree) (by
        rcases hwR with h0 | hR
        · exact Or.inl h0
        · exact Or.inr (by addr_omega [hR]))]
    rfl
  have hkeep (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1648 ∨ (s.getReg .x2).toNat - 1616 ≤ y.toNat)
      (h3 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 152) : t₅.getMem y = u.getMem y := by
    rw [m5 y (by addr_omega [h1, h2, h3, hb]), keepE y h1 h3]
  refine ⟨t₅, e₁.getMem (s.getReg .x2 - 144), hr₃.trans (hr₄.trans hr₅), Or.inl {
    pc := b8000f89c_pc h₅
    ok := {
      base := B₅
      wok := {
        x9 := by rw [b8000f89c_x9 h₅, x9₄, c64, hwlen]
        x22 := b8000f89c_x22 h₅
        elems := fun j hj ↦ by rw [← ew, getD_eListAt _ _ (by rw [← hwlen]; exact hj)]
        region := fun j hj ↦ by
          rcases hwR with h0 | hR
          · rw [hwlen, h0] at hj; omega
          · rw [hwlen] at hj; addr_omega [hR, hj] }
      wS := fun j hj ↦ by
        rcases hwR with h0 | hR
        · rw [hwlen, h0] at hj; omega
        · rw [hwlen] at hj; addr_omega [hR, hj, hwS, hb]
      sgE := fun k hk ↦ by rw [← sgE5, getD_eListAt _ _ hk]
      sgR := by
        have h0 := B₂.heap.lo
        have h3 := hH₃.hi
        simp only [heapStart, heapEnd] at h0 h3 ⊢
        rcases sgB with ⟨ha, hz | ⟨h1, h2⟩⟩
        · omega
        · exact ⟨by omega, by omega, ha⟩
      step := hpre.step
      rc := m64
      wpM := by rw [m72, c56]
      nstep := by
        rw [m80, hm₄, keepE _ (by addr_omega [hb]) (by addr_omega [hb]), S.step]
      endM := by rw [m88, hm₄, hm₄, Open.mul24, hsl]
      depth := by rw [m5 _ (by addr_omega [hb]), dep] }
    q := {
      base := B₅
      regs := fun _ _ ↦ rfl
      x11 := by
        rw [b8000f89c_x11 h₅, x2₄, show BitVec.ofNat 64 (24 * 0) = 0 from rfl, Sym.add_zero_lit]
        rv_eval [hm₄]
      x21 := by rw [x21₅]; rfl
      x23 := by rw [b8000f89c_x23 h₅]; rfl
      acc := by
        rw [b8000f89c_x19 h₅, b8000f89c_x20 h₅, b8000f89c_x24 h₅]; exact limbs_zero.symm
      lt := by decide
      le := Nat.zero_le _
      frame := DFrame.refl _ _ }
    mp := by rw [hkeep _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])) (by addr_omega [hb]), S.mp]
    plenM := by
      rw [hkeep _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])) (by addr_omega [hb]), S.plen]
    out := by rw [hkeep _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])) (by addr_omega [hb]), S.out]
    claim := by
      rw [hkeep _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])) (by addr_omega [hb]), S.claim]
    p := by rw [hkeep _ (by addr_omega [hb]) (Or.inr (by addr_omega [hb])) (by addr_omega [hb]), S.p]
    ppM := by
      rw [hkeep _ (by addr_omega [hb]) (Or.inr (by addr_omega [hb])) (by addr_omega [hb]), S.pp]
    x8 := by
      rw [k₅ .x8 (by decide), k₄ .x8 (by decide), hpres₃.reg .x8, k₂ .x8 (by decide),
        k₁ .x8 (by decide), J.x8]
    acc := by
      rw [k₅ .x27 (by decide), k₄ .x27 (by decide), hpres₃.reg .x27, k₂ .x27 (by decide),
        k₁ .x27 (by decide), k₅ .x26 (by decide), k₄ .x26 (by decide), hpres₃.reg .x26,
        k₂ .x26 (by decide), k₁ .x26 (by decide), k₅ .x25 (by decide), k₄ .x25 (by decide),
        hpres₃.reg .x25, k₂ .x25 (by decide), k₁ .x25 (by decide), J.acc]
    plen := J.plen
    prod := by
      rw [← J.prod]
      have hpb := J.pbuf
      have hHu := B.heap.hi
      have hHs := hpre.heap.lo
      exact Fu5.eListAt fun i hi hw ↦ by
        simp only [BodyW, Fresh] at hw
        unfold verifyLayerStack at hw
        rcases hw with hw | hw | hw <;> addr_omega [hi, hw, hpb, hHu, hHs, hb, hab]
    pbuf := ⟨J.pbuf.1, by have := J.pbuf.2; omega⟩
    rest := J.rest.body hpre B B₅ Fu5 }⟩

/-! ## The check -/

theorem limbs_sum_eq {x y z : E} : x + y = z ↔ ((limbs y).1 ^^^ (limbs x).1 = (limbs z).1 ∧
    (limbs y).2.1 ^^^ (limbs x).2.1 = (limbs z).2.1 ∧ (limbs y).2.2 ^^^ (limbs x).2.2 = (limbs z).2.2) := by
  constructor
  · rintro rfl
    rw [limbs_add]
    exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩
  · rintro ⟨h1, h2, h3⟩
    apply eq_of_limbs
    rw [limbs_add]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact (BitVec.xor_comm _ _).trans h1
    · exact (BitVec.xor_comm _ _).trans h2
    · exact (BitVec.xor_comm _ _).trans h3

theorem stk_body {s u v : MachineState} (hpre : VerifyLayerPre s) {a : Word}
    (h : Within a (s.getReg .x2 - 2736) 2736) : BodyW s u v a := by
  have hb := bounds hpre
  unfold verifyLayerStack at hb
  exact Or.inl (by unfold verifyLayerStack; addr_omega [hb, h])

/-- `0x8000f9cc`: `Err` with the code in `x10` into the result, then return. -/
theorem err_exit {s u : MachineState} (hpre : VerifyLayerPre s) (B : Base s u)
    (hpc : u.pc = 0x8000f9cc) (hout : u.getMem (s.getReg .x2 - 1664) = s.getReg .x10)
    (hf : Fails s) : ∃ t, Reaches Image.code u t ∧ Ret s t := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  have hof := hpre.outFree
  obtain ⟨w, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f9cc_spec hpc (by
    rv_eval [B.x2, hout]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have m0 := b8000f9cc_m1 h₁
  rw [B.x2] at m0
  rv_eval [hout] at m0
  have f₁ : MemFrame u w (s.getReg .x10) 16 := h₁.memFrame (by
    rv_eval [B.x2, hout]; and_intros <;> addr_omega [ho])
  have x2w : w.getReg .x2 = s.getReg .x2 - 1712 := (b8000f9cc_keeps h₁ .x2 (by decide)).trans B.x2
  have hN : w.getMem nextAddr = u.getMem nextAddr := f₁ _ (by addr_omega [ho, hof])
  have Bw : Base s w := B.next hpre x2w
    ⟨by simp only [heapNext, hN]; exact B.heap.lo, by simp only [heapNext, hN]; exact B.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) (DFrame.of_memFrame f₁) fun a ha ↦
      ⟨Or.inl (by addr_omega [ha]), by unfold verifyLayerStack at hb hos; addr_omega [ha, hos, hb]⟩
  obtain ⟨t, hr₂, pc, pres, same⟩ := exit hpre (b8000f9cc_pc h₁) Bw.x2 Bw.saved
  exact ⟨t, hr₁.trans hr₂, pc, pres, post_err Bw m0 hf same⟩

/-- After the first check, at `0x8000f294`. -/
structure J3 (s u : MachineState) (pp : Word) (product : List E) : Prop where
  pc : u.pc = 0x8000f294
  base : Base s u
  plenM : u.getMem (s.getReg .x2 - 1672) = 47
  out : u.getMem (s.getReg .x2 - 1664) = s.getReg .x10
  claim : u.getMem (s.getReg .x2 - 1656) = s.getReg .x15
  p : u.getMem (s.getReg .x2 - 1608) = s.getReg .x11
  ppM : u.getMem (s.getReg .x2 - 1600) = pp
  x19 : u.getReg .x19 = s.getReg .x15
  x20 : u.getReg .x20 = s.getReg .x11
  x21 : u.getReg .x21 = pp
  plen : product.length = 47
  prod : eListAt u pp 47 = product
  pbuf : heapNext s ≤ pp.toNat ∧ pp.toNat + 24 * 47 ≤ heapNext u
  rest : Rest s u (stage2 (claimAt s (lClaim s)) product)

set_option maxHeartbeats 8000000 in
theorem check (hM : MulSpec) (hSum : FieldContracts.SumSpec) {s o₀ v : MachineState}
    {sg pp : Word} {product : List E} (hpre : VerifyLayerPre s) (I : I0 s o₀ sg pp product)
    (X : QX s o₀ v (segsOf s) (claimAt s (lClaim s)).weights) (hpc : v.pc = 0x8000f218) :
    ∃ t, Reaches Image.code v t ∧ (J3 s t pp product ∨ Ret s t ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have B := X.base
  have hc := hpre.claim
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hA := hpre.stack.above
  have hnx := hpre.stack.next
  simp only [stackLo] at hA hnx
  unfold verifyLayerStack at hA hb hnx hss
  have mo (a : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 1448) : v.getMem a = o₀.getMem a :=
    X.frame a (scrP_miss hpre (Or.inl ⟨h1, h2⟩))
  have R : Rest s v (TM.require (check1 (shapeOf s) (s.getReg .x14).toNat (claimAt s (lClaim s))
      product) >>= fun _ ↦ stage2 (claimAt s (lClaim s)) product) :=
    I.rest.keep fun T hT ↦ I.ok.base.tat hpre B.heap X.frame (fun a ha ↦ ⟨by
      simp only [ScrP] at ha; rcases ha with ha | ha | ha <;> addr_omega [ha, hb, hS, hss],
      (scrP_lw hpre ha).1⟩) hT
  -- `0x8000f218`: `iota` stored at `f + 264`, `E::sum(mu)` into `f + 960`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f218_spec hpc (by
    rv_eval [B.x2]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b8000f218_keeps h₁
  have f₁ := b8000f218_frame h₁ (by rw [B.x2]; addr_omega [hb])
  rw [B.x2] at f₁
  rv_eval [] at f₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ : Base s t₁ := B.slots hpre x2₁ f₁ (by addr_omega [hb]) (by addr_omega [hb])
  have mp₀ : v.getMem (s.getReg .x2 - 1680) = vecPtr s (lClaim s) := by
    rw [mo _ (by addr_omega [hb]) (by addr_omega [hb]), I.mp]
  have x8v : v.getReg .x8 = vecLen s (lClaim s) := by rw [X.regs .x8 (by decide), I.x8]
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 752 := by rw [b8000f218_x10 h₁, B.x2]; rv_eval []
  have x11₁ : t₁.getReg .x11 = vecPtr s (lClaim s) := by
    rw [b8000f218_x11 h₁, B.x2]; rv_eval [mp₀]
  have x12₁ : t₁.getReg .x12 =
      vecPtr s (lClaim s) + BitVec.ofNat 64 (24 * (vecLen s (lClaim s)).toNat) := by
    rw [b8000f218_x12 h₁, B.x2, x8v, Open.mul24]; rv_eval [mp₀]
  have muR := hpre.mu
  simp only [VecRegion] at muR
  have hsl : FieldContracts.sumLen t₁ = (vecLen s (lClaim s)).toNat := by
    simp only [FieldContracts.sumLen, x11₁, x12₁]
    rcases muR with h0 | hR
    · rw [h0]; simp
    · addr_omega [hR]
  have hsp : FieldContracts.SumPre t₁ := {
    out := by rw [x10₁]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    slice := fun i hi ↦ by
      rw [hsl] at hi
      rw [x11₁]
      rcases muR with h0 | hR
      · rw [h0] at hi; omega
      · exact Region.valid hR (by addr_omega [hR, hi]) (by addr_omega [hR, hi]) (by addr_omega [hR, hi])
    bounds := by
      rw [x11₁, x12₁]
      rcases muR with h0 | hR
      · rw [h0]; simp
      · addr_omega [hR]
    whole := by
      rw [x11₁, x12₁]
      rcases muR with h0 | hR
      · rw [h0]; simp
      · addr_omega [hR] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hSum.call hr₁ (b8000f218_pc h₁) hsp
  swap
  · exact ⟨_, hr₂, Or.inr (Or.inr hd)⟩
  have F₂ := hpost₂.frame
  have V₂ := hpost₂.value
  rw [x10₁] at F₂ V₂
  rw [x11₁, hsl] at V₂
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := (hpres₂.reg .x2).trans x2₁
  have B₂ : Base s t₂ := B₁.slots hpre x2₂ F₂ (by addr_omega [hb]) (by addr_omega [hb])
  have esum : eAt t₂ (s.getReg .x2 - 752) = sumE (claimAt s (lClaim s)).mu := by
    rw [V₂, sumE_eq_sum, B₁.eListAt (missVec B₁.heap hpre.mu hpre.muOut hpre.muSelf hpre.muStack
      hpre.muFree) (by
        rcases muR with h0 | hR
        · exact Or.inl h0
        · exact Or.inr (by addr_omega [hR]))]
    rfl
  have eiota : eAt t₂ (s.getReg .x2 - 1448) =
      iotaAcc (segsOf s) (claimAt s (lClaim s)).weights (s.getReg .x14).toNat 2 := by
    apply eAt_eq_of_limbs
    rw [← X.acc]
    have n0 := b8000f218_m_x2_264 h₁
    have n8 := b8000f218_m_x2_272 h₁
    have n16 := b8000f218_m_x2_280 h₁
    rw [B.x2] at n0 n8 n16
    rv_eval [] at n0 n8 n16
    rv_eval []
    rw [F₂ (s.getReg .x2 - 1448) (by addr_omega [hb]), F₂ (s.getReg .x2 - 1440) (by addr_omega [hb]),
      F₂ (s.getReg .x2 - 1432) (by addr_omega [hb]), n0, n8, n16]
  -- `0x8000f244`: `iota * sum` into `f + 1584`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f244_spec
    (by rw [hpc₂, returnAddress_eq, b8000f218_x1 h₁]; decide) trivial
  have k₃ := b8000f244_keeps h₃
  have hm₃ := b8000f244_mem_same h₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have B₃ : Base s t₃ := B₂.same x2₃ hm₃
  have x10₃ : t₃.getReg .x10 = s.getReg .x2 - 128 := by rw [b8000f244_x10 h₃, x2₂]; rv_eval []
  have x11₃ : t₃.getReg .x11 = s.getReg .x2 - 1448 := by rw [b8000f244_x11 h₃, x2₂]; rv_eval []
  have x12₃ : t₃.getReg .x12 = s.getReg .x2 - 752 := by rw [b8000f244_x12 h₃, x2₂]; rv_eval []
  have hmp : MulPre t₃ := mul_pre hpre x2₃ (B₃.rodata hpre) 128 x10₃ (by decide) (by decide)
    (by decide)
    (by rw [x11₃]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x11₃]; addr_omega [hb])
    (by rw [x10₃, x11₃]; addr_omega [hb])
    (by rw [x12₃]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x12₃]; addr_omega [hb])
    (by rw [x10₃, x12₃]; addr_omega [hb])
  obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hd⟩ := hM.call (hr₂.trans hr₃) (b8000f244_pc h₃) hmp
  swap
  · exact ⟨_, hr₄, Or.inr (Or.inr hd)⟩
  have F₄ := mul_frame x2₃ hpost₄
  rw [x10₃] at F₄
  have v₄ := hpost₄.value
  have e3 (a : Word) : eAt t₃ a = eAt t₂ a := by unfold Rv64Verifier.eAt; rw [hm₃, hm₃, hm₃]
  rw [x10₃, x11₃, x12₃, e3, e3] at v₄
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1712 := (hpres₄.reg .x2).trans x2₃
  have hN₄ : t₄.getMem nextAddr = t₃.getMem nextAddr := F₄ _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hi, hw, hb, hnx]
  have B₄ : Base s t₄ := B₃.next hpre x2₄
    ⟨by simp only [heapNext, hN₄]; exact B₃.heap.lo, by simp only [heapNext, hN₄]; exact B₃.heap.hi⟩
    (by simp only [heapNext, hN₄]; exact le_refl _) F₄ fun a h ↦ by
      refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> rcases h with h | h <;> addr_omega [h, hb]
  -- the frame from `v` on
  have Fst : DFrame v t₄ (Within · (s.getReg .x2 - 2736) 2736) :=
    (((DFrame.of_memFrame f₁).mono fun a h ↦ by addr_omega [h, hb]).trans
      (DFrame.of_memFrame F₂) fun a h ↦ by addr_omega [h, hb]).trans
      ((DFrame.of_same hm₃ _).trans F₄ fun a h ↦ by rcases h with h | h <;> addr_omega [h, hb])
      fun _ h ↦ h
  have keep4 (a : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 1448) : t₄.getMem a = o₀.getMem a := by
    rw [← mo a h1 h2]
    exact ((((DFrame.of_memFrame f₁).mono (w' := fun a ↦ Within a (s.getReg .x2 - 1448) 24 ∨
      Within a (s.getReg .x2 - 752) 24 ∨ Within a (s.getReg .x2 - 128) 24 ∨
      Within a (s.getReg .x2 - 2736) 1024) fun a h ↦ Or.inl h).trans (DFrame.of_memFrame F₂)
      fun a h ↦ Or.inr (Or.inl h)).trans ((DFrame.of_same hm₃ _).trans F₄ fun a h ↦ h)
      fun a h ↦ Or.inr (Or.inr h)) a fun i hi hw ↦ by
        rcases hw with hw | hw | hw | hw <;> addr_omega [hi, hw, h1, h2, hb]
  have cl₄ : t₄.getMem (s.getReg .x2 - 1656) = s.getReg .x15 := by
    rw [keep4 _ (by addr_omega [hb]) (by addr_omega [hb]), I.claim]
  have kc4 (y : Word) (h1 : (lClaim s).toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ (lClaim s).toNat + 96) :
      t₄.getMem y = s.getMem y :=
    B₄.keep (missClaim hpre B₄.heap) (by addr_omega [hc]) h1 h2
  have c72 := kc4 (s.getReg .x15 + 72) (by addr_omega [hc]) (by addr_omega [hc])
  have c80 := kc4 (s.getReg .x15 + 80) (by addr_omega [hc]) (by addr_omega [hc])
  have c88 := kc4 (s.getReg .x15 + 88) (by addr_omega [hc]) (by addr_omega [hc])
  -- the check, on limbs
  have hshape : shapeOf s = ⟨(s.getReg .x12).toNat, 12⟩ := by
    simp only [shapeOf, hpre.depth]; rfl
  have hval : eAt t₄ (s.getReg .x2 - 128) =
      iotaRust (shapeOf s) (s.getReg .x14).toNat (claimAt s (lClaim s)) *
        sumE (claimAt s (lClaim s)).mu := by
    rw [v₄, eiota, esum, hshape, iotaRust_acc]; rfl
  have rg (r : Reg) (hr : r ∈ [Reg.x25, .x26, .x27]) : t₄.getReg r = o₀.getReg r := by
    rw [hpres₄.reg r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide),
      k₃ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide),
      hpres₂.reg r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide),
      k₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide),
      X.regs r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)]
  have hx : limbs (projectedRust (claimAt s (lClaim s)).mu product) =
      (t₄.getReg .x27, t₄.getReg .x26, t₄.getReg .x25) := by
    rw [rg .x27 (by decide), rg .x26 (by decide), rg .x25 (by decide), I.acc]
  have hy : limbs (eAt t₄ (s.getReg .x2 - 128)) =
      (t₄.getMem (s.getReg .x2 - 128), t₄.getMem (s.getReg .x2 - 120),
        t₄.getMem (s.getReg .x2 - 112)) := by
    rw [limbs_eAt]; rv_eval []
  have hz : limbs (claimAt s (lClaim s)).value = (s.getMem (s.getReg .x15 + 72),
      s.getMem (s.getReg .x15 + 80), s.getMem (s.getReg .x15 + 88)) := by
    simp only [claimAt, lClaim]; rw [limbs_eAt]; rv_eval []
  have hC : check1 (shapeOf s) (s.getReg .x14).toNat (claimAt s (lClaim s)) product ↔
      (t₄.getMem (s.getReg .x2 - 128) ^^^ t₄.getReg .x27 = t₄.getMem (s.getReg .x15 + 72) ∧
        t₄.getMem (s.getReg .x2 - 120) ^^^ t₄.getReg .x26 = t₄.getMem (s.getReg .x15 + 80) ∧
        t₄.getMem (s.getReg .x2 - 112) ^^^ t₄.getReg .x25 = t₄.getMem (s.getReg .x15 + 88)) := by
    rw [c72, c80, c88]
    show _ + _ = _ ↔ _
    rw [limbs_sum_eq, ← hval, hy, hz, hx]
  -- the mismatch
  have out₄ : t₄.getMem (s.getReg .x2 - 1664) = s.getReg .x10 := by
    rw [keep4 _ (by addr_omega [hb]) (by addr_omega [hb]), I.out]
  have fail (w : MachineState) (hrw : Reaches Image.code v w) (hw : w.pc = 0x8000f9c8)
      (hmw : ∀ a, w.getMem a = t₄.getMem a) (hx2 : w.getReg .x2 = s.getReg .x2 - 1712)
      (hn : ¬ check1 (shapeOf s) (s.getReg .x14).toNat (claimAt s (lClaim s)) product) :
      ∃ t, Reaches Image.code v t ∧ (J3 s t pp product ∨ Ret s t ∨ Dead Image.code t) := by
    obtain ⟨w', hr', h'⟩ := Sym.BlockSpec.reaches b8000f9c8_spec hw trivial
    have Bw : Base s w' := B₄.same ((b8000f9c8_keeps h' .x2 (by decide)).trans hx2)
      fun a ↦ by rw [b8000f9c8_mem_same h', hmw]
    obtain ⟨t, hr'', ht⟩ := err_exit hpre Bw (b8000f9c8_pc h')
      (by rw [b8000f9c8_mem_same h', hmw, out₄]) (R.require_fail hn)
    exact ⟨t, hrw.trans (hr'.trans hr''), Or.inr (Or.inl ht)⟩
  have hr04 := hr₄
  -- `0x8000f258`, `0x8000f26c`, `0x8000f27c`: the three limbs
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000f258_spec
    (by rw [hpc₄, returnAddress_eq, b8000f244_x1 h₃]; decide) (by
      rv_eval [x2₄, cl₄]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc]))
  have k₅ := b8000f258_keeps h₅
  have hm₅ := b8000f258_mem_same h₅
  have x2₅ : t₅.getReg .x2 = s.getReg .x2 - 1712 := (k₅ .x2 (by decide)).trans x2₄
  by_cases e0 : t₄.getMem (s.getReg .x2 - 128) ^^^ t₄.getReg .x27 = t₄.getMem (s.getReg .x15 + 72)
  swap
  · exact fail t₅ (hr04.trans hr₅) (b8000f258_pc_taken h₅ (by rw [x2₄]; rv_eval [cl₄]; exact e0))
      hm₅ x2₅ fun h ↦ e0 (hC.mp h).1
  have pc₅ := b8000f258_pc_not_taken h₅ (by rw [x2₄]; rv_eval [cl₄]; exact e0)
  have x19₅ : t₅.getReg .x19 = s.getReg .x15 := by rw [b8000f258_x19 h₅, x2₄]; rv_eval [cl₄]
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000f26c_spec pc₅ (by
    rv_eval [x2₅, x19₅]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc]))
  have k₆ := b8000f26c_keeps h₆
  have hm₆ := b8000f26c_mem_same h₆
  have x2₆ : t₆.getReg .x2 = s.getReg .x2 - 1712 := (k₆ .x2 (by decide)).trans x2₅
  have hm46 (a : Word) : t₆.getMem a = t₄.getMem a := by rw [hm₆, hm₅]
  by_cases e1 : t₄.getMem (s.getReg .x2 - 120) ^^^ t₄.getReg .x26 = t₄.getMem (s.getReg .x15 + 80)
  swap
  · exact fail t₆ (hr04.trans (hr₅.trans hr₆)) (b8000f26c_pc_taken h₆ (by
      rw [x2₅, x19₅, k₅ .x26 (by decide)]; rv_eval [hm₅]; exact e1)) hm46 x2₆
      fun h ↦ e1 (hC.mp h).2.1
  have pc₆ := b8000f26c_pc_not_taken h₆ (by rw [x2₅, x19₅, k₅ .x26 (by decide)]; rv_eval [hm₅]; exact e1)
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000f27c_spec pc₆ (by
    rv_eval [x2₆, k₆ .x19 (by decide), x19₅]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc]))
  have k₇ := b8000f27c_keeps h₇
  have hm₇ := b8000f27c_mem_same h₇
  have x2₇ : t₇.getReg .x2 = s.getReg .x2 - 1712 := (k₇ .x2 (by decide)).trans x2₆
  have hm47 (a : Word) : t₇.getMem a = t₄.getMem a := by rw [hm₇, hm46]
  by_cases e2 : t₄.getMem (s.getReg .x2 - 112) ^^^ t₄.getReg .x25 = t₄.getMem (s.getReg .x15 + 88)
  swap
  · exact fail t₇ (hr04.trans (hr₅.trans (hr₆.trans hr₇))) (b8000f27c_pc_taken h₇ (by
      rw [x2₆, k₆ .x19 (by decide), x19₅, k₆ .x25 (by decide), k₅ .x25 (by decide)]
      rv_eval [hm46]; exact e2)) hm47 x2₇ fun h ↦ e2 (hC.mp h).2.2
  have pc₇ := b8000f27c_pc_not_taken h₇ (by
    rw [x2₆, k₆ .x19 (by decide), x19₅, k₆ .x25 (by decide), k₅ .x25 (by decide)]
    rv_eval [hm46]; exact e2)
  -- `0x8000f28c`: the check passed
  obtain ⟨t₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b8000f28c_spec pc₇ (by
    rv_eval [x2₇]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₈ := b8000f28c_keeps h₈
  have hm₈ := b8000f28c_mem_same h₈
  have hm48 (a : Word) : t₈.getMem a = t₄.getMem a := by rw [hm₈, hm47]
  have x2₈ : t₈.getReg .x2 = s.getReg .x2 - 1712 := (k₈ .x2 (by decide)).trans x2₇
  have B₈ : Base s t₈ := B₄.same x2₈ hm48
  have F48 : DFrame v t₈ (Within · (s.getReg .x2 - 2736) 2736) :=
    Fst.trans (DFrame.of_same hm48 _) fun _ h ↦ h
  have Fo8 : DFrame o₀ t₈ (Within · (s.getReg .x2 - 2736) 2736) :=
    (X.frame.mono fun a h ↦ by
      simp only [ScrP] at h; rcases h with h | h | h <;> addr_omega [h, hb]).trans F48 fun _ h ↦ h
  have hN8 : heapNext t₈ = heapNext o₀ := by
    simp only [heapNext]; rw [Fo8 nextAddr fun i hi hw ↦ by addr_omega [hi, hw, hb, hnx]]
  have s48 (a : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 1448) : t₈.getMem a = o₀.getMem a := by
    rw [hm48, keep4 a h1 h2]
  refine ⟨t₈, hr04.trans (hr₅.trans (hr₆.trans (hr₇.trans hr₈))), Or.inl {
    pc := b8000f28c_pc h₈
    base := B₈
    plenM := by rw [s48 _ (by addr_omega [hb]) (by addr_omega [hb]), I.plenM]
    out := by rw [s48 _ (by addr_omega [hb]) (by addr_omega [hb]), I.out]
    claim := by rw [s48 _ (by addr_omega [hb]) (by addr_omega [hb]), I.claim]
    p := by rw [s48 _ (by addr_omega [hb]) (by addr_omega [hb]), I.p]
    ppM := by rw [s48 _ (by addr_omega [hb]) (by addr_omega [hb]), I.ppM]
    x19 := by rw [k₈ .x19 (by decide), k₇ .x19 (by decide), k₆ .x19 (by decide), x19₅]
    x20 := by
      rw [b8000f28c_x20 h₈, x2₇]; rv_eval [hm47]
      rw [keep4 _ (by addr_omega [hb]) (by addr_omega [hb]), I.p]
    x21 := by
      rw [b8000f28c_x21 h₈, x2₇]; rv_eval [hm47]
      rw [keep4 _ (by addr_omega [hb]) (by addr_omega [hb]), I.ppM]
    plen := I.plen
    prod := by
      rw [← I.prod]
      have hpb := I.pbuf
      have hHo := I.ok.base.heap.hi
      exact Fo8.eListAt fun i hi hw ↦ by addr_omega [hi, hw, hpb, hHo, hb, hA]
    pbuf := ⟨I.pbuf.1, by rw [hN8]; exact I.pbuf.2⟩
    rest := (R.require_pass (hC.mpr ⟨e0, e1, e2⟩)).keep fun T hT ↦
      B.tat hpre B₈.heap F48 (fun a ha ↦ bodyW_tat hpre B B₈.heap (stk_body hpre ha)) hT }⟩

end Rv64Verifier.Gkr.Layer
