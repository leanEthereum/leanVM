import Rv64Verifier.Proofs.Gkr.LayerCheck

/-!
# `keccak::verify_layer`: the instance weights' challenge and its powers

`keccak.rs:103-108` and `:147`, inlined at `0x8000f294..0x8000f420`: the sponge duplexed and `s`
read from its state into `f + 888` (`sample_s`), then `powers = [ONE; EMBED_BITS]` at `f + 960`
and `powers[b] = powers[b - 1] * s` (`pow_loop`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript
  Rv64Verifier.Contracts Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem challengeOf_stateAt (u : MachineState) (a : Word) :
    challengeOf (stateAt u a) = eAt u a := by
  simp only [challengeOf, lane_stateAt u a (by decide : 0 < 25),
    lane_stateAt u a (by decide : 1 < 25), lane_stateAt u a (by decide : 2 < 25), Nat.mul_zero,
    Nat.mul_one, Nat.reduceMul, add_ofNat_zero]
  rfl

/-- A call of `Sponge::duplex` on the transcript's sponge: what the transcript stands for has its
sponge permuted. -/
theorem duplexCall (hD : DuplexSpec) {s u₀ u : MachineState} (hpre : VerifyLayerPre s)
    (B : Base s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x80007cd8)
    (h10 : u.getReg .x10 = s.getReg .x11 + 8) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Base s v ∧
      DFrame u v (fun a ↦ Within a (s.getReg .x11 + 8) 336 ∨
        Within a (s.getReg .x2 - 2592) duplexStack) ∧
      ∀ T, TranscriptAt u (s.getReg .x11) T →
        TranscriptAt v (s.getReg .x11) { T with sponge := spDuplex T.sponge }) ∨
      Dead Image.code v) := by
  have hb := bounds hpre
  have hS := hpre.self.self
  have ss := hpre.selfStack
  have sr := hpre.selfRodata
  have hx := hpre.stack.next
  have hsf := hpre.selfFree
  unfold verifyLayerStack at hb ss hx
  have hsl : stackLo u duplexStack = s.getReg .x2 - 2592 := by
    simp only [stackLo, B.x2]; apply BitVec.eq_of_toNat_eq; addr_omega [hb]
  have pre : DuplexPre u := {
    sponge := by rw [h10]; addr_omega [hS]
    stack := hpre.stack.sub 1712 B.x2 (by unfold verifyLayerStack; decide) (by decide) (by decide)
      (by decide) (by decide)
    spongeStack := by rw [h10, hsl]; addr_omega [hS, ss, hb]
    rodata := B.rodata hpre
    spongeRodata := by rw [h10]; addr_omega [sr, hS] }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hD.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have fr := post.frame
  rw [h10, hsl] at fr
  have hval := post.value
  rw [h10] at hval
  have hN : v.getMem nextAddr = u.getMem nextAddr := fr _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hx, hw, hi, hb, hS, hsf.2]
  have Bv : Base s v := B.next hpre ((hp.reg .x2).trans B.x2)
    ⟨by simp only [heapNext, hN]; exact B.heap.lo, by simp only [heapNext, hN]; exact B.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) fr fun a ha ↦ by
      rcases ha with ha | ha
      · exact ⟨Or.inr (Or.inl (by addr_omega [ha, hS])), by addr_omega [ha, hS, ss, hb]⟩
      · exact ⟨Or.inr (Or.inr (Or.inl (by unfold verifyLayerStack; addr_omega [ha, hb]))),
          by addr_omega [ha, hb]⟩
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, Bv, fr, fun T hT ↦ ?_⟩⟩
  have hpS := hpre.proofStack
  have hA := hpre.self.apart
  unfold verifyLayerStack at hpS
  simp only [ProofApart] at hpS hA
  obtain ⟨e0, e1, e2⟩ := B.reads hpre
  have kept (y : Word) (hy : ∀ i < 8, ¬ (Within (y + BitVec.ofNat 64 i) (s.getReg .x11 + 8) 336 ∨
      Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 2592) duplexStack)) : v.getMem y = u.getMem y :=
    fr y hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hT.stream]
    refine fr.eListAt_stream (fun i hi hw ↦ ?_) (fun i hi hw ↦ ?_) (fun i hi hw ↦ ?_)
    · rcases hw with hw | hw <;> addr_omega [hw, hi, hS, ss, hb]
    · rw [e0] at hw
      rcases hw with hw | hw <;> addr_omega [hw, hi, hA.1, hpS.1, hb, hpre.self.proof]
    · rw [e1] at hw
      rw [e2] at hi
      rcases hpre.self.stream with h0 | h0
      · omega
      rcases hw with hw | hw <;> addr_omega [hw, hi, hA.2, hpS.2, hb, h0]
  · rw [hval, hT.sponge]
  · rw [← hT.streamOffset, kept _ fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hS, ss, hb]]
  · rw [← hT.openingOffset, kept _ fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hS, ss, hb]]

/-! ## The powers -/

/-- What the powers loop writes: `mul`'s result and stack, the powers. -/
@[rv_addr] def PwW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1448) 24 ∨ Within a (s.getReg .x2 - 2736) 1024 ∨
    Within a (s.getReg .x2 - 752) 576

/-- The powers loop at its head `0x8000f3e8` after `k` products. -/
structure PW (s w₀ w : MachineState) (c : E) (k : Nat) : Prop where
  base : Base s w
  regs : ∀ r ∈ [Reg.x2, .x8, .x19, .x20, .x21], w.getReg r = w₀.getReg r
  x9 : w.getReg .x9 = s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * k)
  pow : ∀ i < 24, eAt w (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) =
    if i ≤ k then c ^ i else 1
  sc : eAt w (s.getReg .x2 - 824) = c
  lt : k < 23
  frame : DFrame w₀ w (PwW s)

/-- The powers done, at `0x8000f420`. -/
structure PWX (s w₀ w : MachineState) (c : E) : Prop where
  base : Base s w
  regs : ∀ r ∈ [Reg.x2, .x8, .x19, .x20, .x21], w.getReg r = w₀.getReg r
  pow : ∀ i < 24, eAt w (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) = c ^ i
  sc : eAt w (s.getReg .x2 - 824) = c
  frame : DFrame w₀ w (PwW s)

theorem step24 (b : Word) (k d : Nat) : b + BitVec.ofNat 64 (24 * (k + 1)) + BitVec.ofNat 64 d =
    b + BitVec.ofNat 64 (24 * k) + BitVec.ofNat 64 (24 + d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 4000000 in
theorem pow_step (hM : MulSpec) {s w₀ w : MachineState} {c : E} {k : Nat}
    (hpre : VerifyLayerPre s) (hx8 : w₀.getReg .x8 = s.getReg .x2 - 200) (Q : PW s w₀ w c k)
    (hpc : w.pc = 0x8000f3e8) :
    ∃ v, Reaches Image.code w v ∧ ((PW s w₀ v c (k + 1) ∧ v.pc = 0x8000f3e8) ∨
      (PWX s w₀ v c ∧ v.pc = 0x8000f420) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := Q.base
  have hk := Q.lt
  have hnx := hpre.stack.next
  unfold verifyLayerStack at hb hnx
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f3e8_spec hpc trivial
  have k₁ := b8000f3e8_keeps h₁
  have hm₁ := b8000f3e8_mem_same h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ : Base s u₁ := B.same x2₁ hm₁
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 1448 := by rw [b8000f3e8_x10 h₁, B.x2]; rv_eval []
  have x11₁ : u₁.getReg .x11 = s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * k) := by
    rw [b8000f3e8_x11 h₁, Q.x9]
  have x12₁ : u₁.getReg .x12 = s.getReg .x2 - 824 := by rw [b8000f3e8_x12 h₁, B.x2]; rv_eval []
  have hmp : MulPre u₁ := mul_pre hpre x2₁ (B₁.rodata hpre) 1448 x10₁ (by decide) (by decide)
    (by decide)
    (by rw [x11₁]; valid_sub hpre.stack.valid [hb, hk])
    (by rw [x11₁]; addr_omega [hb, hk])
    (by rw [x10₁, x11₁]; addr_omega [hb, hk])
    (by rw [x12₁]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x12₁]; addr_omega [hb])
    (by rw [x10₁, x12₁]; addr_omega [hb])
  obtain ⟨u₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hM.call hr₁ (b8000f3e8_pc h₁) hmp
  swap
  · exact ⟨_, hr₂, Or.inr (Or.inr hd)⟩
  have F₂ := mul_frame x2₁ hpost₂
  rw [x10₁] at F₂
  have v₂ := hpost₂.value
  have e1 (a : Word) : eAt u₁ a = eAt w a := by unfold Rv64Verifier.eAt; rw [hm₁, hm₁, hm₁]
  rw [x10₁, x11₁, x12₁, e1, e1, Q.sc, Q.pow k (by omega), ite_eq_left (le_refl k)] at v₂
  have x2₂ : u₂.getReg .x2 = s.getReg .x2 - 1712 := (hpres₂.reg .x2).trans x2₁
  have hN₂ : u₂.getMem nextAddr = u₁.getMem nextAddr := F₂ _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hi, hw, hb, hnx]
  have B₂ : Base s u₂ := B₁.next hpre x2₂
    ⟨by simp only [heapNext, hN₂]; exact B₁.heap.lo, by simp only [heapNext, hN₂]; exact B₁.heap.hi⟩
    (by simp only [heapNext, hN₂]; exact le_refl _) F₂ fun a h ↦ by
      refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> rcases h with h | h <;> addr_omega [h, hb]
  have x9₂ : u₂.getReg .x9 = s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * k) := by
    rw [hpres₂.reg .x9, k₁ .x9 (by decide), Q.x9]
  -- `0x8000f400`: the product stored, the next power
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f400_spec
    (by rw [hpc₂, returnAddress_eq, b8000f3e8_x1 h₁]; decide) (by
      rv_eval [x2₂, x9₂]; and_intros <;> valid_access hpre.stack.valid [hb, hk])
  have k₃ := b8000f400_keeps h₃
  have f₃ := b8000f400_frame h₃ (by rw [x9₂]; addr_omega [hb, hk])
  rw [x9₂] at f₃
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have B₃ : Base s u₃ := B₂.slots hpre x2₃ f₃ (by addr_omega [hb, hk]) (by addr_omega [hb, hk])
  have ea : s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * k) + 24 =
      s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * (k + 1)) := ofNat_step0 _ 24 k
  have m24 := b8000f400_m_x9_24 h₃
  have m32 := b8000f400_m_x9_32 h₃
  have m40 := b8000f400_m_x9_40 h₃
  rw [x9₂, x2₂] at m24 m32 m40
  rv_eval [] at m24 m32 m40
  have enew : eAt u₃ (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * (k + 1))) = c ^ (k + 1) := by
    rw [pow_succ, ← v₂]
    apply eAt_congr
    · rw [← ea]; exact m24
    · rv_eval []
      rw [show s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * (k + 1)) + 8 =
        s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * k) + 32 from step24 _ k 8]
      exact m32
    · rv_eval []
      rw [show s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * (k + 1)) + 16 =
        s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * k) + 40 from step24 _ k 16]
      exact m40
  have Fw3 : DFrame w u₃ (PwW s) :=
    ((DFrame.of_same hm₁ _).trans F₂ fun a h ↦ by
      simp only [PwW]; rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)).trans (DFrame.of_memFrame f₃) fun a h ↦ by
        simp only [PwW]; exact Or.inr (Or.inr (by addr_omega [h, hb, hk]))
  have hnot (i : Nat) (hi : i < 24) (hne : i ≠ k + 1) :
      eAt u₃ (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) =
        eAt w (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) := by
    rw [f₃.eAt (by addr_omega [hb, hk, hi, hne]) (by addr_omega [hb, hi]),
      F₂.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb, hi], e1]
  have sc₃ : eAt u₃ (s.getReg .x2 - 824) = c := by
    rw [f₃.eAt (by addr_omega [hb, hk]) (by addr_omega [hb]),
      F₂.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb], e1, Q.sc]
  have x18₂ : u₂.getReg .x18 = s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * (k + 1)) := by
    rw [hpres₂.reg .x18, b8000f3e8_x18 h₁, Q.x9, ea]
  have x8₂ : u₂.getReg .x8 = s.getReg .x2 - 200 := by
    rw [hpres₂.reg .x8, k₁ .x8 (by decide), Q.regs .x8 (by decide), hx8]
  have x9₃ : u₃.getReg .x9 = s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * (k + 1)) := by
    rw [b8000f400_x9 h₃, x18₂]
  have regs₃ (r : Reg) (hr : r ∈ [Reg.x2, .x8, .x19, .x20, .x21]) : u₃.getReg r = w₀.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hpres₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _), Q.regs r hr]
  have Pw (i : Nat) (hi : i < 24) : eAt u₃ (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) =
      if i ≤ k + 1 then c ^ i else 1 := by
    by_cases hik : i = k + 1
    · subst hik; rw [enew, ite_eq_left (le_refl _)]
    · rw [hnot i hi hik, Q.pow i hi]
      by_cases h' : i ≤ k
      · rw [ite_eq_left h', ite_eq_left (by omega)]
      · rw [ite_eq_right h', ite_eq_right (by omega)]
  by_cases hl : k + 1 < 23
  · refine ⟨u₃, hr₂.trans hr₃, Or.inl ⟨{
      base := B₃
      regs := regs₃
      x9 := x9₃
      pow := Pw
      sc := sc₃
      lt := hl
      frame := Q.frame.trans Fw3 fun _ h ↦ h }, b8000f400_pc_taken h₃ ?_⟩⟩
    rw [x18₂, x8₂]; addr_omega [hb, hl]
  · refine ⟨u₃, hr₂.trans hr₃, Or.inr (Or.inl ⟨{
      base := B₃
      regs := regs₃
      pow := fun i hi ↦ by rw [Pw i hi, ite_eq_left (by omega)]
      sc := sc₃
      frame := Q.frame.trans Fw3 fun _ h ↦ h }, b8000f400_pc_not_taken h₃ ?_⟩)⟩
    rw [x18₂, x8₂]; addr_omega [hb, hl, hk]

theorem pow_loop (hM : MulSpec) {s w₀ : MachineState} {c : E} (hpre : VerifyLayerPre s)
    (hx8 : w₀.getReg .x8 = s.getReg .x2 - 200) :
    ∀ n k w, k + n = 23 → PW s w₀ w c k → w.pc = 0x8000f3e8 →
      ∃ v, Reaches Image.code w v ∧ ((PWX s w₀ v c ∧ v.pc = 0x8000f420) ∨ Dead Image.code v)
  | 0, k, w, hn, Q, _ => absurd Q.lt (by omega)
  | n + 1, k, w, hn, Q, hpc => by
    obtain ⟨v, hr, ⟨Q', hpc'⟩ | ⟨X, hpc'⟩ | hd⟩ := pow_step hM hpre hx8 Q hpc
    · obtain ⟨t, hr', ht⟩ := pow_loop hM hpre hx8 n (k + 1) v (by omega) Q' hpc'
      exact ⟨t, hr.trans hr', ht⟩
    · exact ⟨v, hr, Or.inl ⟨X, hpc'⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

/-! ## The challenge -/

/-- The powers computed, at `0x8000f420`. -/
structure J5 (s u : MachineState) (pp : Word) (product : List E) (c : E) : Prop where
  pc : u.pc = 0x8000f420
  base : Base s u
  plenM : u.getMem (s.getReg .x2 - 1672) = 47
  out : u.getMem (s.getReg .x2 - 1664) = s.getReg .x10
  claim : u.getMem (s.getReg .x2 - 1656) = s.getReg .x15
  sponge : u.getMem (s.getReg .x2 - 1616) = s.getReg .x11 + 8
  p : u.getMem (s.getReg .x2 - 1608) = s.getReg .x11
  ppM : u.getMem (s.getReg .x2 - 1600) = pp
  x19 : u.getReg .x19 = s.getReg .x15
  x20 : u.getReg .x20 = s.getReg .x11
  x21 : u.getReg .x21 = pp
  pow : ∀ i < 24, eAt u (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) = c ^ i
  sc : eAt u (s.getReg .x2 - 824) = c
  plen : product.length = 47
  prod : eListAt u pp 47 = product
  pbuf : heapNext s ≤ pp.toNat ∧ pp.toNat + 24 * 47 ≤ heapNext u
  rest : Rest s u (packRest (claimAt s (lClaim s)) (instanceWeightsRust c)
    (sumE (instanceWeightsRust c)) 0 (polyEvalRust product c, 1, []))

set_option maxHeartbeats 16000000 in
theorem powers (hD : DuplexSpec) (hM : MulSpec) {s u : MachineState} {pp : Word}
    {product : List E} (hpre : VerifyLayerPre s) (J : J3 s u pp product) :
    ∃ v c, Reaches Image.code u v ∧ (J5 s v pp product c ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := J.base
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hnx := hpre.stack.next
  have hA := hpre.stack.above
  simp only [stackLo] at hA hnx hss
  unfold verifyLayerStack at hb hnx hA hss
  -- `0x8000f294`: the sponge's address saved, `duplex`
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000f294_spec J.pc (by
    rv_eval [B.x2]; valid_access hpre.stack.valid [hb])
  have k₀ := b8000f294_keeps h₀
  have f₀ := b8000f294_frame h₀ (by rw [B.x2]; addr_omega [hb])
  rw [B.x2] at f₀
  rv_eval [] at f₀
  have x2₀ : t₀.getReg .x2 = s.getReg .x2 - 1712 := (k₀ .x2 (by decide)).trans B.x2
  have B₀ : Base s t₀ := B.slots hpre x2₀ f₀ (by addr_omega [hb]) (by addr_omega [hb])
  have m96 := b8000f294_m_x2_96 h₀
  rw [B.x2, J.x20] at m96
  rv_eval [] at m96
  obtain ⟨v₁, hr₁, ⟨hpc₁, hpres₁, B₁, F₁, tr₁⟩ | hd⟩ := duplexCall hD hpre B₀ hr₀
    (b8000f294_pc h₀) (by rw [b8000f294_x10 h₀, J.x20])
  swap
  · exact ⟨_, 0, hr₁, Or.inr hd⟩
  have x2v : v₁.getReg .x2 = s.getReg .x2 - 1712 := (hpres₁.reg .x2).trans x2₀
  have x20v : v₁.getReg .x20 = s.getReg .x11 := by
    rw [hpres₁.reg .x20, k₀ .x20 (by decide), J.x20]
  -- `0x8000f2a4`: `s` from the state, `powers = [ONE; 24]`
  obtain ⟨w₀, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f2a4_spec
    (by rw [hpc₁, returnAddress_eq, b8000f294_x1 h₀]; decide) (by
      rv_eval [x2v, x20v]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid hS ?_ ?_ ?_ <;> addr_omega [hS]))
  have k₂ := b8000f2a4_keeps h₂
  have f₂ := b8000f2a4_frame h₂ (by rw [x2v]; addr_omega [hb])
  rw [x2v] at f₂
  rv_eval [] at f₂
  have x2w : w₀.getReg .x2 = s.getReg .x2 - 1712 := (k₂ .x2 (by decide)).trans x2v
  have Bw : Base s w₀ := B₁.slots hpre x2w f₂ (by addr_omega [hb]) (by addr_omega [hb])
  have n888 := b8000f2a4_m_x2_888 h₂
  have n896 := b8000f2a4_m_x2_896 h₂
  have n904 := b8000f2a4_m_x2_904 h₂
  rw [x2v, x20v] at n888 n896 n904
  rv_eval [] at n888 n896 n904
  have n960 := b8000f2a4_m_x2_960 h₂
  have n968 := b8000f2a4_m_x2_968 h₂
  have n976 := b8000f2a4_m_x2_976 h₂
  have n984 := b8000f2a4_m_x2_984 h₂
  have n992 := b8000f2a4_m_x2_992 h₂
  have n1000 := b8000f2a4_m_x2_1000 h₂
  have n1008 := b8000f2a4_m_x2_1008 h₂
  have n1016 := b8000f2a4_m_x2_1016 h₂
  have n1024 := b8000f2a4_m_x2_1024 h₂
  have n1032 := b8000f2a4_m_x2_1032 h₂
  have n1040 := b8000f2a4_m_x2_1040 h₂
  have n1048 := b8000f2a4_m_x2_1048 h₂
  have n1056 := b8000f2a4_m_x2_1056 h₂
  have n1064 := b8000f2a4_m_x2_1064 h₂
  have n1072 := b8000f2a4_m_x2_1072 h₂
  have n1080 := b8000f2a4_m_x2_1080 h₂
  have n1088 := b8000f2a4_m_x2_1088 h₂
  have n1096 := b8000f2a4_m_x2_1096 h₂
  have n1104 := b8000f2a4_m_x2_1104 h₂
  have n1112 := b8000f2a4_m_x2_1112 h₂
  have n1120 := b8000f2a4_m_x2_1120 h₂
  have n1128 := b8000f2a4_m_x2_1128 h₂
  have n1136 := b8000f2a4_m_x2_1136 h₂
  have n1144 := b8000f2a4_m_x2_1144 h₂
  have n1152 := b8000f2a4_m_x2_1152 h₂
  have n1160 := b8000f2a4_m_x2_1160 h₂
  have n1168 := b8000f2a4_m_x2_1168 h₂
  have n1176 := b8000f2a4_m_x2_1176 h₂
  have n1184 := b8000f2a4_m_x2_1184 h₂
  have n1192 := b8000f2a4_m_x2_1192 h₂
  have n1200 := b8000f2a4_m_x2_1200 h₂
  have n1208 := b8000f2a4_m_x2_1208 h₂
  have n1216 := b8000f2a4_m_x2_1216 h₂
  have n1224 := b8000f2a4_m_x2_1224 h₂
  have n1232 := b8000f2a4_m_x2_1232 h₂
  have n1240 := b8000f2a4_m_x2_1240 h₂
  have n1248 := b8000f2a4_m_x2_1248 h₂
  have n1256 := b8000f2a4_m_x2_1256 h₂
  have n1264 := b8000f2a4_m_x2_1264 h₂
  have n1272 := b8000f2a4_m_x2_1272 h₂
  have n1280 := b8000f2a4_m_x2_1280 h₂
  have n1288 := b8000f2a4_m_x2_1288 h₂
  have n1296 := b8000f2a4_m_x2_1296 h₂
  have n1304 := b8000f2a4_m_x2_1304 h₂
  have n1312 := b8000f2a4_m_x2_1312 h₂
  have n1320 := b8000f2a4_m_x2_1320 h₂
  have n1328 := b8000f2a4_m_x2_1328 h₂
  have n1336 := b8000f2a4_m_x2_1336 h₂
  have n1344 := b8000f2a4_m_x2_1344 h₂
  have n1352 := b8000f2a4_m_x2_1352 h₂
  have n1360 := b8000f2a4_m_x2_1360 h₂
  have n1368 := b8000f2a4_m_x2_1368 h₂
  have n1376 := b8000f2a4_m_x2_1376 h₂
  have n1384 := b8000f2a4_m_x2_1384 h₂
  have n1392 := b8000f2a4_m_x2_1392 h₂
  have n1400 := b8000f2a4_m_x2_1400 h₂
  have n1408 := b8000f2a4_m_x2_1408 h₂
  have n1416 := b8000f2a4_m_x2_1416 h₂
  have n1424 := b8000f2a4_m_x2_1424 h₂
  have n1432 := b8000f2a4_m_x2_1432 h₂
  have n1440 := b8000f2a4_m_x2_1440 h₂
  have n1448 := b8000f2a4_m_x2_1448 h₂
  have n1456 := b8000f2a4_m_x2_1456 h₂
  have n1464 := b8000f2a4_m_x2_1464 h₂
  have n1472 := b8000f2a4_m_x2_1472 h₂
  have n1480 := b8000f2a4_m_x2_1480 h₂
  have n1488 := b8000f2a4_m_x2_1488 h₂
  have n1496 := b8000f2a4_m_x2_1496 h₂
  have n1504 := b8000f2a4_m_x2_1504 h₂
  have n1512 := b8000f2a4_m_x2_1512 h₂
  have n1520 := b8000f2a4_m_x2_1520 h₂
  have n1528 := b8000f2a4_m_x2_1528 h₂
  rw [x2v] at n960 n968 n976 n984 n992 n1000 n1008 n1016 n1024 n1032 n1040 n1048 n1056 n1064 n1072 n1080 n1088 n1096 n1104 n1112 n1120 n1128 n1136 n1144 n1152 n1160 n1168 n1176 n1184 n1192 n1200 n1208 n1216 n1224 n1232 n1240 n1248 n1256 n1264 n1272 n1280 n1288 n1296 n1304 n1312 n1320 n1328 n1336 n1344 n1352 n1360 n1368 n1376 n1384 n1392 n1400 n1408 n1416 n1424 n1432 n1440 n1448 n1456 n1464 n1472 n1480 n1488 n1496 n1504 n1512 n1520 n1528
  rv_eval [] at n960 n968 n976 n984 n992 n1000 n1008 n1016 n1024 n1032 n1040 n1048 n1056 n1064 n1072 n1080 n1088 n1096 n1104 n1112 n1120 n1128 n1136 n1144 n1152 n1160 n1168 n1176 n1184 n1192 n1200 n1208 n1216 n1224 n1232 n1240 n1248 n1256 n1264 n1272 n1280 n1288 n1296 n1304 n1312 n1320 n1328 n1336 n1344 n1352 n1360 n1368 n1376 n1384 n1392 n1400 n1408 n1416 n1424 n1432 n1440 n1448 n1456 n1464 n1472 n1480 n1488 n1496 n1504 n1512 n1520 n1528
  have one (i : Nat) (hi : i < 24) :
      eAt w₀ (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) = 1 := by
    apply eAt_eq_of_limbs
    rw [limbs_one]
    interval_cases i <;> (simp only [Nat.reduceMul]; rv_eval [n960, n968, n976, n984, n992, n1000, n1008, n1016, n1024, n1032, n1040, n1048, n1056, n1064, n1072, n1080, n1088, n1096, n1104, n1112, n1120, n1128, n1136, n1144, n1152, n1160, n1168, n1176, n1184, n1192, n1200, n1208, n1216, n1224, n1232, n1240, n1248, n1256, n1264, n1272, n1280, n1288, n1296, n1304, n1312, n1320, n1328, n1336, n1344, n1352, n1360, n1368, n1376, n1384, n1392, n1400, n1408, n1416, n1424, n1432, n1440, n1448, n1456, n1464, n1472, n1480, n1488, n1496, n1504, n1512, n1520, n1528])
  -- the transcript and the mirror
  have R₀ : Rest s t₀ (TM.sample >>= fun x ↦ packRest (claimAt s (lClaim s))
      (instanceWeightsRust x) (sumE (instanceWeightsRust x)) 0 (polyEvalRust product x, 1, [])) :=
    J.rest.keep fun T hT ↦ B.slots_tat hpre B₀ f₀ (by addr_omega [hb]) (by addr_omega [hb]) hT
  have R₁ : Rest s w₀ (packRest (claimAt s (lClaim s)) (instanceWeightsRust (eAt w₀ (s.getReg .x2 - 824)))
      (sumE (instanceWeightsRust (eAt w₀ (s.getReg .x2 - 824)))) 0
      (polyEvalRust product (eAt w₀ (s.getReg .x2 - 824)), 1, [])) := R₀.step fun T hT ↦ by
    have h1 := tr₁ T hT
    refine ⟨{ T with sponge := spDuplex T.sponge }, ?_,
      B₁.slots_tat hpre Bw f₂ (by addr_omega [hb]) (by addr_omega [hb]) h1⟩
    have hs : spongeAt v₁ (s.getReg .x11 + 8) = spDuplex T.sponge := h1.sponge
    have e1 : (spSqueeze T.sponge).2 = spDuplex T.sponge := rfl
    have e2 : (spSqueeze T.sponge).1 = challengeOf (spDuplex T.sponge).state := rfl
    have hce : challengeOf (spDuplex T.sponge).state = eAt w₀ (s.getReg .x2 - 824) := by
      rw [← hs]
      show challengeOf (stateAt v₁ (s.getReg .x11 + 8 + 128)) = _
      rw [challengeOf_stateAt]
      symm
      apply eAt_congr <;> rv_eval [n888, n896, n904]
    show some ((spSqueeze T.sponge).1, { T with sponge := (spSqueeze T.sponge).2 }) = _
    rw [e1, e2, hce]
  -- the powers loop
  have P₀ : PW s w₀ w₀ (eAt w₀ (s.getReg .x2 - 824)) 0 := {
    base := Bw
    regs := fun _ _ ↦ rfl
    x9 := by
      rw [b8000f2a4_x9 h₂, x2v, show BitVec.ofNat 64 (24 * 0) = 0 from rfl, Sym.add_zero_lit]
      rv_eval []
    pow := fun i hi ↦ by
      rw [one i hi]
      by_cases h0 : i ≤ 0
      · rw [ite_eq_left h0, show i = 0 by omega, pow_zero]
      · rw [ite_eq_right h0]
    sc := rfl
    lt := by decide
    frame := DFrame.refl _ _ }
  have hx8 : w₀.getReg .x8 = s.getReg .x2 - 200 := by rw [b8000f2a4_x8 h₂, x2v]; rv_eval []
  obtain ⟨v, hr₃, ⟨X, hpc₃⟩ | hd⟩ :=
    pow_loop hM hpre hx8 23 0 w₀ (by decide) P₀ (b8000f2a4_pc h₂)
  swap
  · exact ⟨v, 0, hr₁.trans (hr₂.trans hr₃), Or.inr hd⟩
  -- what the stretch kept
  have keepS (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1616 ∨
        (s.getReg .x2).toNat - 1608 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 1448) :
      v.getMem y = u.getMem y := by
    rw [X.frame y fun i hi hw ↦ by
        simp only [PwW] at hw; rcases hw with hw | hw | hw <;> addr_omega [hw, hi, h1, h2, hb],
      f₂ y (by addr_omega [h1, h2, hb]),
      F₁ y fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, h1, h2, hb, hS, hss],
      f₀ y (by addr_omega [h1, h2, hb])]
  have regsv (r : Reg) (hr : r ∈ [Reg.x19, .x20, .x21]) : v.getReg r = u.getReg r := by
    rw [X.regs r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), hpres₁ r (mem_of_mem hr _),
      k₀ r (mem_of_mem hr _)]
  have hpb := J.pbuf
  have hHu := B.heap.hi
  have hHs := hpre.heap.lo
  have missP (y : Word) (h1 : pp.toNat ≤ y.toNat) (h2 : y.toNat < pp.toNat + 24 * 47) :
      ¬ Within y (s.getReg .x11 + 8) 336 ∧ ¬ Within y (s.getReg .x2 - 2736) 2736 := by
    have := hsf.1
    constructor
    · rcases this with h | h <;> addr_omega [h, h1, h2, hpb, hHu, hS]
    · addr_omega [h1, h2, hpb, hHu, hb, hA]
  have Fuv : DFrame u v fun a ↦ Within a (s.getReg .x11 + 8) 336 ∨
      Within a (s.getReg .x2 - 2736) 2736 :=
    ((((DFrame.of_memFrame f₀).mono fun a h ↦ Or.inr (by addr_omega [h, hb])).trans F₁
      fun a h ↦ h.elim Or.inl fun h ↦ Or.inr (by addr_omega [h, hb])).trans (DFrame.of_memFrame f₂)
      fun a h ↦ Or.inr (by addr_omega [h, hb])).trans X.frame fun a h ↦ by
        simp only [PwW] at h; exact Or.inr (by rcases h with h | h | h <;> addr_omega [h, hb])
  have hNv : v.getMem nextAddr = u.getMem nextAddr := Fuv _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hnx, hS, hsf.2]
  refine ⟨v, eAt w₀ (s.getReg .x2 - 824), hr₁.trans (hr₂.trans hr₃), Or.inl {
    pc := hpc₃
    base := X.base
    plenM := by rw [keepS _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), J.plenM]
    out := by rw [keepS _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), J.out]
    claim := by rw [keepS _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), J.claim]
    sponge := by
      rw [X.frame _ fun i hi hw ↦ by
          simp only [PwW] at hw; rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb],
        f₂ _ (by addr_omega [hb]),
        F₁ _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hS, hss], m96]
    p := by
      rw [keepS _ (by addr_omega [hb]) (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩), J.p]
    ppM := by
      rw [keepS _ (by addr_omega [hb]) (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩), J.ppM]
    x19 := by rw [regsv .x19 (by decide), J.x19]
    x20 := by rw [regsv .x20 (by decide), J.x20]
    x21 := by rw [regsv .x21 (by decide), J.x21]
    pow := X.pow
    sc := X.sc
    plen := J.plen
    prod := by
      rw [← J.prod]
      exact Fuv.eListAt fun i hi hw ↦ by
        obtain ⟨m1, m2⟩ := missP (pp + BitVec.ofNat 64 i) (by addr_omega [hi, hpb, hHu])
          (by addr_omega [hi, hpb, hHu])
        rcases hw with hw | hw
        · exact m1 hw
        · exact m2 hw
    pbuf := ⟨hpb.1, by simp only [heapNext, hNv]; exact hpb.2⟩
    rest := R₁.keep fun T hT ↦ Bw.tat hpre X.base.heap X.frame (fun a ha ↦ by
      simp only [PwW] at ha
      exact bodyW_tat hpre Bw X.base.heap (Or.inl (by
        unfold verifyLayerStack; rcases ha with ha | ha | ha <;> addr_omega [ha, hb]))) hT }⟩

end Rv64Verifier.Gkr.Layer
