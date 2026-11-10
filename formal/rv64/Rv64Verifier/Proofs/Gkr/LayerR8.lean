import Rv64Verifier.Proofs.Gkr.LayerR7

/-!
# `keccak::verify_layer`: the pack rounds

`keccak.rs:118-129` at `0x8000f56c..0x8000f718`: for each coordinate `r` of the claim's point,
`sumcheck_round_poly(3, value, Some(r))` into `f + 264` (its `Err` returned through `0x8000f9e0`),
the challenge `c` sampled, `value = (1 + r + c) * message(c)`, `scale *= 1 + r + c`, and `c` pushed
onto the challenges' `Vec` at `f + 864`. The loop's head is `0x8000f5ec` (`PK`), its exit
`0x8000f718` (`J8`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- The mirror's remaining pack rounds and the rest, from `mu`'s challenge `c`. -/
abbrev packR (s : MachineState) (c : E) (k : Nat) (acc : E × E × List E) : TM KeccakClaim :=
  packRest (claimAt s (lClaim s)) (instanceWeightsRust c) (sumE (instanceWeightsRust c)) k acc

/-- The pack loop's head `0x8000f5ec`, before round `k`. -/
structure PK (s w : MachineState) (ip : Word) (c : E) (k : Nat) (acc : E × E × List E) :
    Prop where
  pc : w.pc = 0x8000f5ec
  base : Base s w
  out : w.getMem (s.getReg .x2 - 1664) = s.getReg .x10
  claim : w.getMem (s.getReg .x2 - 1656) = s.getReg .x15
  sponge : w.getMem (s.getReg .x2 - 1616) = s.getReg .x11 + 8
  p : w.getMem (s.getReg .x2 - 1608) = s.getReg .x11
  ipM : w.getMem (s.getReg .x2 - 1648) = ip
  endM : w.getMem (s.getReg .x2 - 1632) = s.getMem (s.getReg .x15 + 32) +
    BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x15 + 40)).toNat)
  cpM : w.getMem (s.getReg .x2 - 1624) = s.getMem (s.getReg .x15 + 32)
  push : w.getMem (s.getReg .x2 - 1600) = w.getMem (s.getReg .x2 - 840)
  x9 : w.getReg .x9 = BitVec.ofNat 64 (24 * k)
  x23 : w.getReg .x23 = BitVec.ofNat 64 k
  x20 : w.getReg .x20 = s.getReg .x11
  x26 : w.getReg .x26 = 16
  lt : k < (s.getMem (s.getReg .x15 + 40)).toNat
  iw : eListAt w ip 16 = instanceWeightsRust c
  ibuf : heapNext s ≤ ip.toNat ∧ ip.toNat % 8 = 0 ∧ 16 ≤ (w.getMem (s.getReg .x2 - 1672)).toNat ∧
    ip.toNat + 24 * (w.getMem (s.getReg .x2 - 1672)).toNat ≤ heapNext w
  kappa : eAt w (s.getReg .x2 - 800) = sumE (instanceWeightsRust c)
  value : eAt w (s.getReg .x2 - 1592) = acc.1
  scale : eAt w (s.getReg .x2 - 1472) = acc.2.1
  ptLen : w.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 k
  ptCap : k ≤ (w.getMem (s.getReg .x2 - 848)).toNat
  ptBuf : (w.getMem (s.getReg .x2 - 840)).toNat % 8 = 0 ∧
    ((w.getMem (s.getReg .x2 - 848)).toNat * 24 = 0 ∨
      ip.toNat + 24 * (w.getMem (s.getReg .x2 - 1672)).toNat ≤ (w.getMem (s.getReg .x2 - 840)).toNat ∧
      (w.getMem (s.getReg .x2 - 840)).toNat + (w.getMem (s.getReg .x2 - 848)).toNat * 24 ≤ heapNext w)
  ptE : eListAt w (w.getMem (s.getReg .x2 - 840)) k = acc.2.2
  rest : Rest s w (packR s c k acc)

/-- The pack rounds done, at `0x8000f718`. -/
structure J8 (s w : MachineState) (ip : Word) (c : E) (acc : E × E × List E) : Prop where
  pc : w.pc = 0x8000f718
  base : Base s w
  out : w.getMem (s.getReg .x2 - 1664) = s.getReg .x10
  claim : w.getMem (s.getReg .x2 - 1656) = s.getReg .x15
  sponge : w.getMem (s.getReg .x2 - 1616) = s.getReg .x11 + 8
  p : w.getMem (s.getReg .x2 - 1608) = s.getReg .x11
  ipM : w.getMem (s.getReg .x2 - 1648) = ip
  x20 : w.getReg .x20 = s.getReg .x11
  x26 : w.getReg .x26 = 16
  iw : eListAt w ip 16 = instanceWeightsRust c
  ibuf : heapNext s ≤ ip.toNat ∧ ip.toNat % 8 = 0 ∧ 16 ≤ (w.getMem (s.getReg .x2 - 1672)).toNat ∧
    ip.toNat + 24 * (w.getMem (s.getReg .x2 - 1672)).toNat ≤ heapNext w
  kappa : eAt w (s.getReg .x2 - 800) = sumE (instanceWeightsRust c)
  value : eAt w (s.getReg .x2 - 1592) = acc.1
  scale : eAt w (s.getReg .x2 - 1472) = acc.2.1
  ptLen : w.getMem (s.getReg .x2 - 832) = s.getMem (s.getReg .x15 + 40)
  ptCap : (s.getMem (s.getReg .x15 + 40)).toNat ≤ (w.getMem (s.getReg .x2 - 848)).toNat
  ptBuf : (w.getMem (s.getReg .x2 - 840)).toNat % 8 = 0 ∧
    ((w.getMem (s.getReg .x2 - 848)).toNat * 24 = 0 ∨
      ip.toNat + 24 * (w.getMem (s.getReg .x2 - 1672)).toNat ≤ (w.getMem (s.getReg .x2 - 840)).toNat ∧
      (w.getMem (s.getReg .x2 - 840)).toNat + (w.getMem (s.getReg .x2 - 848)).toNat * 24 ≤ heapNext w)
  ptE : eListAt w (w.getMem (s.getReg .x2 - 840)) (s.getMem (s.getReg .x15 + 40)).toNat = acc.2.2
  rest : Rest s w (stage4 (claimAt s (lClaim s)) (instanceWeightsRust c)
    (sumE (instanceWeightsRust c)) acc)

theorem claim_point (s : MachineState) : (claimAt s (lClaim s)).point =
    eListAt s (s.getMem (s.getReg .x15 + 32)) (s.getMem (s.getReg .x15 + 40)).toNat := by
  simp only [claimAt, vecEs, vecPtr, vecLen, lClaim]; rv_eval []

theorem claim_point_length (s : MachineState) :
    (claimAt s (lClaim s)).point.length = (s.getMem (s.getReg .x15 + 40)).toNat := by
  rw [claim_point, eListAt_length]

theorem packRest_step (claim : KeccakClaim) (mu : List E) (kappa : E) {k : Nat}
    (hk : k < claim.point.length) (acc : E × E × List E) :
    packRest claim mu kappa k acc =
      (TM.sumcheckRoundPoly 3 acc.1 (some (claim.point.getD k 0)) >>= fun msg ↦ TM.sample >>=
        fun ch ↦ packRest claim mu kappa (k + 1) ((1 + claim.point.getD k 0 + ch) *
          polyEvalRust msg ch, acc.2.1 * (1 + claim.point.getD k 0 + ch), acc.2.2 ++ [ch])) := by
  rw [packRest_succ _ _ _ hk]
  simp only [packRound, bind_assoc, pure_bind]

theorem eListAt_snoc (s : MachineState) (p : Word) (d : Nat) :
    eListAt s p (d + 1) = eListAt s p d ++ [eAt s (p + BitVec.ofNat 64 (24 * d))] := by
  simp only [eListAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem eListAt_getD_lt (s : MachineState) (p : Word) {n i : Nat} (h : i < n) :
    (eListAt s p n).getD i 0 = eAt s (p + BitVec.ofNat 64 (24 * i)) := by
  rw [List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact h), eListAt_getElem]

theorem mul24_ofNat (x : Word) : x * 16 + x * 8 = BitVec.ofNat 64 (24 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have h16 : (16 : Word).toNat = 16 := rfl
  have h8 : (8 : Word).toNat = 8 := rfl
  rw [h16, h8]
  omega

/-- The mirror's sample, once the transcript's sponge is duplexed: the challenge is the state's
first three lanes. -/
theorem Rest.sample {s u v : MachineState} {f : E → TM KeccakClaim} (h : Rest s u (TM.sample >>= f))
    (hv : ∀ T, TranscriptAt u (s.getReg .x11) T →
      TranscriptAt v (s.getReg .x11) { T with sponge := spDuplex T.sponge }) :
    Rest s v (f (eAt v (s.getReg .x11 + 136))) := h.step fun T hT ↦ by
  have h1 := hv T hT
  refine ⟨{ T with sponge := spDuplex T.sponge }, ?_, h1⟩
  have hs : spongeAt v (s.getReg .x11 + 8) = spDuplex T.sponge := h1.sponge
  have e1 : (spSqueeze T.sponge).2 = spDuplex T.sponge := rfl
  have e2 : (spSqueeze T.sponge).1 = challengeOf (spDuplex T.sponge).state := rfl
  have hce : challengeOf (spDuplex T.sponge).state = eAt v (s.getReg .x11 + 136) := by
    rw [← hs]
    show challengeOf (stateAt v (s.getReg .x11 + 8 + 128)) = _
    rw [challengeOf_stateAt]
    congr 1
    rv_eval []
  show some ((spSqueeze T.sponge).1, { T with sponge := (spSqueeze T.sponge).2 }) = _
  rw [e1, e2, hce]

set_option maxHeartbeats 8000000 in
/-- `0x8000f56c`: the challenges' `Vec` and the instance weights' slots; no rounds to the exit,
otherwise the loop's bounds (`0x8000f590`) and its head. -/
theorem pack_enter {s u : MachineState} {ip : Word} {product : List E} {c : E}
    (hpre : VerifyLayerPre s) (J : J7 s u ip product c) :
    ∃ v, Reaches Image.code u v ∧ (PK s v ip c 0 (polyEvalRust product c, 1, []) ∨
      J8 s v ip c (polyEvalRust product c, 1, [])) := by
  have hb := bounds hpre
  have B := J.base
  have hc := hpre.claim
  have hHu := B.heap.hi
  have hib := J.ibuf
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  simp only [stackLo] at hnx hab
  unfold verifyLayerStack at hb hnx hab
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f56c_spec J.pc (by
    rv_eval [B.x2]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b8000f56c_keeps h₁
  have f₁ := b8000f56c_frame h₁ (by rw [B.x2]; addr_omega [hb])
  rw [B.x2] at f₁
  rv_eval [] at f₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ : Base s t₁ := B.slots hpre x2₁ f₁ (by addr_omega [hb]) (by addr_omega [hb])
  have m40 := b8000f56c_m_x2_40 h₁
  have m64 := b8000f56c_m_x2_64 h₁
  have m112 := b8000f56c_m_x2_112 h₁
  have m864 := b8000f56c_m_x2_864 h₁
  have m872 := b8000f56c_m_x2_872 h₁
  have m880 := b8000f56c_m_x2_880 h₁
  rw [B.x2] at m40 m64 m112 m864 m872 m880
  rv_eval [J.ptCap, J.x9] at m40 m64 m112 m864 m872 m880
  have kw₁ (y : Word) (hy : ∀ K ∈ [880, 872, 112, 864, 64, 40],
      y ≠ s.getReg .x2 - 1712 + BitVec.ofNat 64 K) : t₁.getMem y = u.getMem y :=
    keep_of_writes h₁ (by
      have := hy; rv_eval [B.x2] at this ⊢
      exact ⟨fun h ↦ this.1 h.symm, fun h ↦ this.2.1 h.symm, fun h ↦ this.2.2.1 h.symm,
        fun h ↦ this.2.2.2.1 h.symm, fun h ↦ this.2.2.2.2.1 h.symm, fun h ↦ this.2.2.2.2.2 h.symm⟩)
  have hm₁ (a : Word) (ha : ¬ Within a (s.getReg .x2 - 1672) 848) : t₁.getMem a = u.getMem a :=
    f₁ a ha
  have Fu₁ : DFrame u t₁ (Within · (s.getReg .x2 - 1672) 848) := DFrame.of_memFrame f₁
  have hN₁ : heapNext t₁ = heapNext u := by
    simp only [heapNext]; rw [hm₁ _ (by addr_omega [hb, hnx])]
  have iw₁ : eListAt t₁ ip 16 = instanceWeightsRust c := by
    rw [← J.iw]
    exact Fu₁.eListAt fun j hj hw ↦ by addr_omega [hw, hj, hb, hib, hHu, hab]
  have eA (a : Word) (h1 : (s.getReg .x2).toNat - 824 ≤ a.toNat)
      (h2 : a.toNat + 24 ≤ (s.getReg .x2).toNat - 104) : eAt t₁ a = eAt u a :=
    Fu₁.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb, h1, h2]
  have Rt₁ := J.rest.body hpre B B₁ (Fu₁.mono fun a h ↦ slots_body hpre (by addr_omega [hb])
    (by addr_omega [hb]) h)
  have hlen := J.x21
  have out₁ : t₁.getMem (s.getReg .x2 - 1664) = s.getReg .x10 := by
    rw [kw₁ _ (by rv_eval []; and_intros <;> addr_omega [hb]), J.out]
  have claim₁ : t₁.getMem (s.getReg .x2 - 1656) = s.getReg .x15 := by
    rw [kw₁ _ (by rv_eval []; and_intros <;> addr_omega [hb]), J.claim]
  have sponge₁ : t₁.getMem (s.getReg .x2 - 1616) = s.getReg .x11 + 8 := by
    rw [kw₁ _ (by rv_eval []; and_intros <;> addr_omega [hb]), J.sponge]
  have p₁ : t₁.getMem (s.getReg .x2 - 1608) = s.getReg .x11 := by
    rw [kw₁ _ (by rv_eval []; and_intros <;> addr_omega [hb]), J.p]
  have kappa₁ : eAt t₁ (s.getReg .x2 - 800) = sumE (instanceWeightsRust c) := by
    rw [eA _ (by addr_omega [hb]) (by addr_omega [hb])]; exact J.kappa
  have value₁ : eAt t₁ (s.getReg .x2 - 1592) = polyEvalRust product c := by
    rw [← J.value]
    exact eAt_congr (kw₁ _ (by rv_eval []; and_intros <;> addr_omega [hb]))
      (kw₁ _ (by rv_eval []; and_intros <;> addr_omega [hb]))
      (kw₁ _ (by rv_eval []; and_intros <;> addr_omega [hb]))
  have scale₁ : eAt t₁ (s.getReg .x2 - 1472) = 1 := by
    rw [← J.scale]
    exact eAt_congr (kw₁ _ (by rv_eval []; and_intros <;> addr_omega [hb]))
      (kw₁ _ (by rv_eval []; and_intros <;> addr_omega [hb]))
      (kw₁ _ (by rv_eval []; and_intros <;> addr_omega [hb]))
  have ibuf₁ : heapNext s ≤ ip.toNat ∧ ip.toNat % 8 = 0 ∧
      16 ≤ (t₁.getMem (s.getReg .x2 - 1672)).toNat ∧
      ip.toNat + 24 * (t₁.getMem (s.getReg .x2 - 1672)).toNat ≤ heapNext t₁ := by
    rw [m40, hN₁]; exact ⟨hib.1, hib.2.1, hib.2.2.1, hib.2.2.2⟩
  have ptBuf₁ : (t₁.getMem (s.getReg .x2 - 840)).toNat % 8 = 0 ∧
      ((t₁.getMem (s.getReg .x2 - 848)).toNat * 24 = 0 ∨
        ip.toNat + 24 * (t₁.getMem (s.getReg .x2 - 1672)).toNat ≤
          (t₁.getMem (s.getReg .x2 - 840)).toNat ∧
        (t₁.getMem (s.getReg .x2 - 840)).toNat + (t₁.getMem (s.getReg .x2 - 848)).toNat * 24 ≤
          heapNext t₁) := by
    rw [m864, m872, m40, hN₁]; exact J.ptBuf
  by_cases h0 : s.getMem (s.getReg .x15 + 40) = 0
  · -- no rounds
    have pc₁ : t₁.pc = 0x8000f718 := b8000f56c_pc_taken h₁ (by rw [hlen, h0])
    have hl0 : (s.getMem (s.getReg .x15 + 40)).toNat = 0 := by rw [h0]; rfl
    refine ⟨t₁, hr₁, Or.inr {
      pc := pc₁
      base := B₁
      out := out₁
      claim := claim₁
      sponge := sponge₁
      p := p₁
      ipM := m64
      x20 := by rw [k₁ .x20 (by decide), J.x20]
      x26 := by rw [k₁ .x26 (by decide), J.x26]
      iw := iw₁
      ibuf := ibuf₁
      kappa := kappa₁
      value := value₁
      scale := scale₁
      ptLen := by rw [m880, h0]
      ptCap := by rw [hl0]; exact Nat.zero_le _
      ptBuf := ptBuf₁
      ptE := by rw [hl0]; rfl
      rest := by
        have e := packRest_end (claimAt s (lClaim s)) (instanceWeightsRust c)
          (sumE (instanceWeightsRust c)) (polyEvalRust product c, 1, [])
        rw [claim_point_length, hl0] at e
        rw [← e]; exact Rt₁ }⟩
  -- `0x8000f590`: the point's start and end
  have pc₁ : t₁.pc = 0x8000f590 := b8000f56c_pc_not_taken h₁ (by rw [hlen]; exact h0)
  have kc (y : Word) (h1 : (lClaim s).toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ (lClaim s).toNat + 96) :
      t₁.getMem y = s.getMem y :=
    B₁.keep (missClaim hpre B₁.heap) (by addr_omega [hc]) h1 h2
  have c32 : t₁.getMem (s.getReg .x15 + 32) = s.getMem (s.getReg .x15 + 32) :=
    kc _ (by addr_omega [hc]) (by addr_omega [hc])
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f590_spec pc₁ (by
    rv_eval [x2₁, claim₁]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc]))
  have k₂ := b8000f590_keeps h₂
  have f₂ := b8000f590_frame h₂ (by rw [x2₁]; addr_omega [hb])
  rw [x2₁] at f₂
  rv_eval [] at f₂
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := (k₂ .x2 (by decide)).trans x2₁
  have B₂ : Base s t₂ := B₁.slots hpre x2₂ f₂ (by addr_omega [hb]) (by addr_omega [hb])
  have m80 := b8000f590_m_x2_80 h₂
  have m88 := b8000f590_m_x2_88 h₂
  rw [x2₁] at m80 m88
  rv_eval [claim₁, c32, k₁ .x21 (by decide), hlen, mul24_ofNat] at m80 m88
  have keep₂ (y : Word) (h : ¬ Within y (s.getReg .x2 - 1632) 16) : t₂.getMem y = t₁.getMem y :=
    f₂ y h
  have hN₂ : heapNext t₂ = heapNext t₁ := by
    simp only [heapNext]; rw [keep₂ _ (by addr_omega [hb, hnx])]
  have F₂ : DFrame t₁ t₂ (Within · (s.getReg .x2 - 1632) 16) := DFrame.of_memFrame f₂
  have e2 (a : Word) (h : a.toNat + 24 ≤ (s.getReg .x2).toNat - 1632 ∨
      (s.getReg .x2).toNat - 1616 ≤ a.toNat ∧ a.toNat + 24 ≤ (s.getReg .x2).toNat) :
      eAt t₂ a = eAt t₁ a :=
    F₂.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb, h]
  refine ⟨t₂, hr₁.trans hr₂, Or.inl {
    pc := b8000f590_pc h₂
    base := B₂
    out := by rw [keep₂ _ (by addr_omega [hb]), out₁]
    claim := by rw [keep₂ _ (by addr_omega [hb]), claim₁]
    sponge := by rw [keep₂ _ (by addr_omega [hb]), sponge₁]
    p := by rw [keep₂ _ (by addr_omega [hb]), p₁]
    ipM := by rw [keep₂ _ (by addr_omega [hb]), m64]
    endM := m80
    cpM := m88
    push := by rw [keep₂ _ (by addr_omega [hb]), keep₂ _ (by addr_omega [hb]), m112, m872]
    x9 := by rw [b8000f590_x9 h₂]; rfl
    x23 := by rw [b8000f590_x23 h₂]; rfl
    x20 := by rw [k₂ .x20 (by decide), k₁ .x20 (by decide), J.x20]
    x26 := by rw [k₂ .x26 (by decide), k₁ .x26 (by decide), J.x26]
    lt := by
      have : (s.getMem (s.getReg .x15 + 40)).toNat ≠ 0 := fun h ↦ h0 (BitVec.eq_of_toNat_eq h)
      omega
    iw := by
      rw [← iw₁]
      exact F₂.eListAt fun j hj hw ↦ by addr_omega [hw, hj, hb, hib, hHu, hab]
    ibuf := by rw [keep₂ _ (by addr_omega [hb]), hN₂]; exact ibuf₁
    kappa := by rw [e2 _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact kappa₁
    value := by rw [e2 _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact value₁
    scale := by rw [e2 _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact scale₁
    ptLen := by rw [keep₂ _ (by addr_omega [hb]), m880]; rfl
    ptCap := Nat.zero_le _
    ptBuf := by
      rw [keep₂ _ (by addr_omega [hb]), keep₂ _ (by addr_omega [hb]),
        keep₂ (s.getReg .x2 - 1672) (by addr_omega [hb]), hN₂]
      exact ptBuf₁
    ptE := rfl
    rest := Rt₁.body hpre B₁ B₂ (F₂.mono fun a h ↦ slots_body hpre (by addr_omega [hb])
      (by addr_omega [hb]) h) }⟩

/-! ## A round -/

/-- What a round writes before the push: its slots, the callees' stacks below the frame, `NEXT`,
the sponge and what it allocates. -/
@[rv_addr] def W8 (s w v : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1592) 24 ∨ Within a (s.getReg .x2 - 1448) 24 ∨
    Within a (s.getReg .x2 - 752) 32 ∨ Within a (s.getReg .x2 - 128) 24 ∨
    Within a (s.getReg .x2 - 1712 - BitVec.ofNat 64 sumcheckStack) sumcheckStack ∨
    Within a nextAddr 8 ∨ Within a (s.getReg .x11 + 8) 344 ∨ Fresh w v a

theorem w8_mono {s w v v' : MachineState} (h : heapNext v ≤ heapNext v') {a : Word}
    (ha : W8 s w v a) : W8 s w v' a := by
  simp only [W8, Fresh] at ha ⊢
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha.1, by omega⟩))))))

/-- The round's coordinate. -/
abbrev rOf (s : MachineState) (k : Nat) : E :=
  eAt s (s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k))

/-- The round's message read, at `0x8000f644`, before the challenge. -/
structure Q1 (s w t : MachineState) (ip : Word) (c : E) (k : Nat) (acc : E × E × List E)
    (msg : List E) : Prop where
  pc : t.pc = 0x8000f644
  base : Base s t
  mono : heapNext w ≤ heapNext t
  frame : DFrame w t (W8 s w t)
  x8 : t.getReg .x8 = s.getMem (s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k))
  x27 : t.getReg .x27 = s.getMem (s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k) + 8)
  x24 : t.getReg .x24 = s.getMem (s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k) + 16)
  x19 : t.getReg .x19 = s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k)
  regs : ∀ r ∈ [Reg.x9, .x20, .x23, .x26], t.getReg r = w.getReg r
  x22 : t.getReg .x22 = t.getMem (s.getReg .x2 - 1440)
  x21 : t.getReg .x21 = t.getMem (s.getReg .x2 - 1432)
  msgV : NewVecE w t (s.getReg .x2 - 1448) msg
  rest : Rest s t (TM.sample >>= fun ch ↦ packR s c (k + 1)
    ((1 + rOf s k + ch) * polyEvalRust msg ch, acc.2.1 * (1 + rOf s k + ch), acc.2.2 ++ [ch]))

/-- `0x8000f9e0`: a callee's `Err` (its discriminant in `s6`, its payload in `s5`) into the
result, then return. -/
theorem err_f9e0 {s u : MachineState} (hpre : VerifyLayerPre s) (B : Base s u)
    (hpc : u.pc = 0x8000f9e0) (hout : u.getMem (s.getReg .x2 - 1664) = s.getReg .x10)
    (hf : Fails s) : ∃ t, Reaches Image.code u t ∧ Ret s t := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  have hof := hpre.outFree
  obtain ⟨w, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f9e0_spec hpc (by
    rv_eval [B.x2, hout]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have m0 := b8000f9e0_m2 h₁
  rw [B.x2] at m0
  rv_eval [hout] at m0
  have f₁ : MemFrame u w (s.getReg .x10) 24 := h₁.memFrame (by
    rv_eval [B.x2, hout]; and_intros <;> addr_omega [ho])
  have x2w : w.getReg .x2 = s.getReg .x2 - 1712 := (b8000f9e0_keeps h₁ .x2 (by decide)).trans B.x2
  have hN : w.getMem nextAddr = u.getMem nextAddr := f₁ _ (by addr_omega [ho, hof])
  have Bw : Base s w := B.next hpre x2w
    ⟨by simp only [heapNext, hN]; exact B.heap.lo, by simp only [heapNext, hN]; exact B.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) (DFrame.of_memFrame f₁) fun a ha ↦
      ⟨Or.inl (by addr_omega [ha]), by unfold verifyLayerStack at hb hos; addr_omega [ha, hos, hb]⟩
  obtain ⟨t, hr₂, pc, pres, same⟩ := exit hpre (b8000f9e0_pc h₁) Bw.x2 Bw.saved
  exact ⟨t, hr₁.trans hr₂, pc, pres, post_err Bw m0 hf same⟩

set_option maxHeartbeats 16000000 in
/-- `0x8000f5ec`: `sumcheck_round_poly(3, value, Some(r))`; its `Err` returned (`0x8000f9e0`). -/
theorem pk_round (hRP : RoundPolySpec) {s w : MachineState} {ip : Word} {c : E} {k : Nat}
    {acc : E × E × List E} (hpre : VerifyLayerPre s) (P : PK s w ip c k acc) :
    ∃ t, Reaches Image.code w t ∧ ((∃ msg, Q1 s w t ip c k acc msg) ∨ Ret s t ∨
      Dead Image.code t) := by
  have hb := bounds hpre
  have B := P.base
  have hc := hpre.claim
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hS := hpre.self.self
  have hss := hpre.selfStack
  simp only [stackLo] at hnx hab hss
  unfold verifyLayerStack at hb hnx hab hsm hss
  have hk := P.lt
  have pR := hpre.point
  have mp0 := missVec B.heap hpre.point hpre.pointOut hpre.pointSelf hpre.pointStack hpre.pointFree
  simp only [VecRegion, vecPtr, vecLen, lClaim] at pR mp0
  rv_eval [] at pR mp0
  have hR : Region (s.getMem (s.getReg .x15 + 32)) (24 * (s.getMem (s.getReg .x15 + 40)).toNat) := by
    rcases pR with h0 | h0
    · omega
    · exact h0
  have kp (y : Word) (h1 : (s.getMem (s.getReg .x15 + 32)).toNat ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getMem (s.getReg .x15 + 32)).toNat +
        24 * (s.getMem (s.getReg .x15 + 40)).toNat) : w.getMem y = s.getMem y :=
    B.keep mp0 (by addr_omega [hR]) h1 h2
  -- `0x8000f5ec`: `Some(r)` at `f + 960`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f5ec_spec P.pc (by
    rv_eval [B.x2, P.cpM, P.x9]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid hR ?_ ?_ ?_ <;> addr_omega [hR, hk]))
  have k₁ := b8000f5ec_keeps h₁
  have f₁ := b8000f5ec_frame h₁ (by rw [B.x2]; addr_omega [hb])
  rw [B.x2] at f₁
  rv_eval [] at f₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ : Base s t₁ := B.slots hpre x2₁ f₁ (by addr_omega [hb]) (by addr_omega [hb])
  have r0 : w.getMem (s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k)) =
      s.getMem (s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k)) :=
    kp _ (by addr_omega [hR, hk]) (by addr_omega [hR, hk])
  have r1 : w.getMem (s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k) + 8) =
      s.getMem (s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k) + 8) :=
    kp _ (by addr_omega [hR, hk]) (by addr_omega [hR, hk])
  have r2 : w.getMem (s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k) + 16) =
      s.getMem (s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k) + 16) :=
    kp _ (by addr_omega [hR, hk]) (by addr_omega [hR, hk])
  have m960 := b8000f5ec_m_x2_960 h₁
  have m968 := b8000f5ec_m_x2_968 h₁
  have m976 := b8000f5ec_m_x2_976 h₁
  have m984 := b8000f5ec_m_x2_984 h₁
  rw [B.x2] at m960 m968 m976 m984
  rv_eval [P.cpM, P.x9, r0, r1, r2] at m960 m968 m976 m984
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 1448 := by rw [b8000f5ec_x10 h₁, B.x2]; rv_eval []
  have x11₁ : t₁.getReg .x11 = s.getReg .x11 := by rw [b8000f5ec_x11 h₁, P.x20]
  have x12₁ : t₁.getReg .x12 = 3 := b8000f5ec_x12 h₁
  have x13₁ : t₁.getReg .x13 = s.getReg .x2 - 1592 := by rw [b8000f5ec_x13 h₁, B.x2]; rv_eval []
  have x14₁ : t₁.getReg .x14 = s.getReg .x2 - 752 := by rw [b8000f5ec_x14 h₁, B.x2]; rv_eval []
  have F₁ : DFrame w t₁ (Within · (s.getReg .x2 - 752) 32) := DFrame.of_memFrame f₁
  have value₁ : eAt t₁ (s.getReg .x2 - 1592) = acc.1 := by
    rw [F₁.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb]]; exact P.value
  have hrv : (claimAt s (lClaim s)).point.getD k 0 = rOf s k := by
    rw [claim_point, eListAt_getD_lt _ _ hk]
  have opt₁ : optEAt t₁ (s.getReg .x2 - 752) = some (rOf s k) := by
    simp only [optEAt, m960]
    rw [ite_eq_right (by decide)]
    congr 1
    apply eq_of_limbs
    rw [limbs_eAt, limbs_eAt]
    rv_eval [m968, m976, m984]
  -- `sumcheck_round_poly`
  have tp : TPre 24 roundPolyStack t₁ := B₁.tpre hpre 1448 x10₁ x11₁ (by decide) (by decide)
    (by decide) (by unfold sumcheckStack; omega) (by decide)
  have hlo : stackLo t₁ roundPolyStack =
      s.getReg .x2 - 1712 - BitVec.ofNat 64 roundPolyStack := by simp only [stackLo, x2₁]
  have pre : RoundPolyPre t₁ := { tp with
    count := by rw [x12₁]; decide
    claim := by rw [x13₁]; addr_omega [hb, hsm]
    eqFactor := by rw [x14₁]; addr_omega [hb, hsm]
    claimFree := by rw [x13₁]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    eqFactorFree := by rw [x14₁]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    claimStack := by rw [x13₁, hlo]; addr_omega [hb]
    eqFactorStack := by rw [x14₁, hlo]; addr_omega [hb]
    claimSelf := by rw [x13₁, x11₁]; addr_omega [hb, hss, hS]
    eqFactorSelf := by rw [x14₁, x11₁]; addr_omega [hb, hss, hS] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hp₂, RP⟩ | hd⟩ := hRP.call (hr₁) (b8000f5ec_pc h₁) pre
  swap
  · exact ⟨_, hr₂, Or.inr (Or.inr hd)⟩
  have G₂ := RP.frame
  have V₂ := RP.value
  unfold TFrame at G₂
  rw [x10₁, x11₁] at G₂
  rw [x10₁, x11₁, x12₁, x13₁, x14₁, value₁, opt₁, show (3 : Word).toNat = 3 from rfl] at V₂
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := (hp₂.reg .x2).trans x2₁
  have B₂ : Base s t₂ := B₁.next hpre x2₂ RP.heap RP.mono RP.frame fun a ha ↦
    tframe_lw hpre B₁ 1448 x10₁ x11₁ (by decide) (by decide) (by unfold sumcheckStack; omega)
      RP.heap a ha
  have R₀ : Rest s w (TM.sumcheckRoundPoly 3 acc.1 (some (rOf s k)) >>= fun msg ↦ TM.sample >>=
      fun ch ↦ packR s c (k + 1) ((1 + rOf s k + ch) * polyEvalRust msg ch,
        acc.2.1 * (1 + rOf s k + ch), acc.2.2 ++ [ch])) := by
    have e := packRest_step (claimAt s (lClaim s)) (instanceWeightsRust c)
      (sumE (instanceWeightsRust c)) (by rw [claim_point_length]; exact hk) acc
    rw [hrv] at e
    exact P.rest.congr e
  have tat₁ (T : TState) (hT : TranscriptAt w (s.getReg .x11) T) : TranscriptAt t₁ (s.getReg .x11) T :=
    B.slots_tat hpre B₁ f₁ (by addr_omega [hb]) (by addr_omega [hb]) hT
  -- `0x8000f630`: `Err` or the message
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f630_spec
    (by rw [hpc₂, returnAddress_eq, b8000f5ec_x1 h₁]; decide) (by
      rv_eval [x2₂]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b8000f630_keeps h₃
  have hm₃ := b8000f630_mem_same h₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have B₃ : Base s t₃ := B₂.same x2₃ hm₃
  have hH₂ := RP.heap.hi
  have hN₁ : heapNext t₁ = heapNext w := by
    simp only [heapNext]; rw [f₁ _ (by addr_omega [hb, hnx])]
  rw [hlo] at G₂
  have keep₃ (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1448 ∨
        (s.getReg .x2).toNat - 1424 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 752 ∨
        (s.getReg .x2).toNat - 720 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 104) :
      t₃.getMem y = w.getMem y := by
    rw [hm₃, G₂ y fun i hi hw ↦ by
        simp only [Fresh] at hw
        rcases hw with hw | hw | hw | hw | hw <;>
          addr_omega [hw, hi, h1, h2, hb, hss, hS, hnx, hab, hH₂],
      f₁ y (by addr_omega [h1, h2, hb])]
  by_cases herr : t₂.getMem (s.getReg .x2 - 1448) = errNiche
  · -- `0x8000f9e0`: the `Err` copied out
    have hf : Fails s := R₀.fail fun T hT ↦ by
      have e := V₂ T (tat₁ T hT)
      generalize (TM.sumcheckRoundPoly 3 acc.1 (some (rOf s k))).run T = o at e ⊢
      rcases o with _ | ⟨q, T'⟩
      · rfl
      · exact absurd herr e.1
    obtain ⟨t, hr, ht⟩ := err_f9e0 hpre B₃ (b8000f630_pc_taken h₃ (by rw [x2₂]; rv_eval []; exact herr))
      (by rw [keep₃ _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), P.out]) hf
    exact ⟨t, hr₂.trans (hr₃.trans hr), Or.inr (Or.inl ht)⟩
  -- the message
  obtain ⟨okV, okB⟩ := RP.ok (by rw [x10₁]; exact herr)
  rw [x10₁] at okV okB
  have msgV₂ : NewVecE t₁ t₂ (s.getReg .x2 - 1448) (vecEs t₂ (s.getReg .x2 - 1448)) :=
    ⟨okV, okB, rfl⟩
  have R₂ : Rest s t₃ (TM.sample >>= fun ch ↦ packR s c (k + 1)
      ((1 + rOf s k + ch) * polyEvalRust (vecEs t₂ (s.getReg .x2 - 1448)) ch,
        acc.2.1 * (1 + rOf s k + ch), acc.2.2 ++ [ch])) := R₀.step fun T hT ↦ by
    have e := V₂ T (tat₁ T hT)
    generalize (TM.sumcheckRoundPoly 3 acc.1 (some (rOf s k))).run T = o at e ⊢
    rcases o with _ | ⟨q, T'⟩
    · exact absurd e herr
    · refine ⟨T', ?_, transcriptAt_congr hm₃ e.2.2⟩
      rw [← e.2.1.elems]
  have hN₃ : heapNext t₃ = heapNext t₂ := by simp only [heapNext, hm₃]
  have Fw : DFrame w t₃ (W8 s w t₃) :=
    ((F₁.mono (w' := W8 s w t₃) fun a h ↦ Or.inr (Or.inr (Or.inl h))).trans G₂ fun a h ↦ by
      simp only [W8, Fresh] at h ⊢
      rcases h with h | h | h | h | h
      · exact Or.inr (Or.inl (by addr_omega [h, hb]))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h])))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨by rw [← hN₁]; exact h.1, by rw [hN₃]; exact h.2⟩))))))).trans
      (DFrame.of_same hm₃ _) fun _ h ↦ h
  have regs (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x19, .x20, .x23, .x24, .x26, .x27]) :
      t₃.getReg r = t₁.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hp₂.reg r (mem_of_mem hr _)]
  refine ⟨t₃, hr₂.trans hr₃, Or.inl ⟨vecEs t₂ (s.getReg .x2 - 1448), {
    pc := b8000f630_pc_not_taken h₃ (by rw [x2₂]; rv_eval []; exact herr)
    base := B₃
    mono := by rw [hN₃, ← hN₁]; exact RP.mono
    frame := Fw
    x8 := by rw [regs .x8 (by decide), b8000f5ec_x8 h₁, B.x2]; rv_eval [P.cpM, P.x9, r0]
    x27 := by rw [regs .x27 (by decide), b8000f5ec_x27 h₁, B.x2]; rv_eval [P.cpM, P.x9, r1]
    x24 := by rw [regs .x24 (by decide), b8000f5ec_x24 h₁, B.x2]; rv_eval [P.cpM, P.x9, r2]
    x19 := by rw [regs .x19 (by decide), b8000f5ec_x19 h₁, B.x2]; rv_eval [P.cpM, P.x9]
    regs := fun r hr ↦ by
      rw [regs r (by simp only [List.mem_cons] at hr ⊢; rcases hr with h | h | h | h | h <;>
        simp [h]), k₁ r (by simp only [List.mem_cons] at hr ⊢; rcases hr with h | h | h | h | h <;>
        simp [h])]
    x22 := by rw [b8000f630_x22 h₃, x2₂, hm₃]; rv_eval []
    x21 := by rw [b8000f630_x21 h₃, x2₂, hm₃]; rv_eval []
    msgV := by
      have := newVecE_congr hm₃ msgV₂
      exact Open.newVecE_mono this (le_of_eq hN₁.symm)
    rest := R₂ }⟩⟩

/-- A block's writes all satisfy `W`: a frame of `W`. -/
theorem dframe_of_writes {x : Sym.Expect} {s t : MachineState} (h : x.Holds s t)
    {W : Word → Prop} (hw : ∀ k ∈ x.writes, W (k.eval s)) : DFrame s t W := fun a ha ↦
  keep_of_writes h fun k hk heq ↦ ha 0 (by decide) (by rw [add_ofNat_zero, ← heq]; exact hw k hk)

/-- `mul` of two slots into a third, `f + 1712 - K` its result. -/
theorem mulCall (hM : MulSpec) {s u₀ u : MachineState} (hpre : VerifyLayerPre s) (B : Base s u)
    (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x80008c48) (K L R : Nat)
    (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K)
    (hx11 : u.getReg .x11 = s.getReg .x2 - BitVec.ofNat 64 L)
    (hx12 : u.getReg .x12 = s.getReg .x2 - BitVec.ofNat 64 R)
    (hK : 128 ≤ K ∧ K ≤ 1712 ∧ K % 8 = 0) (hL : 24 ≤ L ∧ L ≤ 1712 ∧ L % 8 = 0)
    (hR : 24 ≤ R ∧ R ≤ 1712 ∧ R % 8 = 0) (hKL : K + 24 ≤ L ∨ L + 24 ≤ K)
    (hKR : K + 24 ≤ R ∨ R + 24 ≤ K) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Base s v ∧
      DFrame u v (fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 K) 24 ∨
        Within a (s.getReg .x2 - 2736) 1024) ∧
      eAt v (s.getReg .x2 - BitVec.ofNat 64 K) =
        eAt u (s.getReg .x2 - BitVec.ofNat 64 L) * eAt u (s.getReg .x2 - BitVec.ofNat 64 R)) ∨
      Dead Image.code v) := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  simp only [stackLo] at hnx
  unfold verifyLayerStack at hb hnx
  obtain ⟨hK1, hK2, hK3⟩ := hK
  obtain ⟨hL1, hL2, hL3⟩ := hL
  obtain ⟨hR1, hR2, hR3⟩ := hR
  have hmp : MulPre u := mul_pre hpre B.x2 (B.rodata hpre) K hx10 (by omega) hK2 hK3
    (by rw [hx11]; exact slot_vmr hpre (by omega) hL2 hL3)
    (by rw [hx11]; addr_omega [hb, hL1, hL2])
    (by rw [hx10, hx11]; addr_omega [hb, hK1, hK2, hL1, hL2, hKL])
    (by rw [hx12]; exact slot_vmr hpre (by omega) hR2 hR3)
    (by rw [hx12]; addr_omega [hb, hR1, hR2])
    (by rw [hx10, hx12]; addr_omega [hb, hK1, hK2, hR1, hR2, hKR])
  obtain ⟨v, hrv, ⟨hpc', hp, post⟩ | hd⟩ := hM.call hr hpc hmp
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have F := mul_frame B.x2 post
  rw [hx10] at F
  have V := post.value
  rw [hx10, hx11, hx12] at V
  have x2v : v.getReg .x2 = s.getReg .x2 - 1712 := (hp.reg .x2).trans B.x2
  have hN : v.getMem nextAddr = u.getMem nextAddr := F _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hi, hw, hb, hnx, hK1, hK2]
  have Bv : Base s v := B.next hpre x2v
    ⟨by simp only [heapNext, hN]; exact B.heap.lo, by simp only [heapNext, hN]; exact B.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) F fun a h ↦ by
      refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> rcases h with h | h <;>
        addr_omega [h, hb, hK1, hK2]
  exact ⟨v, hrv, Or.inl ⟨hpc', hp, Bv, F, V⟩⟩

/-- What the round's middle writes: its slots, the callees' stacks, the sponge. -/
@[rv_addr] def W8b (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1592) 24 ∨ Within a (s.getReg .x2 - 1448) 24 ∨
    Within a (s.getReg .x2 - 752) 32 ∨ Within a (s.getReg .x2 - 128) 24 ∨
    Within a (s.getReg .x2 - 1712 - BitVec.ofNat 64 sumcheckStack) sumcheckStack ∨
    Within a (s.getReg .x11 + 8) 344

/-- The round's products, at `0x8000f6d0`: `nv` is the new value. -/
structure Q2 (s w t : MachineState) (c : E) (k : Nat) (acc : E × E × List E) (ch nv : E) :
    Prop where
  pc : t.pc = 0x8000f6d0
  base : Base s t
  mono : heapNext w ≤ heapNext t
  frame : DFrame w t (W8 s w t)
  x19 : t.getReg .x19 = s.getMem (s.getReg .x15 + 32) + BitVec.ofNat 64 (24 * k)
  regs : ∀ r ∈ [Reg.x9, .x23, .x26], t.getReg r = w.getReg r
  chL : limbs ch = (t.getReg .x18, t.getReg .x25, t.getReg .x20)
  value : eAt t (s.getReg .x2 - 1592) = nv
  sc : eAt t (s.getReg .x2 - 752) = acc.2.1 * (1 + rOf s k + ch)
  rest : Rest s t (packR s c (k + 1) (nv, acc.2.1 * (1 + rOf s k + ch), acc.2.2 ++ [ch]))

theorem limbs_one_add (r ch : E) : limbs (1 + r + ch) =
    (((limbs r).1 ^^^ (limbs ch).1) ^^^ 1, (limbs ch).2.1 ^^^ (limbs r).2.1,
      (limbs ch).2.2 ^^^ (limbs r).2.2) := by
  rw [limbs_add, limbs_add, limbs_one]
  simp only [Sym.zero_xor_lit]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ac_rfl

end Rv64Verifier.Gkr.Layer
