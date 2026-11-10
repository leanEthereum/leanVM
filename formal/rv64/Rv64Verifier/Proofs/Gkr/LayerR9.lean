import Rv64Verifier.Proofs.Gkr.LayerR8
import Rv64Verifier.Proofs.Gkr.LayerJ11

/-!
# `keccak::verify_layer`: the local sumcheck

`keccak.rs:130-135` at `0x8000f718..0x8000f750`: `sumcheck(value, 4, [None; 11])` into `f + 960`
(`r9_sc`), its `Err` returned through `0x8000f9f8`. What the rest of the body up to the second
check keeps of the pack rounds' state is `K8`, and what it writes is `W9`.
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-! ## What the body writes from `0x8000f718` to the second check, and what it keeps -/

/-- The frame's scratch slots: `f .. f + 40`, `f + 72 .. f + 96`, `f + 112 .. f + 240`,
`f + 264 .. f + 864`, `f + 936 .. f + 1608`. -/
@[rv_addr] def Scr9 (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1712) 40 ∨ Within a (s.getReg .x2 - 1640) 24 ∨
    Within a (s.getReg .x2 - 1600) 128 ∨ Within a (s.getReg .x2 - 1448) 600 ∨
    Within a (s.getReg .x2 - 776) 672

/-- The scratch slots, the callees' stacks below the frame, `NEXT`, the sponge and what is
allocated from `w` on to `v`. -/
@[rv_addr] def W9 (s w v : MachineState) (a : Word) : Prop :=
  Scr9 s a ∨ Within a (s.getReg .x2 - 1712 - BitVec.ofNat 64 sumcheckStack) sumcheckStack ∨
    Within a nextAddr 8 ∨ Within a (s.getReg .x11 + 8) 344 ∨ Fresh w v a

/-- The frame's slots the body keeps: `f + 40 .. f + 72`, `f + 96 .. f + 112`, the scale at
`f + 240`, the point's `Vec` at `f + 864` and `kappa` at `f + 912`. -/
@[rv_addr] def Kept (s : MachineState) (y : Word) (n : Nat) : Prop :=
  (s.getReg .x2).toNat - 1672 ≤ y.toNat ∧ y.toNat + n ≤ (s.getReg .x2).toNat - 1640 ∨
    (s.getReg .x2).toNat - 1616 ≤ y.toNat ∧ y.toNat + n ≤ (s.getReg .x2).toNat - 1600 ∨
    (s.getReg .x2).toNat - 1472 ≤ y.toNat ∧ y.toNat + n ≤ (s.getReg .x2).toNat - 1448 ∨
    (s.getReg .x2).toNat - 848 ≤ y.toNat ∧ y.toNat + n ≤ (s.getReg .x2).toNat - 776

theorem w9_kept {s w v : MachineState} (hpre : VerifyLayerPre s) (hH : HeapOk v) {y : Word}
    {n : Nat} (hy : Kept s y n) : ∀ i < n, ¬ W9 s w v (y + BitVec.ofNat 64 i) := by
  intro i hi hw
  have hb := bounds hpre
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have := hH.hi
  simp only [stackLo] at hnx hab hss
  unfold verifyLayerStack at hb hnx hab hss
  simp only [Kept] at hy
  simp only [W9, Scr9, Fresh] at hw
  rcases hw with (hw | hw | hw | hw | hw) | hw | hw | hw | hw
  · addr_omega [hw, hy, hi, hb]
  · addr_omega [hw, hy, hi, hb]
  · addr_omega [hw, hy, hi, hb]
  · addr_omega [hw, hy, hi, hb]
  · addr_omega [hw, hy, hi, hb]
  · addr_omega [hw, hy, hi, hb]
  · addr_omega [hw, hy, hi, hb, hnx]
  · addr_omega [hw, hy, hi, hb, hss, hS]
  · addr_omega [hw, hy, hi, hb, hab, this]

/-- A buffer allocated since the entry, below `NEXT` at `w`, misses `W9`. -/
theorem w9_new {s w v : MachineState} (hpre : VerifyLayerPre s) (hH : HeapOk w) {p : Word}
    {n : Nat} (h1 : heapNext s ≤ p.toNat) (h2 : p.toNat + n ≤ heapNext w) :
    ∀ i < n, ¬ W9 s w v (p + BitVec.ofNat 64 i) := by
  intro i hi hw
  have hb := bounds hpre
  have hS := hpre.self.self
  have hsf := hpre.selfFree.1
  have hab := hpre.stack.above
  have := hH.hi
  simp only [stackLo] at hab
  unfold verifyLayerStack at hb hab
  simp only [W9, Scr9, Fresh] at hw
  rcases hw with (hw | hw | hw | hw | hw) | hw | hw | hw | hw
  · addr_omega [hw, h2, hi, hb, hab, this]
  · addr_omega [hw, h2, hi, hb, hab, this]
  · addr_omega [hw, h2, hi, hb, hab, this]
  · addr_omega [hw, h2, hi, hb, hab, this]
  · addr_omega [hw, h2, hi, hb, hab, this]
  · addr_omega [hw, h2, hi, hb, hab, this]
  · addr_omega [hw, h2, hi, this]
  · rcases hsf with h | h <;> addr_omega [hw, h, h1, h2, hi, hS, this]
  · addr_omega [hw, h2, hi]

theorem w9_word {s w v : MachineState} (hpre : VerifyLayerPre s) (hH : HeapOk v)
    (F : DFrame w v (W9 s w v)) {y : Word} (hy : Kept s y 8) : v.getMem y = w.getMem y :=
  F y (w9_kept hpre hH hy)

theorem w9_eAt {s w v : MachineState} (hpre : VerifyLayerPre s) (hH : HeapOk v)
    (F : DFrame w v (W9 s w v)) {y : Word} (hy : Kept s y 24) : eAt v y = eAt w y :=
  F.eAt (w9_kept hpre hH hy)

theorem w9_eList {s w v : MachineState} (hpre : VerifyLayerPre s) (hH : HeapOk w)
    (F : DFrame w v (W9 s w v)) {p : Word} {k n : Nat} (hB : NewBuf s w p n 8) (hk : 24 * k ≤ n) :
    eListAt v p k = eListAt w p k := by
  rcases hB.2 with h0 | ⟨b1, b2⟩
  · have : k = 0 := by omega
    subst this; rfl
  · exact F.eListAt (w9_new hpre hH b1 (by omega))

theorem newBuf_mono {s w v : MachineState} {p : Word} {n : Nat} (hB : NewBuf s w p n 8)
    (hN : heapNext w ≤ heapNext v) : NewBuf s v p n 8 :=
  ⟨hB.1, hB.2.imp_right fun h ↦ ⟨h.1, h.2.trans hN⟩⟩

theorem newBuf_len {s w : MachineState} {p : Word} {n m : Nat} (hB : NewBuf s w p n 8)
    (h : m ≤ n) : NewBuf s w p m 8 := by
  refine ⟨hB.1, ?_⟩
  rcases hB.2 with h0 | ⟨b1, b2⟩
  · left; omega
  · by_cases hm : m = 0
    · exact Or.inl hm
    · exact Or.inr ⟨b1, by omega⟩

/-- A `Vec` in a kept slot, its buffer allocated since the entry. -/
theorem w9_vec {s w v : MachineState} (hpre : VerifyLayerPre s) (hH : HeapOk w) (hH' : HeapOk v)
    (hN : heapNext w ≤ heapNext v) (F : DFrame w v (W9 s w v)) {a : Word} {xs : List E}
    (ha : Kept s a 24) (hv : NewVecE s w a xs) : NewVecE s v a xs := by
  have hb := bounds hpre
  simp only [Kept] at ha
  have e0 : v.getMem a = w.getMem a := w9_word hpre hH' F (by simp only [Kept]; omega)
  have e1 : v.getMem (a + 8) = w.getMem (a + 8) :=
    w9_word hpre hH' F (by simp only [Kept]; addr_omega [ha, hb])
  have e2 : v.getMem (a + 16) = w.getMem (a + 16) :=
    w9_word hpre hH' F (by simp only [Kept]; addr_omega [ha, hb])
  obtain ⟨⟨hr, hl⟩, hbuf, he⟩ := hv
  have p0 : vecCap v a = vecCap w a := e0
  have p1 : vecPtr v a = vecPtr w a := e1
  have p2 : vecLen v a = vecLen w a := e2
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [RawVecOk, Buf, p0, p1] at hr ⊢
    exact ⟨hr.1, hr.2.imp_right fun h ↦ ⟨h.1, h.2.trans hN⟩⟩
  · rw [p0, p2]; exact hl
  · rw [p0, p1]; exact newBuf_mono hbuf hN
  · rw [← he]
    simp only [vecEs, p1, p2]
    exact w9_eList hpre hH F hbuf (by omega)

/-- What the body keeps of the pack rounds' state: the result's, the claim's, the sponge's and
the transcript's addresses, the instance weights (`mu`), `kappa`, the scale and the point. -/
structure K8 (s w : MachineState) (ip : Word) (c : E) (point : List E) (scale : E) : Prop where
  out : w.getMem (s.getReg .x2 - 1664) = s.getReg .x10
  claim : w.getMem (s.getReg .x2 - 1656) = s.getReg .x15
  sponge : w.getMem (s.getReg .x2 - 1616) = s.getReg .x11 + 8
  p : w.getMem (s.getReg .x2 - 1608) = s.getReg .x11
  ipM : w.getMem (s.getReg .x2 - 1648) = ip
  icap : 16 ≤ (w.getMem (s.getReg .x2 - 1672)).toNat
  ibuf : NewBuf s w ip ((w.getMem (s.getReg .x2 - 1672)).toNat * 24) 8
  iw : eListAt w ip 16 = instanceWeightsRust c
  kappa : eAt w (s.getReg .x2 - 800) = sumE (instanceWeightsRust c)
  scale : eAt w (s.getReg .x2 - 1472) = scale
  ptV : NewVecE s w (s.getReg .x2 - 848) point

theorem K8.keep {s w v : MachineState} {ip : Word} {c : E} {point : List E} {scale : E}
    (hpre : VerifyLayerPre s) (K : K8 s w ip c point scale) (hH : HeapOk w) (hH' : HeapOk v)
    (hN : heapNext w ≤ heapNext v) (F : DFrame w v (W9 s w v)) : K8 s v ip c point scale := by
  have hb := bounds hpre
  have kw (y : Word) (hy : Kept s y 8) : v.getMem y = w.getMem y := w9_word hpre hH' F hy
  have e40 := kw (s.getReg .x2 - 1672) (by simp only [Kept]; addr_omega [hb])
  have e64 := kw (s.getReg .x2 - 1648) (by simp only [Kept]; addr_omega [hb])
  exact {
    out := by rw [kw _ (by simp only [Kept]; addr_omega [hb]), K.out]
    claim := by rw [kw _ (by simp only [Kept]; addr_omega [hb]), K.claim]
    sponge := by rw [kw _ (by simp only [Kept]; addr_omega [hb]), K.sponge]
    p := by rw [kw _ (by simp only [Kept]; addr_omega [hb]), K.p]
    ipM := by rw [e64, K.ipM]
    icap := by rw [e40]; exact K.icap
    ibuf := by rw [e40]; exact newBuf_mono K.ibuf hN
    iw := by rw [w9_eList hpre hH F K.ibuf (by have := K.icap; omega)]; exact K.iw
    kappa := by rw [w9_eAt hpre hH' F (by simp only [Kept]; addr_omega [hb])]; exact K.kappa
    scale := by rw [w9_eAt hpre hH' F (by simp only [Kept]; addr_omega [hb])]; exact K.scale
    ptV := w9_vec hpre hH hH' hN F (by simp only [Kept]; addr_omega [hb]) K.ptV }

theorem k8_of_j8 {s w : MachineState} {ip : Word} {c : E} {acc : E × E × List E}
    (hpre : VerifyLayerPre s) (J : J8 s w ip c acc) : K8 s w ip c acc.2.2 acc.2.1 := by
  have hb := bounds hpre
  have hlo := hpre.heap.lo
  have hm := J.base.mono
  obtain ⟨i1, i2, i3, i4⟩ := J.ibuf
  obtain ⟨p1, p2⟩ := J.ptBuf
  have v0 : vecCap w (s.getReg .x2 - 848) = w.getMem (s.getReg .x2 - 848) := rfl
  have v1 : vecPtr w (s.getReg .x2 - 848) = w.getMem (s.getReg .x2 - 840) := by
    simp only [vecPtr]; rv_eval []
  have v2 : vecLen w (s.getReg .x2 - 848) = w.getMem (s.getReg .x2 - 832) := by
    simp only [vecLen]; rv_eval []
  have hl := J.ptCap
  rw [← J.ptLen] at hl
  exact {
    out := J.out
    claim := J.claim
    sponge := J.sponge
    p := J.p
    ipM := J.ipM
    icap := i3
    ibuf := ⟨i2, Or.inr ⟨i1, by omega⟩⟩
    iw := J.iw
    kappa := J.kappa
    scale := J.scale
    ptV := {
      vec := ⟨by
          simp only [RawVecOk, Buf, v0, v1]
          exact ⟨p1, p2.imp_right fun h ↦ ⟨by omega, h.2⟩⟩,
        by rw [v0, v2]; exact hl⟩
      buf := by
        simp only [NewBuf, v0, v1]
        exact ⟨p1, p2.imp_right fun h ↦ ⟨by omega, h.2⟩⟩
      elems := by rw [vecEs, v1, v2, J.ptLen]; exact J.ptE } }

/-! ## `Err` from a callee -/

/-- `0x8000f9f8`: `sumcheck`'s `Err` (the niche in `s2`, its payload in `s6` and `s1`) into the
result, then return. -/
theorem err_f9f8 {s u : MachineState} (hpre : VerifyLayerPre s) (B : Base s u)
    (hpc : u.pc = 0x8000f9f8) (hout : u.getMem (s.getReg .x2 - 1664) = s.getReg .x10)
    (hx18 : u.getReg .x18 = errNiche) (hf : Fails s) : ∃ t, Reaches Image.code u t ∧ Ret s t := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  have hof := hpre.outFree
  obtain ⟨w, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f9f8_spec hpc (by
    rv_eval [B.x2, hout]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have m0 := b8000f9f8_m2 h₁
  rw [B.x2] at m0
  rv_eval [hout, hx18] at m0
  have f₁ : MemFrame u w (s.getReg .x10) 24 := h₁.memFrame (by
    rv_eval [B.x2, hout]; and_intros <;> addr_omega [ho])
  have x2w : w.getReg .x2 = s.getReg .x2 - 1712 := (b8000f9f8_keeps h₁ .x2 (by decide)).trans B.x2
  have hN : w.getMem nextAddr = u.getMem nextAddr := f₁ _ (by addr_omega [ho, hof])
  have Bw : Base s w := B.next hpre x2w
    ⟨by simp only [heapNext, hN]; exact B.heap.lo, by simp only [heapNext, hN]; exact B.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) (DFrame.of_memFrame f₁) fun a ha ↦
      ⟨Or.inl (by addr_omega [ha]), by unfold verifyLayerStack at hb hos; addr_omega [ha, hos, hb]⟩
  obtain ⟨t, hr₂, pc, pres, same⟩ := exit hpre (b8000f9f8_pc h₁) Bw.x2 Bw.saved
  exact ⟨t, hr₁.trans hr₂, pc, pres, post_err Bw m0 hf same⟩

/-- `[None; 11]` in `.rodata`: `sumcheck`'s equalities. -/
theorem rodata_nones11 {u : MachineState} (h : RodataOk u) :
    optEListAt u 0xa0000cc8 11 = List.replicate 11 none := by
  have h0 : u.getMem 0xa0000cc8 = 0 := h.word
  have h1 : u.getMem 0xa0000ce8 = 0 := h.word
  have h2 : u.getMem 0xa0000d08 = 0 := h.word
  have h3 : u.getMem 0xa0000d28 = 0 := h.word
  have h4 : u.getMem 0xa0000d48 = 0 := h.word
  have h5 : u.getMem 0xa0000d68 = 0 := h.word
  have h6 : u.getMem 0xa0000d88 = 0 := h.word
  have h7 : u.getMem 0xa0000da8 = 0 := h.word
  have h8 : u.getMem 0xa0000dc8 = 0 := h.word
  have h9 : u.getMem 0xa0000de8 = 0 := h.word
  have h10 : u.getMem 0xa0000e08 = 0 := h.word
  simp only [optEListAt, List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, optEAt]
  rw [show (0xa0000cc8 : Word) + BitVec.ofNat 64 (32 * 0) = 0xa0000cc8 from rfl,
    show (0xa0000cc8 : Word) + BitVec.ofNat 64 (32 * 1) = 0xa0000ce8 from rfl,
    show (0xa0000cc8 : Word) + BitVec.ofNat 64 (32 * 2) = 0xa0000d08 from rfl,
    show (0xa0000cc8 : Word) + BitVec.ofNat 64 (32 * 3) = 0xa0000d28 from rfl,
    show (0xa0000cc8 : Word) + BitVec.ofNat 64 (32 * 4) = 0xa0000d48 from rfl,
    show (0xa0000cc8 : Word) + BitVec.ofNat 64 (32 * 5) = 0xa0000d68 from rfl,
    show (0xa0000cc8 : Word) + BitVec.ofNat 64 (32 * 6) = 0xa0000d88 from rfl,
    show (0xa0000cc8 : Word) + BitVec.ofNat 64 (32 * 7) = 0xa0000da8 from rfl,
    show (0xa0000cc8 : Word) + BitVec.ofNat 64 (32 * 8) = 0xa0000dc8 from rfl,
    show (0xa0000cc8 : Word) + BitVec.ofNat 64 (32 * 9) = 0xa0000de8 from rfl,
    show (0xa0000cc8 : Word) + BitVec.ofNat 64 (32 * 10) = 0xa0000e08 from rfl,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  rfl

/-! ## The local sumcheck -/

/-- Back from `sumcheck`, at `0x8000f750`: the local point `lp` and its value `lv`. -/
structure S9 (s v : MachineState) (ip : Word) (c : E) (point : List E) (scale : E)
    (lp : List E) (lv : E) : Prop where
  pc : v.pc = 0x8000f750
  base : Base s v
  k8 : K8 s v ip c point scale
  x18 : v.getReg .x18 = errNiche
  x20 : v.getReg .x20 = s.getReg .x11
  x26 : v.getReg .x26 = 16
  x9 : v.getReg .x9 = v.getMem (s.getReg .x2 - 736)
  x22 : v.getReg .x22 = v.getMem (s.getReg .x2 - 744)
  lpV : NewVecE s v (s.getReg .x2 - 752) lp
  lvE : eAt v (s.getReg .x2 - 728) = lv
  rest : Rest s v (stage5 (claimAt s (lClaim s)) (instanceWeightsRust c)
    (sumE (instanceWeightsRust c)) scale point lp lv)

set_option maxHeartbeats 16000000 in
/-- `0x8000f718`: `sumcheck(value, 4, [None; 11])` into `f + 960`; its `Err` returned. -/
theorem r9_sc (hSC : SumcheckSpec) {s w : MachineState} {ip : Word} {c : E}
    {acc : E × E × List E} (hpre : VerifyLayerPre s) (J : J8 s w ip c acc) :
    ∃ v, Reaches Image.code w v ∧ ((∃ lp lv, S9 s v ip c acc.2.2 acc.2.1 lp lv) ∨ Ret s v ∨
      Dead Image.code v) := by
  have hb := bounds hpre
  have B := J.base
  have K := k8_of_j8 hpre J
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hrs := hpre.stack.rodata
  have hsr := hpre.selfRodata
  simp only [stackLo] at hnx hab hss hrs
  unfold verifyLayerStack at hb hnx hab hsm hss hrs
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f718_spec J.pc trivial
  have k₁ := b8000f718_keeps h₁
  have hm₁ := b8000f718_mem_same h₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ : Base s t₁ := B.same x2₁ hm₁
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 752 := by rw [b8000f718_x10 h₁, B.x2]; rv_eval []
  have x11₁ : t₁.getReg .x11 = s.getReg .x11 := by rw [b8000f718_x11 h₁, J.x20]
  have x12₁ : t₁.getReg .x12 = s.getReg .x2 - 1592 := by rw [b8000f718_x12 h₁, B.x2]; rv_eval []
  have x13₁ := b8000f718_x13 h₁
  have x14₁ := b8000f718_x14 h₁
  have x15₁ := b8000f718_x15 h₁
  have h11 : (t₁.getReg .x15).toNat = 11 := by rw [x15₁]; rfl
  have tp : TPre 48 sumcheckStack t₁ := B₁.tpre hpre 752 x10₁ x11₁ (by decide) (by decide)
    (by decide) (le_refl _) (by decide)
  obtain ⟨r1, r2, -⟩ := readsLW hpre B₁.heap
  have hS8 : (s.getReg .x11).toNat + 8 ≤ 2 ^ 64 := by addr_omega [hS]
  have hP48 : (proofAt s (s.getReg .x11)).toNat + 48 ≤ 2 ^ 64 := by addr_omega [hpre.self.proof]
  have hsp : SumcheckPre t₁ := { tp with
    count := by rw [x13₁]; decide
    claim := by rw [x12₁]; addr_omega [hb, hsm]
    eqs := by rw [h11, x14₁]; right; addr_omega []
    claimFree := by rw [x12₁]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    eqsFree := by rw [h11, x14₁]; right; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega []
    claimStack := by rw [x12₁]; simp only [stackLo, x2₁]; addr_omega [hb]
    eqsStack := by rw [h11, x14₁]; simp only [stackLo, x2₁]; addr_omega [hb, hrs]
    claimSelf := by rw [x12₁, x11₁]; addr_omega [hb, hss, hS]
    eqsSelf := by rw [h11, x14₁, x11₁]; addr_omega [hsr]
    claimOut := by rw [x12₁, x10₁]; addr_omega [hb]
    eqsOut := by rw [h11, x14₁, x10₁]; addr_omega [hb, hrs]
    claimEqs := by rw [h11, x14₁, x12₁]; addr_omega [hb, hrs]
    proofClaim := by
      rw [x11₁, x12₁]
      refine B₁.frame.proofApart r1 hS8 r2 hP48 (Open.ProofApart.mono' hpre.proofStack ?_ ?_) <;>
        addr_omega [hb]
    claimRodata := by rw [x12₁]; addr_omega [hb, hrs] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hp₂, SP⟩ | hd⟩ := hSC.call hr₁ (b8000f718_pc h₁) hsp
  swap
  · exact ⟨_, hr₂, Or.inr (Or.inr hd)⟩
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := (hp₂.reg .x2).trans x2₁
  have B₂ : Base s t₂ := B₁.next hpre x2₂ SP.heap SP.mono SP.frame fun a ha ↦ by
    rcases ha with h | h | h
    · exact tframe_lw hpre B₁ (n := 48) 752 x10₁ x11₁ (by decide) (by decide) (le_refl _)
        SP.heap a (Or.inl h)
    · rw [x12₁] at h; exact slots_lw hpre (by addr_omega [hb]) (by addr_omega [hb]) h
    · exact tframe_lw hpre B₁ (n := 48) 752 x10₁ x11₁ (by decide) (by decide) (le_refl _)
        SP.heap a (Or.inr h)
  have G₂ := SP.frame
  rw [x10₁, x12₁, x11₁] at G₂
  simp only [stackLo, x2₁] at G₂
  have hN₁ : heapNext t₁ = heapNext w := by simp only [heapNext, hm₁]
  have F₂ : DFrame w t₂ (W9 s w t₂) := (DFrame.of_same hm₁ _).trans G₂ fun a h ↦ by
    simp only [W9, Fresh] at h ⊢
    rcases h with h | h | h | h | h | h
    · exact Or.inl (by simp only [Scr9]; addr_omega [h, hb])
    · exact Or.inl (by simp only [Scr9]; addr_omega [h, hb])
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [← hN₁]; exact h.1, h.2⟩)))
  have K₂ : K8 s t₂ ip c acc.2.2 acc.2.1 :=
    K.keep hpre B.heap SP.heap (by rw [← hN₁]; exact SP.mono) F₂
  have R₀ : Rest s w (TM.sumcheck acc.1 4 (List.replicate keccakLocalBits none) >>= fun lv ↦
      stage5 (claimAt s (lClaim s)) (instanceWeightsRust c) (sumE (instanceWeightsRust c))
        acc.2.1 acc.2.2 lv.1 lv.2) := J.rest.congr (stage4_eq _ _ _ _)
  have hnones := rodata_nones11 (B₁.rodata hpre)
  have value₁ : eAt t₁ (s.getReg .x2 - 1592) = acc.1 := by
    rw [show eAt t₁ (s.getReg .x2 - 1592) = eAt w (s.getReg .x2 - 1592) from by
      simp only [Rv64Verifier.eAt, hm₁]]
    exact J.value
  have hv (T : TState) (hT : TranscriptAt w (s.getReg .x11) T) :
      match (TM.sumcheck acc.1 4 (List.replicate keccakLocalBits none)).run T with
      | some ((point, claim), T') => vecCap t₂ (s.getReg .x2 - 752) ≠ errNiche ∧
          NewVecE t₁ t₂ (s.getReg .x2 - 752) point ∧ eAt t₂ (s.getReg .x2 - 752 + 24) = claim ∧
          TranscriptAt t₂ (s.getReg .x11) T'
      | none => vecCap t₂ (s.getReg .x2 - 752) = errNiche := by
    have h := SP.value T (by rw [x11₁]; exact transcriptAt_congr hm₁ hT)
    rw [x12₁, value₁, x13₁, x14₁, h11, hnones, x10₁, x11₁] at h
    exact h
  -- `0x8000f73c`: `Err` or the point
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f73c_spec
    (by rw [hpc₂, returnAddress_eq, b8000f718_x1 h₁]; decide) (by
      rv_eval [x2₂]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b8000f73c_keeps h₃
  have hm₃ := b8000f73c_mem_same h₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have B₃ : Base s t₃ := B₂.same x2₃ hm₃
  have K₃ : K8 s t₃ ip c acc.2.2 acc.2.1 := K₂.keep hpre B₂.heap B₃.heap
    (by simp only [heapNext, hm₃]; exact le_refl _) (DFrame.of_same hm₃ _)
  have cap₂ : t₂.getMem (t₂.getReg .x2 + 960) = t₂.getMem (s.getReg .x2 - 752) := by
    rw [x2₂]; rv_eval []
  by_cases herr : t₂.getMem (s.getReg .x2 - 752) = errNiche
  · have hf : Fails s := R₀.fail fun T hT ↦ by
      have e := hv T hT
      generalize (TM.sumcheck acc.1 4 (List.replicate keccakLocalBits none)).run T = o at e ⊢
      rcases o with _ | ⟨⟨pt, cv⟩, T'⟩
      · rfl
      · exact absurd herr e.1
    obtain ⟨t, hr, ht⟩ := err_f9f8 hpre B₃ (b8000f73c_pc_taken h₃ (by rw [cap₂]; exact herr))
      (by rw [hm₃]; exact K₂.out) (b8000f73c_x18 h₃) hf
    exact ⟨t, hr₂.trans (hr₃.trans hr), Or.inr (Or.inl ht)⟩
  obtain ⟨T₀, hT₀⟩ := Open.exists_T w (s.getReg .x11)
  have h₀ := hv T₀ hT₀
  generalize (TM.sumcheck acc.1 4 (List.replicate keccakLocalBits none)).run T₀ = o at h₀
  rcases o with _ | ⟨⟨lp, lv⟩, T₀'⟩
  · exact absurd h₀ herr
  obtain ⟨-, hlp, hlv, -⟩ := h₀
  have hp24 : s.getReg .x2 - 752 + 24 = s.getReg .x2 - 728 := by rv_eval []
  refine ⟨t₃, hr₂.trans hr₃, Or.inl ⟨lp, lv, {
    pc := b8000f73c_pc_not_taken h₃ (by rw [cap₂]; exact herr)
    base := B₃
    k8 := K₃
    x18 := b8000f73c_x18 h₃
    x20 := by rw [k₃ .x20 (by decide), hp₂.reg .x20, k₁ .x20 (by decide), J.x20]
    x26 := by rw [k₃ .x26 (by decide), hp₂.reg .x26, k₁ .x26 (by decide), J.x26]
    x9 := by rw [b8000f73c_x9 h₃, x2₂, hm₃]; rv_eval []
    x22 := by rw [b8000f73c_x22 h₃, x2₂, hm₃]; rv_eval []
    lpV := newVecE_congr hm₃ (Open.newVecE_mono hlp B₁.mono)
    lvE := by rw [← hlv, hp24]; simp only [Rv64Verifier.eAt, hm₃]
    rest := R₀.step (x := (lp, lv)) fun T hT ↦ by
      have h := hv T hT
      generalize (TM.sumcheck acc.1 4 (List.replicate keccakLocalBits none)).run T = o at h ⊢
      rcases o with _ | ⟨⟨pt, cv⟩, T'⟩
      · exact absurd h herr
      obtain ⟨-, hpt, hcv, hT'⟩ := h
      have e1 : pt = lp := hpt.elems.symm.trans hlp.elems
      have e2 : cv = lv := hcv.symm.trans hlv
      subst e1 e2
      exact ⟨T', rfl, transcriptAt_congr hm₃ hT'⟩ }⟩⟩

end Rv64Verifier.Gkr.Layer
