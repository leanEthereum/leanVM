import Rv64Verifier.Proofs.Gkr.KeccakEntry
import Rv64Verifier.Proofs.Multilinear.Contracts

/-!
# `keccak::verify_keccak`: the first claim's point, the lanes, the weights' buffer

`[&instance[4..], &segment].concat()` into `f + 104` (`to_point`), `samples(5)` into `f + 1952`
(`to_lanePoint`), `eq_kernel` of it into `f + 128` (`to_lanes`), the weights' buffer of 1600
elements allocated and reserved into `f + 416` (`to_wbuf`).
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F35 Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- A `Vec` allocated since `s`: its elements in the heap, below `NEXT`. -/
theorem vec_inHeap {s u : MachineState} {a : Word} {xs : List E} (h : NewVecE s u a xs) :
    (vecLen u a).toNat = 0 ∨ (heapNext s ≤ (vecPtr u a).toNat ∧
      (vecPtr u a).toNat + 24 * (vecLen u a).toNat ≤ heapNext u ∧ (vecPtr u a).toNat % 8 = 0) := by
  have hl := h.vec.len
  have hb := h.buf
  simp only [NewBuf] at hb
  rcases hb with ⟨h8, h0 | hb⟩
  · left; omega
  · right; refine ⟨hb.1, by omega, h8⟩

/-- Its elements are a region outside the free heap, apart from the stack, the frame and the
transcript. -/
structure Heaped (s u : MachineState) (p : Word) (n : Nat) : Prop where
  region : Region p n
  outside : Outside u p n
  above : ∀ lo m, heapEnd ≤ lo.toNat → Apart p n lo m
  self : Apart p n (s.getReg .x11 + 8) 344

theorem vec_heaped {s u : MachineState} (hpre : VerifyKeccakPreW s) (B : Base s u) {a : Word}
    {xs : List E} (h : NewVecE s u a xs) :
    (vecLen u a).toNat = 0 ∨ Heaped s u (vecPtr u a) (24 * (vecLen u a).toNat) := by
  have hhi := B.heap.hi
  have hlo := hpre.heap.lo
  have hS := hpre.self.self
  obtain ⟨f1, f2⟩ := hpre.selfFree
  rcases vec_inHeap h with h0 | ⟨h1, h2, h3⟩
  · exact Or.inl h0
  · right
    exact ⟨by addr_omega [h1, h2, h3, hhi, hlo], ⟨Or.inl h2, by addr_omega [h2, hhi]⟩,
      fun lo m hl ↦ by addr_omega [h2, hhi, hl], by addr_omega [h1, h2, hhi, f1, hS]⟩

/-- Back from the point's `concat`: the point at `f + 104`. -/
structure A2 (s u : MachineState) (seg : List E) : Prop where
  pc : u.pc = 0x80008fb8
  base : Base s u
  ok : OK s
  x8 : u.getReg .x8 = s.getReg .x11
  x9 : u.getReg .x9 = s.getReg .x14
  x18 : u.getReg .x18 = s.getReg .x12
  x19 : u.getReg .x19 = 12
  x23 : u.getReg .x23 = vecPtr u (s.getReg .x2 - 5168)
  x24 : u.getReg .x24 = vecLen u (s.getReg .x2 - 5168)
  m32 : u.getMem (s.getReg .x2 - 5216) = s.getReg .x12 - 4
  m40 : u.getMem (s.getReg .x2 - 5208) = s.getReg .x16
  m48 : u.getMem (s.getReg .x2 - 5200) = s.getReg .x10
  m56 : u.getMem (s.getReg .x2 - 5192) = s.getReg .x14
  m64 : u.getMem (s.getReg .x2 - 5184) = 2
  segV : NewVecE s u (s.getReg .x2 - 5168) seg
  segLen : seg.length = 1
  pointV : NewVecE s u (s.getReg .x2 - 5144) ((instOf s).drop 4 ++ seg)
  rest : Rest s u (kSeg (s.getReg .x12).toNat (instOf s) (outOf s) seg)

theorem to_point (hC : SliceConcatSpec) {s u : MachineState} (hpre : VerifyKeccakPreW s)
    (A : A1 s u) : ∃ v, Reaches Image.code u v ∧
      (A2 s v (vecEs u (s.getReg .x2 - 5168)) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have B := A.base
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008f7c_spec A.pc (by
    rv_eval [B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b80008f7c_keeps h₁
  have F₁ : DFrame u u₁ (Slots s [(3296, 32), (5216, 8), (5192, 8)]) := block_slots h₁ (by
    intro k hk
    simp only [b80008f7c, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h | h | h | h | h <;> subst h <;> rv_eval [B.x2] <;>
      exact slots_of hpre (by decide))
  have B₁ := B.block hpre ((k₁ .x2 (by decide)).trans B.x2) (by decide) F₁
  have m1952 := b80008f7c_m_x2_1952 h₁
  have m1960 := b80008f7c_m_x2_1960 h₁
  have m1968 := b80008f7c_m_x2_1968 h₁
  have m1976 := b80008f7c_m_x2_1976 h₁
  rw [B.x2] at m1952 m1960 m1968 m1976
  rv_eval [A.x9, A.x18] at m1952 m1960 m1968 m1976
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 5144 := by rw [b80008f7c_x10 h₁, B.x2]; rv_eval []
  have x11₁ : u₁.getReg .x11 = s.getReg .x2 - 3296 := by rw [b80008f7c_x11 h₁, B.x2]; rv_eval []
  have x12₁ : u₁.getReg .x12 = 2 := b80008f7c_x12 h₁
  -- the segment's `Vec` and the instance, unchanged by the block
  have hseg : NewVecE s u₁ (s.getReg .x2 - 5168) (vecEs u (s.getReg .x2 - 5168)) :=
    SW.vec hpre B B₁.heap (le_of_eq (by simp only [heapNext, slots_next hpre (by decide) F₁]))
      (by decide) (by decide) (by decide) (by decide) (slots_sw F₁) A.seg
  have hN₁ : heapNext u₁ = heapNext u := by simp only [heapNext, slots_next hpre (by decide) F₁]
  have keep₁ (J : Nat) (hJ : J ≤ 5248) (h8 : 8 ≤ J)
      (hsep : SlotsSep [(3296, 32), (5216, 8), (5192, 8)] J 8 = true) :=
    SW.mem hpre B₁.heap (by decide) hJ h8 hsep (slots_sw F₁)
  have eptr : vecPtr u₁ (s.getReg .x2 - 5168) = u.getMem (s.getReg .x2 - 5160) := by
    simp only [vecPtr]
    rw [show s.getReg .x2 - 5168 + 8 = s.getReg .x2 - 5160 by ring]; exact keep₁ 5160 (by decide) (by decide) (by decide)
  have elen : vecLen u₁ (s.getReg .x2 - 5168) = u.getMem (s.getReg .x2 - 5152) := by
    simp only [vecLen]
    rw [show s.getReg .x2 - 5168 + 16 = s.getReg .x2 - 5152 by ring]; exact keep₁ 5152 (by decide) (by decide) (by decide)
  have hlen1 : (vecLen u₁ (s.getReg .x2 - 5168)).toNat = 1 := by
    have := A.segLen
    rw [← hseg.elems] at this
    simpa only [vecEs, eListAt_length] using this
  have hok := A.ok
  have hl := hok.2
  have hinst : kInstLen s = (s.getReg .x12).toNat := by simp only [kInstLen, hok.1]
  have hl4 : (s.getReg .x12 - 4).toNat = (s.getReg .x12).toNat - 4 := by
    rw [BitVec.toNat_sub]; simp only [Sym.wordToNatLit]; omega
  have hst : RtStack u₁ sliceConcatStack := hpre.stack.sub 5248 B₁.x2
    (by unfold verifyKeccakStack; decide) (by decide) (by decide) (by decide) (by decide)
  have p0 : partPtr u₁ 0 = s.getReg .x14 + 96 := by
    simp only [partPtr, x11₁]
    rw [show s.getReg .x2 - 3296 + BitVec.ofNat 64 (16 * 0) = s.getReg .x2 - 3296 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb])]; exact m1952
  have l0 : partLen u₁ 0 = (s.getReg .x12).toNat - 4 := by
    simp only [partLen, x11₁]
    rw [show s.getReg .x2 - 3296 + BitVec.ofNat 64 (16 * 0) + 8 = s.getReg .x2 - 3288 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb]), m1960, hl4]
  have p1 : partPtr u₁ 1 = vecPtr u₁ (s.getReg .x2 - 5168) := by
    simp only [partPtr, x11₁]
    rw [show s.getReg .x2 - 3296 + BitVec.ofNat 64 (16 * 1) = s.getReg .x2 - 3280 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb]), m1968, eptr]
  have l1 : partLen u₁ 1 = 1 := by
    simp only [partLen, x11₁]
    rw [show s.getReg .x2 - 3296 + BitVec.ofNat 64 (16 * 1) + 8 = s.getReg .x2 - 3272 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb]), m1976, ← elen, hlen1]
  have hiR := hpre.inst
  have hiF := hpre.instFree.resolve_left (by rw [hinst]; have := hok.2; omega)
  have hiS := hpre.instStack
  rw [hinst] at hiR hiF hiS
  simp only [kInst] at hiR hiF hiS
  have hcp : SliceConcatPre u₁ := {
    heap := B₁.heap
    out := by rw [x10₁]; addr_omega [hb, hsm]
    count := by rw [x12₁]; decide
    slices := by rw [x11₁, x12₁]; addr_omega [hb, hsm]
    stack := hst
    outFree := by
      rw [x10₁]; have hab := hpre.stack.above; have hnx := hpre.stack.next
      refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    outStack := by rw [x10₁]; simp only [stackLo, B₁.x2]; addr_omega [hb]
    slicesFree := by
      rw [x11₁, x12₁]; have hab := hpre.stack.above; have hnx := hpre.stack.next
      refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    slicesStack := by rw [x11₁, x12₁]; simp only [stackLo, B₁.x2]; addr_omega [hb]
    slicesOut := by rw [x11₁, x12₁, x10₁]; addr_omega [hb]
    part := by
      intro i hi
      rw [x12₁] at hi
      have hi' : i < 2 := hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [p0, l0]
        by_cases h4 : (s.getReg .x12).toNat = 4
        · left; omega
        right
        rcases hiR with h0 | hR
        · omega
        have hm := B₁.mono
        obtain ⟨f1, f2⟩ := hiF
        refine ⟨by addr_omega [hR, hl], ⟨by addr_omega [hR, hl, f1, hm], by addr_omega [hR, hl, f2]⟩,
          ?_, ?_⟩
        · simp only [stackLo, B₁.x2]; unfold verifyKeccakStack at hb hiS; addr_omega [hR, hl, hiS, hb]
        · rw [x10₁]; unfold verifyKeccakStack at hb hiS; addr_omega [hR, hl, hiS, hb]
      · rw [p1, l1]
        right
        rcases vec_heaped hpre B₁ hseg with h0 | H
        · omega
        rw [hlen1] at H
        refine ⟨H.region, H.outside, ?_, ?_⟩
        · simp only [stackLo, B₁.x2]; have hab := hpre.stack.above
          exact H.above _ _ (by unfold verifyKeccakStack at hb hab; addr_omega [hb, hab])
        · rw [x10₁]; have hab := hpre.stack.above
          exact H.above _ _ (by unfold verifyKeccakStack at hb hab; addr_omega [hb, hab]) }
  obtain ⟨v, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hC.call (hr₁) (b80008f7c_pc h₁) hcp
  swap
  · exact ⟨v, hr₂, Or.inr hd⟩
  have x2₂ : v.getReg .x2 = s.getReg .x2 - 5248 := (hpres₂.reg .x2).trans B₁.x2
  have F₂ : DFrame u₁ v (SW s u₁ v [(5144, 24)] false) := DFrame.mono hpost₂.frame
    fun a ha ↦ cframe_sw hpre 5144 B₁.x2 x10₁ (by decide) a ha
  have B₂ := B₁.step hpre x2₂ hpost₂.heap hpost₂.mono (by decide) F₂
  have keep₂ (J : Nat) (hJ : J ≤ 5248) (h8 : 8 ≤ J) (hsep : SlotsSep [(5144, 24)] J 8 = true) :=
    SW.mem hpre hpost₂.heap (by decide) hJ h8 hsep F₂
  have hval := hpost₂.value
  have hparts : (parts u₁).flatten = eListAt u₁ (partPtr u₁ 0) (partLen u₁ 0) ++
      eListAt u₁ (partPtr u₁ 1) (partLen u₁ 1) := by
    simp [parts, x12₁, List.range_succ]
  have e0 : eListAt u₁ (partPtr u₁ 0) (partLen u₁ 0) = (instOf s).drop 4 := by
    rw [p0, l0, instOf, Open.eListAt_drop, kInst, kInstLen, hok.1]
    by_cases h4 : (s.getReg .x12).toNat = 4
    · rw [h4]; rfl
    rcases hiR with h0 | hR
    · omega
    have hm := missInst hpre B₁.heap
    rw [hinst] at hm
    simp only [kInst] at hm
    exact B₁.eListAt (fun y hy ↦ hm y (by addr_omega [hy, hR, hl])) (Or.inr (by addr_omega [hR, hl]))
  have e1 : eListAt u₁ (partPtr u₁ 1) (partLen u₁ 1) = vecEs u (s.getReg .x2 - 5168) := by
    rw [p1, l1, ← hseg.elems, vecEs, hlen1]
  rw [hparts, e0, e1, x10₁] at hval
  refine ⟨v, hr₂, Or.inl {
    pc := by rw [hpc₂, returnAddress_eq, b80008f7c_x1 h₁]; decide
    base := B₂
    ok := hok
    x8 := by rw [hpres₂.reg .x8, k₁ .x8 (by decide), A.x8]
    x9 := by rw [hpres₂.reg .x9, k₁ .x9 (by decide), A.x9]
    x18 := by rw [hpres₂.reg .x18, k₁ .x18 (by decide), A.x18]
    x19 := by rw [hpres₂.reg .x19, k₁ .x19 (by decide), A.x19]
    x23 := by
      rw [hpres₂.reg .x23, b80008f7c_x23 h₁, B.x2]; simp only [vecPtr]
      rw [show s.getReg .x2 - 5248 + 88 = s.getReg .x2 - 5160 by ring,
        show s.getReg .x2 - 5168 + 8 = s.getReg .x2 - 5160 by ring]
      exact ((keep₂ 5160 (by decide) (by decide) (by decide)).trans
        (keep₁ 5160 (by decide) (by decide) (by decide))).symm
    x24 := by
      rw [hpres₂.reg .x24, b80008f7c_x24 h₁, B.x2]; simp only [vecLen]
      rw [show s.getReg .x2 - 5248 + 96 = s.getReg .x2 - 5152 by ring,
        show s.getReg .x2 - 5168 + 16 = s.getReg .x2 - 5152 by ring]
      exact ((keep₂ 5152 (by decide) (by decide) (by decide)).trans
        (keep₁ 5152 (by decide) (by decide) (by decide))).symm
    m32 := (keep₂ 5216 (by decide) (by decide) (by decide)).trans (by
      have := b80008f7c_m_x2_32 h₁; rw [B.x2, A.x18] at this; rv_eval [] at this; exact this)
    m40 := (keep₂ 5208 (by decide) (by decide) (by decide)).trans
      ((keep₁ 5208 (by decide) (by decide) (by decide)).trans A.m40)
    m48 := (keep₂ 5200 (by decide) (by decide) (by decide)).trans
      ((keep₁ 5200 (by decide) (by decide) (by decide)).trans A.m48)
    m56 := (keep₂ 5192 (by decide) (by decide) (by decide)).trans (by
      have := b80008f7c_m_x2_56 h₁; rw [B.x2, A.x9] at this; rv_eval [] at this; exact this)
    m64 := (keep₂ 5184 (by decide) (by decide) (by decide)).trans
      ((keep₁ 5184 (by decide) (by decide) (by decide)).trans A.m64)
    segV := SW.vec hpre B₁ hpost₂.heap hpost₂.mono (by decide) (by decide) (by decide) (by decide)
      F₂ hseg
    segLen := A.segLen
    pointV := Open.newVecE_mono hval B₁.mono
    rest := (A.rest.keep fun T hT ↦ B.block_tat hpre (by decide) F₁ hT).keep fun T hT ↦
      SW.tat hpre B₁ hpost₂.heap hpost₂.mono (by decide) F₂ hT }⟩

/-! ## What every later step keeps -/

theorem seg8 {s : MachineState} (hpre : VerifyKeccakPreW s) :
    s.getReg .x2 - 5168 + 8 = s.getReg .x2 - 5160 := by
  have hb := bounds hpre; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])

theorem seg16 {s : MachineState} (hpre : VerifyKeccakPreW s) :
    s.getReg .x2 - 5168 + 16 = s.getReg .x2 - 5152 := by
  have hb := bounds hpre; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])

/-- The frame's spills, the segment's and the point's `Vec`s: the 96 bytes from `f + 32`. -/
structure M (s u : MachineState) (seg : List E) : Prop where
  base : Base s u
  ok : OK s
  m32 : u.getMem (s.getReg .x2 - 5216) = s.getReg .x12 - 4
  m40 : u.getMem (s.getReg .x2 - 5208) = s.getReg .x16
  m48 : u.getMem (s.getReg .x2 - 5200) = s.getReg .x10
  m56 : u.getMem (s.getReg .x2 - 5192) = s.getReg .x14
  m64 : u.getMem (s.getReg .x2 - 5184) = 2
  m72 : u.getMem (s.getReg .x2 - 5176) = s.getReg .x11
  segV : NewVecE s u (s.getReg .x2 - 5168) seg
  segLen : seg.length = 1
  pointV : NewVecE s u (s.getReg .x2 - 5144) ((instOf s).drop 4 ++ seg)

/-- With the callee-saved registers that hold the transcript, the instance, the shape and the
segment's `Vec`. -/
structure C (s u : MachineState) (seg : List E) : Prop extends M s u seg where
  x8 : u.getReg .x8 = s.getReg .x11
  x9 : u.getReg .x9 = s.getReg .x14
  x18 : u.getReg .x18 = s.getReg .x12
  x19 : u.getReg .x19 = 12
  x23 : u.getReg .x23 = vecPtr u (s.getReg .x2 - 5168)
  x24 : u.getReg .x24 = vecLen u (s.getReg .x2 - 5168)

theorem M.step {s u v : MachineState} {seg : List E} (hpre : VerifyKeccakPreW s) (c : M s u seg)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) (hH : HeapOk v) (hN : heapNext u ≤ heapNext v)
    {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true)
    (hsep : SlotsSep rs 5216 96 = true) (F : DFrame u v (SW s u v rs sp)) : M s v seg := by
  have B := c.base
  have km (J : Nat) (h1 : J ≤ 5216) (h2 : 5128 ≤ J) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 J) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 J) :=
    SW.mem hpre hH hok (by omega) (by omega) (SlotsSep.sub hsep h1 (by omega)) F
  have kv (J : Nat) (h1 : J ≤ 5216) (h2 : 5144 ≤ J) {xs : List E}
      (h : NewVecE s u (s.getReg .x2 - BitVec.ofNat 64 J) xs) :
      NewVecE s v (s.getReg .x2 - BitVec.ofNat 64 J) xs :=
    SW.vec hpre B hH hN hok (by omega) (by omega) (SlotsSep.sub hsep h1 (by omega)) F h
  exact {
    base := B.step hpre hx2 hH hN hok F
    ok := c.ok
    m32 := (km 5216 (by decide) (by decide)).trans c.m32
    m40 := (km 5208 (by decide) (by decide)).trans c.m40
    m48 := (km 5200 (by decide) (by decide)).trans c.m48
    m56 := (km 5192 (by decide) (by decide)).trans c.m56
    m64 := (km 5184 (by decide) (by decide)).trans c.m64
    m72 := (km 5176 (by decide) (by decide)).trans c.m72
    segV := kv 5168 (by decide) (by decide) c.segV
    segLen := c.segLen
    pointV := kv 5144 (by decide) (by decide) c.pointV }

theorem C.step {s u v : MachineState} {seg : List E} (hpre : VerifyKeccakPreW s) (c : C s u seg)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) (hH : HeapOk v) (hN : heapNext u ≤ heapNext v)
    {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true)
    (hsep : SlotsSep rs 5216 96 = true) (F : DFrame u v (SW s u v rs sp))
    (hregs : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x23, .x24] : List Reg), v.getReg r = u.getReg r) :
    C s v seg := by
  have km (J : Nat) (h1 : J ≤ 5216) (h2 : 5128 ≤ J) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 J) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 J) :=
    SW.mem hpre hH hok (by omega) (by omega) (SlotsSep.sub hsep h1 (by omega)) F
  have e8 : v.getMem (s.getReg .x2 - 5160) = u.getMem (s.getReg .x2 - 5160) :=
    km 5160 (by decide) (by decide)
  have e16 : v.getMem (s.getReg .x2 - 5152) = u.getMem (s.getReg .x2 - 5152) :=
    km 5152 (by decide) (by decide)
  have a8 := seg8 hpre
  have a16 := seg16 hpre
  exact { c.toM.step hpre hx2 hH hN hok hsep F with
    x8 := (hregs .x8 (by decide)).trans c.x8
    x9 := (hregs .x9 (by decide)).trans c.x9
    x18 := (hregs .x18 (by decide)).trans c.x18
    x19 := (hregs .x19 (by decide)).trans c.x19
    x23 := by rw [hregs .x23 (by decide), c.x23]; simp only [vecPtr, a8, e8]
    x24 := by rw [hregs .x24 (by decide), c.x24]; simp only [vecLen, a16, e16] }

/-- Back from `samples(5)`: the lanes' point at `f + 1952`. -/
structure A3 (s u : MachineState) (seg lp : List E) : Prop extends C s u seg where
  pc : u.pc = 0x80008fd0
  lpV : NewVecE s u (s.getReg .x2 - 3296) lp
  lpLen : lp.length = 5
  rest : Rest s u (kLanes (s.getReg .x12).toNat (instOf s) (outOf s) seg lp)

theorem to_lanePoint (hS : SamplesSpec) {s u : MachineState} {seg : List E}
    (hpre : VerifyKeccakPreW s) (A : A2 s u seg) : ∃ v, Reaches Image.code u v ∧
      (A3 s v seg (vecEs v (s.getReg .x2 - 3296)) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := A.base
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008fb8_spec A.pc (by
    rv_eval [B.x2]
    valid_access hpre.stack.valid [hb])
  have k₁ := b80008fb8_keeps h₁
  have F₁ : DFrame u u₁ (Slots s [(5176, 8)]) := block_slots h₁ (by
    intro k hk
    simp only [b80008fb8, List.mem_cons, List.not_mem_nil, or_false] at hk
    subst hk; rv_eval [B.x2]; exact slots_of hpre (by decide))
  have hN₁ : heapNext u₁ = heapNext u := by simp only [heapNext, slots_next hpre (by decide) F₁]
  have B₁ := B.block hpre ((k₁ .x2 (by decide)).trans B.x2) (by decide) F₁
  have keep₁ (J : Nat) (hJ : J ≤ 5248) (h8 : 8 ≤ J) (hsep : SlotsSep [(5176, 8)] J 8 = true) :=
    SW.mem hpre B₁.heap (by decide) hJ h8 hsep (slots_sw F₁)
  have kv₁ (J : Nat) (hJ : J ≤ 5248) (h24 : 24 ≤ J) (hsep : SlotsSep [(5176, 8)] J 24 = true)
      {xs : List E} (h : NewVecE s u (s.getReg .x2 - BitVec.ofNat 64 J) xs) :=
    SW.vec hpre B B₁.heap (le_of_eq hN₁.symm) (by decide) hJ h24 hsep (slots_sw F₁) h
  have c₁ : C s u₁ seg := {
    base := B₁
    ok := A.ok
    x8 := (k₁ .x8 (by decide)).trans A.x8
    x9 := (k₁ .x9 (by decide)).trans A.x9
    x18 := (k₁ .x18 (by decide)).trans A.x18
    x19 := (k₁ .x19 (by decide)).trans A.x19
    x23 := by
      rw [k₁ .x23 (by decide), A.x23]; simp only [vecPtr, seg8 hpre]
      exact (keep₁ 5160 (by decide) (by decide) (by decide)).symm
    x24 := by
      rw [k₁ .x24 (by decide), A.x24]; simp only [vecLen, seg16 hpre]
      exact (keep₁ 5152 (by decide) (by decide) (by decide)).symm
    m32 := (keep₁ 5216 (by decide) (by decide) (by decide)).trans A.m32
    m40 := (keep₁ 5208 (by decide) (by decide) (by decide)).trans A.m40
    m48 := (keep₁ 5200 (by decide) (by decide) (by decide)).trans A.m48
    m56 := (keep₁ 5192 (by decide) (by decide) (by decide)).trans A.m56
    m64 := (keep₁ 5184 (by decide) (by decide) (by decide)).trans A.m64
    m72 := by
      have := b80008fb8_m_x2_72 h₁; rw [B.x2, A.x8] at this; rv_eval [] at this; exact this
    segV := kv₁ 5168 (by decide) (by decide) (by decide) A.segV
    segLen := A.segLen
    pointV := kv₁ 5144 (by decide) (by decide) (by decide) A.pointV }
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 3296 := by rw [b80008fb8_x10 h₁, B.x2]; rv_eval []
  have x11₁ : u₁.getReg .x11 = s.getReg .x11 := by rw [b80008fb8_x11 h₁, A.x8]
  have hsp : SamplesPre u₁ := B₁.tpre hpre 3296 x10₁ x11₁ (by decide) (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨v, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hS.call hr₁ (b80008fb8_pc h₁) hsp
  swap
  · exact ⟨v, hr₂, Or.inr hd⟩
  have x2₂ : v.getReg .x2 = s.getReg .x2 - 5248 := (hpres₂.reg .x2).trans B₁.x2
  have F₂ : DFrame u₁ v (SW s u₁ v [(3296, 24)] true) := DFrame.mono hpost₂.frame
    fun a ha ↦ tframe_sw hpre 3296 B₁.x2 x10₁ x11₁ (by decide) a ha
  have c₂ := c₁.step hpre x2₂ hpost₂.heap hpost₂.mono (by decide) (by decide) F₂ fun r hr ↦
    hpres₂.reg r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                     rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have R₁ := A.rest.keep fun T hT ↦ B.block_tat hpre (by decide) F₁ hT
  obtain ⟨T₀, hT₀⟩ := Open.exists_T u₁ (s.getReg .x11)
  obtain ⟨xs₀, T₀', hrun₀, hvec₀, -⟩ := hpost₂.value T₀ (by rw [x11₁]; exact hT₀)
  rw [x10₁] at hvec₀
  have hx12 : (u₁.getReg .x12).toNat = 5 := by rw [b80008fb8_x12 h₁]; rfl
  rw [hx12] at hrun₀
  have hlp := hvec₀.elems
  refine ⟨v, hr₂, Or.inl { c₂ with
    pc := by rw [hpc₂, returnAddress_eq, b80008fb8_x1 h₁]; decide
    lpV := by rw [hlp]; exact Open.newVecE_mono hvec₀ B₁.mono
    lpLen := by rw [hlp]; exact Returns.samples _ _ _ _ hrun₀
    rest := R₁.step fun T hT ↦ ?_ }⟩
  obtain ⟨xs, T', hrun, hvec, hT'⟩ := hpost₂.value T (by rw [x11₁]; exact hT)
  rw [x10₁] at hvec
  rw [hx12] at hrun
  rw [x11₁] at hT'
  exact ⟨T', by rw [hvec.elems]; exact hrun, hT'⟩

/-- Back from `eq_kernel`: the lanes' weights at `f + 128`. -/
structure A4 (s u : MachineState) (seg lp : List E) : Prop extends C s u seg where
  pc : u.pc = 0x80008fe4
  lanesV : NewVecE s u (s.getReg .x2 - 5120) (eqKernelRust lp)
  lpLen : lp.length = 5
  rest : Rest s u (kLanes (s.getReg .x12).toNat (instOf s) (outOf s) seg lp)

theorem callee_saved_mem {r : Reg}
    (hr : r ∈ ([.x8, .x9, .x18, .x19, .x23, .x24] : List Reg)) : r ∈ calleeSaved := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem to_lanes (hEK : EqKernelSpec) {s u : MachineState} {seg lp : List E}
    (hpre : VerifyKeccakPreW s) (A : A3 s u seg lp) : ∃ v, Reaches Image.code u v ∧
      (A4 s v seg lp ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have B := A.base
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008fd0_spec A.pc (by
    rv_eval [B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b80008fd0_keeps h₁
  have m₁ := b80008fd0_mem_same h₁
  have c₁ : C s u₁ seg := A.toC.step hpre ((k₁ .x2 (by decide)).trans B.x2)
    ⟨by simp only [heapNext, m₁]; exact B.heap.lo, by simp only [heapNext, m₁]; exact B.heap.hi⟩
    (by simp only [heapNext, m₁]; exact le_refl _) (rs := []) (sp := false) (by decide) (by decide)
    (DFrame.of_same m₁ _) fun r hr ↦ k₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have B₁ := c₁.base
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 5120 := by rw [b80008fd0_x10 h₁, B.x2]; rv_eval []
  have x11₁ : u₁.getReg .x11 = vecPtr u (s.getReg .x2 - 3296) := by
    rw [b80008fd0_x11 h₁, B.x2]; simp only [vecPtr]
    rw [show s.getReg .x2 - 5248 + 1960 = s.getReg .x2 - 3296 + 8 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb])]
  have x12₁ : u₁.getReg .x12 = vecLen u (s.getReg .x2 - 3296) := by
    rw [b80008fd0_x12 h₁, B.x2]; simp only [vecLen]
    rw [show s.getReg .x2 - 5248 + 1968 = s.getReg .x2 - 3296 + 16 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb])]
  have hlen : (vecLen u (s.getReg .x2 - 3296)).toNat = 5 := by
    have := A.lpLen; rw [← A.lpV.elems] at this; simpa only [vecEs, eListAt_length] using this
  have H : Heaped s u (vecPtr u (s.getReg .x2 - 3296)) (24 * 5) := by
    rcases vec_heaped hpre B A.lpV with h0 | H
    · omega
    · rw [hlen] at H; exact H
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  unfold verifyKeccakStack at hb hab hrs
  have hek : EqKernelPre u₁ := {
    heap := B₁.heap
    out := by rw [x10₁]; addr_omega [hb, hsm]
    point := by rw [x11₁, x12₁, hlen]; exact Or.inr H.region
    stack := hpre.stack.sub 5248 B₁.x2 (by unfold verifyKeccakStack; decide) (by decide)
      (by decide) (by decide) (by decide)
    outFree := by
      rw [x10₁]; have hnx := hpre.stack.next; unfold verifyKeccakStack at hnx
      refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    pointFree := by
      rw [x11₁, x12₁, hlen]; right
      exact Open.outside_mono H.outside (by simp only [heapNext, m₁]; exact le_refl _)
    outStack := by rw [x10₁]; simp only [stackLo, B₁.x2]; addr_omega [hb]
    pointStack := by
      rw [x11₁, x12₁, hlen]; simp only [stackLo, B₁.x2]
      exact H.above _ _ (by addr_omega [hb, hab])
    pointOut := by rw [x11₁, x12₁, hlen, x10₁]; exact H.above _ _ (by addr_omega [hb, hab])
    rodata := B₁.rodata hpre
    outRodata := by rw [x10₁]; addr_omega [hb, hrs] }
  obtain ⟨v, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hEK.call hr₁ (b80008fd0_pc h₁) hek
  swap
  · exact ⟨v, hr₂, Or.inr hd⟩
  have x2₂ : v.getReg .x2 = s.getReg .x2 - 5248 := (hpres₂.reg .x2).trans B₁.x2
  have F₂ : DFrame u₁ v (SW s u₁ v [(5120, 24)] false) := DFrame.mono hpost₂.frame
    fun a ha ↦ cframe_sw hpre 5120 B₁.x2 x10₁ (by decide) a ha
  have c₂ := c₁.step hpre x2₂ hpost₂.heap hpost₂.mono (by decide) (by decide) F₂ fun r hr ↦
    hpres₂.reg r (callee_saved_mem hr)
  have hval := hpost₂.value
  have hel : eListAt u₁ (u₁.getReg .x11) (u₁.getReg .x12).toNat = lp := by
    rw [x11₁, x12₁, ← A.lpV.elems, vecEs]
    exact (DFrame.of_same m₁ (fun _ ↦ False)).eListAt fun _ _ h ↦ h
  rw [hel, x10₁] at hval
  refine ⟨v, hr₂, Or.inl { c₂ with
    pc := by rw [hpc₂, returnAddress_eq, b80008fd0_x1 h₁]; decide
    lanesV := Open.newVecE_mono hval B₁.mono
    lpLen := A.lpLen
    rest := (A.rest.keep fun T hT ↦ Layer.transcriptAt_congr m₁ hT).keep fun T hT ↦
      SW.tat hpre B₁ hpost₂.heap hpost₂.mono (by decide) F₂ hT }⟩

theorem trap : Image.code.fetch 0x80009750 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

/-- The weights' buffer reserved: 1600 elements at `f + 416`, none written. -/
structure A5 (s u : MachineState) (seg lp : List E) : Prop extends C s u seg where
  pc : u.pc = 0x8000901c
  x20 : u.getReg .x20 = 1600
  lanesV : NewVecE s u (s.getReg .x2 - 5120) (eqKernelRust lp)
  lpLen : lp.length = 5
  rest : Rest s u (kLanes (s.getReg .x12).toNat (instOf s) (outOf s) seg lp)
  cap : u.getMem (s.getReg .x2 - 4832) = 1600
  len : u.getMem (s.getReg .x2 - 4816) = 0
  wbuf : NewBuf s u (u.getMem (s.getReg .x2 - 4824)) 38400 8
  segW : Apart (vecPtr u (s.getReg .x2 - 5168))
    ((vecCap u (s.getReg .x2 - 5168)).toNat * 24) (u.getMem (s.getReg .x2 - 4824)) 38400
  pointW : Apart (vecPtr u (s.getReg .x2 - 5144))
    ((vecCap u (s.getReg .x2 - 5144)).toNat * 24) (u.getMem (s.getReg .x2 - 4824)) 38400
  lanesW : Apart (vecPtr u (s.getReg .x2 - 5120))
    ((vecCap u (s.getReg .x2 - 5120)).toNat * 24) (u.getMem (s.getReg .x2 - 4824)) 38400

theorem hdr_keep {u v : MachineState} {w : Word → Prop} (F : DFrame u v w) {a : Word}
    (hm : Misses w a 24) (ha : a.toNat + 24 ≤ 2 ^ 64) :
    vecPtr v a = vecPtr u a ∧ vecCap v a = vecCap u a := by
  refine ⟨F _ (hm.bytes (by addr_omega [ha]) (by addr_omega [ha]) ha),
    F _ (hm.bytes (Nat.le_refl _) (by omega) ha)⟩

/-- A buffer allocated by `u` lies below what is allocated after it. -/
theorem below_apart {s u : MachineState} {a p : Word} {xs : List E} (h : NewVecE s u a xs)
    (hp : heapNext u ≤ p.toNat) (n : Nat) :
    Apart (vecPtr u a) ((vecCap u a).toNat * 24) p n := by
  have := h.buf
  simp only [NewBuf] at this
  simp only [Apart]
  omega

theorem to_wbuf (hA : AllocSpec) (hR : ReserveFastSpec 0x80008a10) {s u : MachineState}
    {seg lp : List E} (hpre : VerifyKeccakPreW s) (A : A4 s u seg lp) :
    ∃ v, Reaches Image.code u v ∧ (A5 s v seg lp ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := A.base
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008fe4_spec A.pc trivial
  have k₁ := b80008fe4_keeps h₁
  have m₁ := b80008fe4_mem_same h₁
  have hap : AllocPre u₁ := ⟨⟨by simp only [heapNext, m₁]; exact B.heap.lo,
    by simp only [heapNext, m₁]; exact B.heap.hi⟩, by rw [b80008fe4_x10 h₁]; decide⟩
  obtain ⟨v, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hA.call hr₁ (b80008fe4_pc h₁) hap
  swap
  · exact ⟨v, hr₂, Or.inr hd⟩
  have hN₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have hab := hpost₂.above
  have hnext := hpost₂.next
  rw [b80008fe4_x11 h₁] at hnext
  have hal := hpost₂.aligned
  rw [b80008fe4_x10 h₁] at hal
  have hlo := hpre.heap.lo
  have hmono := B.mono
  have x2₂ : v.getReg .x2 = s.getReg .x2 - 5248 :=
    (hpres₂.reg .x2).trans ((k₁ .x2 (by decide)).trans B.x2)
  have hne : v.getReg .x10 ≠ 0 := fun h ↦ by
    rw [h] at hab; simp only [heapStart] at hlo; rw [hN₁] at hab
    have : (0 : Word).toNat = 0 := rfl
    omega
  obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008ff8_spec
    (by rw [hpc₂, returnAddress_eq, b80008fe4_x1 h₁]; decide) trivial
  have pc₃ := b80008ff8_pc_not_taken h₃ hne
  have k₃ := b80008ff8_keeps h₃
  have m₃ := b80008ff8_mem_same h₃
  have x2₃ : v₃.getReg .x2 = s.getReg .x2 - 5248 := (k₃ .x2 (by decide)).trans x2₂
  obtain ⟨v₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80008ffc_spec pc₃ (by
    rv_eval [x2₃]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₄ := b80008ffc_keeps h₄
  have F₄ : DFrame v₃ v₄ (Slots s [(4832, 24)]) := by
    have f := b80008ffc_frame h₄ (by rw [x2₃]; addr_omega [hb])
    rw [x2₃] at f
    rv_eval [] at f
    exact (DFrame.of_memFrame f).mono fun a ha ↦ ⟨(4832, 24), List.mem_singleton_self _, ha⟩
  have hN₄ : v₄.getMem nextAddr = v₃.getMem nextAddr := slots_next hpre (by decide) F₄
  have x2₄ : v₄.getReg .x2 = s.getReg .x2 - 5248 := (k₄ .x2 (by decide)).trans x2₃
  have x10₄ : v₄.getReg .x10 = s.getReg .x2 - 4832 := by rw [b80008ffc_x10 h₄, x2₃]; rv_eval []
  have m416 : v₄.getMem (s.getReg .x2 - 4832) = 1600 := by
    have := b80008ffc_m_x2_416 h₄; rw [x2₃] at this; rv_eval [] at this; exact this
  have m424 : v₄.getMem (s.getReg .x2 - 4824) = v.getReg .x10 := by
    have := b80008ffc_m_x2_424 h₄; rw [x2₃, k₃ .x10 (by decide)] at this; rv_eval [] at this
    exact this
  have m432 : v₄.getMem (s.getReg .x2 - 4816) = 0 := by
    have := b80008ffc_m_x2_432 h₄; rw [x2₃] at this; rv_eval [] at this; exact this
  have hrp : ValidMemRange (v₄.getReg .x10) 3 ∧ (vecLen v₄ (v₄.getReg .x10)).toNat +
      (v₄.getReg .x11).toNat ≤ (vecCap v₄ (v₄.getReg .x10)).toNat := by
    refine ⟨by rw [x10₄]; exact slot_vmr hpre (by decide) (by decide) (by decide), ?_⟩
    rw [x10₄, b80008ffc_x11 h₄]
    simp only [vecLen, vecCap]
    rw [show s.getReg .x2 - 4832 + 16 = s.getReg .x2 - 4816 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb]), m432, m416]
    decide
  obtain ⟨w, hr₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hd⟩ := hR.call hr₄ (b80008ffc_pc h₄) hrp
  swap
  · exact ⟨w, hr₂.trans (hr₃.trans hr₅), Or.inr hd⟩
  have m₅ := hpost₅.2
  have hNw : heapNext w = heapNext v := by simp only [heapNext, m₅, hN₄, m₃]
  have hHw : HeapOk w := ⟨by rw [hNw]; exact hpost₂.heap.lo, by rw [hNw]; exact hpost₂.heap.hi⟩
  have hNuw : heapNext u ≤ heapNext w := by rw [hNw, hnext, ← hN₁]; omega
  -- everything from `u` to `w`
  have Ft : DFrame u w (SW s u w [(4832, 24)] false) := by
    intro a ha
    rw [m₅, F₄ a fun i hi h ↦ ha i hi (Or.inl h), m₃, hpost₂.mem a fun h ↦ ha 0 (by decide)
      (Or.inr (Or.inr (Or.inl (by rw [add_ofNat_zero, h]; simp only [Within]; omega)))), m₁]
  have regs : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x23, .x24] : List Reg), w.getReg r = u.getReg r :=
    fun r hr ↦ by
      have hc := callee_saved_mem hr
      rw [hpres₅.reg r hc, k₄ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp), k₃ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp), hpres₂.reg r hc, k₁ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
  have x2w : w.getReg .x2 = s.getReg .x2 - 5248 := (hpres₅.reg .x2).trans x2₄
  have cw := A.toC.step hpre x2w hHw hNuw (by decide) (by decide) Ft regs
  have kv (J : Nat) (hJ : J ≤ 5248) (h24 : 24 ≤ J) (hsep : SlotsSep [(4832, 24)] J 24 = true)
      {xs : List E} (h : NewVecE s u (s.getReg .x2 - BitVec.ofNat 64 J) xs) :=
    SW.vec hpre B hHw hNuw (by decide) hJ h24 hsep Ft h
  have hk (J : Nat) (hJ : J ≤ 5248) (h24 : 24 ≤ J) (hsep : SlotsSep [(4832, 24)] J 24 = true) :=
    hdr_keep Ft (SW.slot hpre hHw (by decide) hJ h24 hsep) (by addr_omega [hb, hJ])
  have hptr : w.getMem (s.getReg .x2 - 4824) = v.getReg .x10 := (m₅ _).trans m424
  have hpv : heapNext u ≤ (v.getReg .x10).toNat := by rw [← hN₁]; exact hab
  refine ⟨w, hr₂.trans (hr₃.trans hr₅), Or.inl { cw with
    pc := by rw [hpc₅, returnAddress_eq, b80008ffc_x1 h₄]; decide
    x20 := by rw [hpres₅.reg .x20, b80008ffc_x20 h₄]
    lanesV := kv 5120 (by decide) (by decide) (by decide) A.lanesV
    lpLen := A.lpLen
    rest := A.rest.keep fun T hT ↦ SW.tat hpre B hHw hNuw (by decide) Ft hT
    cap := (m₅ _).trans m416
    len := (m₅ _).trans m432
    wbuf := by
      rw [hptr]
      simp only [NewBuf, hNw, hnext]
      exact ⟨hal, Or.inr ⟨by omega, le_refl _⟩⟩
    segW := by
      obtain ⟨e1, e2⟩ := hk 5168 (by decide) (by decide) (by decide)
      rw [show vecPtr w (s.getReg .x2 - 5168) = vecPtr u (s.getReg .x2 - 5168) from e1,
        show vecCap w (s.getReg .x2 - 5168) = vecCap u (s.getReg .x2 - 5168) from e2, hptr]; exact below_apart A.segV hpv _
    pointW := by
      obtain ⟨e1, e2⟩ := hk 5144 (by decide) (by decide) (by decide)
      rw [show vecPtr w (s.getReg .x2 - 5144) = vecPtr u (s.getReg .x2 - 5144) from e1,
        show vecCap w (s.getReg .x2 - 5144) = vecCap u (s.getReg .x2 - 5144) from e2, hptr]; exact below_apart A.pointV hpv _
    lanesW := by
      obtain ⟨e1, e2⟩ := hk 5120 (by decide) (by decide) (by decide)
      rw [show vecPtr w (s.getReg .x2 - 5120) = vecPtr u (s.getReg .x2 - 5120) from e1,
        show vecCap w (s.getReg .x2 - 5120) = vecCap u (s.getReg .x2 - 5120) from e2, hptr]; exact below_apart A.lanesV hpv _ }⟩

end Rv64Verifier.Gkr.Keccak
