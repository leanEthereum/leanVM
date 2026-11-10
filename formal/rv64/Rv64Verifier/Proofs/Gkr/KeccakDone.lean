import Rv64Verifier.Proofs.Gkr.KeccakEnd

/-!
# `keccak::verify_keccak`: the result

The point's bound (`point[..l - 4]`, a trap when it is shorter), the inputs' point `concat` into
the result, the slices and the outputs stored after it, the exit (`to_done`).
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F35 Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem cap_ne {s u : MachineState} {a : Word} {xs : List E} (h : NewVecE s u a xs)
    (hu : HeapOk u) : vecCap u a ≠ errNiche := by
  intro hc
  have h1 := h.vec.raw
  have h2 := hu.hi
  simp only [RawVecOk, Buf, hc] at h1
  rw [show errNiche.toNat = 18446744073709551615 from rfl] at h1
  simp only [heapEnd] at h2
  omega

theorem HB.take {s u : MachineState} {p n : Word} {xs : List E} (h : HB s u p n xs) (k : Word)
    (hk : k.toNat ≤ n.toNat) : HB s u p k (xs.take k.toNat) := by
  have hb := h.buf
  simp only [NewBuf] at hb
  refine ⟨by simp only [NewBuf]; omega, by rw [← h.elems, eListAt_take _ _ hk], ?_⟩
  by_cases hz : k.toNat = 0
  · exact Or.inl hz
  rcases h.reg with h0 | ⟨hR, hA⟩
  · omega
  · exact Or.inr ⟨by addr_omega [hR, hk], fun lo m hl ↦ by have := hA lo m hl; addr_omega [this, hk]⟩

theorem newVecE_of {s u : MachineState} {a c p n : Word} {xs : List E} (hv : VB s u c p n)
    (he : eListAt u p n.toNat = xs) (e0 : u.getMem a = c) (e8 : u.getMem (a + 8) = p)
    (e16 : u.getMem (a + 16) = n) : NewVecE s u a xs := by
  have c0 : vecCap u a = c := e0
  have c8 : vecPtr u a = p := e8
  have c16 : vecLen u a = n := e16
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [RawVecOk, c0, c8]; exact h1
  · rw [c16, c0]; exact h2
  · rw [c0, c8]; exact h3
  · rw [vecEs, c8, c16]; exact he

/-- Back from the inputs' `concat` at `0x8000964c`. -/
structure D3 (s u : MachineState) (o : KeccakOpenings) (word : E) (oc op on sc sp sn : Word) :
    Prop where
  base : Base s u
  pc : u.pc = 0x8000964c
  x8 : u.getReg .x8 = s.getReg .x10
  x18 : u.getReg .x18 = sc
  x20 : u.getReg .x20 = sp
  x22 : u.getReg .x22 = sn
  x25 : u.getReg .x25 = (Model.limbs word).2.1
  x26 : u.getReg .x26 = (Model.limbs word).1
  m40 : u.getMem (s.getReg .x2 - 5208) = (Model.limbs word).2.2
  m56 : u.getMem (s.getReg .x2 - 5192) = oc
  m400 : u.getMem (s.getReg .x2 - 4848) = op
  m408 : u.getMem (s.getReg .x2 - 4840) = on
  oVB : VB s u oc op on
  oHB : HB s u op on (match o.outputs with | some (pt, _) => pt | none => [])
  sVB : VB s u sc sp sn
  sHB : HB s u sp sn o.inputs.2
  inV : NewVecE s u (s.getReg .x10) o.inputs.1
  rest : Rest s u (pure o)

theorem to_done (hC : SliceConcatSpec) {s u : MachineState} {cl : KeccakClaim} {oslot : List E}
    {word : E} {lp ll : Word} {low : List E} {qp ql : Word} {slot2 : List E} {sc sp sn : Word}
    {slices : List E} (hpre : VerifyKeccakPre s)
    (A : K2 s u cl oslot word lp ll low qp ql slot2 sc sp sn slices) :
    ∃ t, Reaches Image.code u t ∧ ((∃ oc op on, D3 s t ⟨some (instOf s ++ oslot, word),
      (low ++ cl.point.take ((s.getReg .x12).toNat - 4) ++ slot2, slices)⟩ word oc op on sc sp sn) ∨
        Done s t) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have B := A.base
  have ho := hpre.out
  have hos := hpre.outStack
  have hof := hpre.outFree
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have a2 (n : Nat) (hn : n ≤ 5248) :
      s.getReg .x2 - 5248 + BitVec.ofNat 64 n = s.getReg .x2 - BitVec.ofNat 64 (5248 - n) :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hn])
  have ptB := HB.of_vec hpre B A.claim.point
  simp only [vecPtr, vecLen, show s.getReg .x2 - 4952 + 24 + 8 = s.getReg .x2 - 4920 from
    BitVec.eq_of_toNat_eq (by addr_omega [hb]), show s.getReg .x2 - 4952 + 24 + 16 = s.getReg .x2 - 4912 from
    BitVec.eq_of_toNat_eq (by addr_omega [hb])] at ptB
  -- 0x80009610: `point[..l - 4]`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009610_spec A.pc (by
    rv_eval [B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b80009610_keeps h₁
  have m₁ := b80009610_mem_same h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 5248 := (k₁ .x2 (by decide)).trans B.x2
  have l336 : u.getMem (u.getReg .x2 + 336) = u.getMem (s.getReg .x2 - 4912) := by
    rw [B.x2]; exact congrArg _ (a2 336 (by decide))
  have l32 : u.getMem (u.getReg .x2 + 32) = s.getReg .x12 - 4 := by
    rw [B.x2, show s.getReg .x2 - 5248 + 32 = s.getReg .x2 - 5216 from a2 32 (by decide)]
    exact A.m32
  have hl := A.ok.2
  have hl4 : (s.getReg .x12 - 4).toNat = (s.getReg .x12).toNat - 4 := by
    rw [BitVec.toNat_sub]; simp only [Sym.wordToNatLit]; omega
  by_cases hlt : (u.getMem (s.getReg .x2 - 4912)).toNat < (s.getReg .x12 - 4).toNat
  · have pc₁ := b80009610_pc_taken h₁ (by rw [l336, l32]; exact hlt)
    exact ⟨u₁, hr₁, Or.inr (Or.inr (dead_of_fetch (by rw [pc₁]; exact trap)))⟩
  have pc₁ := b80009610_pc_not_taken h₁ (by rw [l336, l32]; omega)
  have hle : (s.getReg .x12 - 4).toNat ≤ (u.getMem (s.getReg .x2 - 4912)).toNat := by omega
  -- 0x8000961c: the three parts, `concat` into the result
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000961c_spec pc₁ (by
    rv_eval [x2₁]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₂ := b8000961c_keeps h₂
  have x2₂ : u₂.getReg .x2 = s.getReg .x2 - 5248 := (k₂ .x2 (by decide)).trans x2₁
  have F₂ : DFrame u₁ u₂ (Slots s [(3296, 48)]) := by
    have f := b8000961c_frame h₂ (by rw [x2₁]; addr_omega [hb])
    rw [x2₁] at f
    rv_eval [] at f
    exact (DFrame.of_memFrame f).mono fun a ha ↦ ⟨(3296, 48), List.mem_singleton_self _, ha⟩
  have hN₂ := slots_next hpre (by decide) F₂
  have hH₂ : HeapOk u₂ :=
    ⟨by simp only [heapNext, hN₂, m₁]; exact B.heap.lo, by simp only [heapNext, hN₂, m₁]; exact B.heap.hi⟩
  have hle₂ : heapNext u ≤ heapNext u₂ := by simp only [heapNext, hN₂, m₁]; exact le_refl _
  have R₂ := (A.toR3.same hpre x2₁ m₁ (k₁ .x25 (by decide)) (k₁ .x26 (by decide))).step hpre x2₂
    hH₂ (by simp only [heapNext, hN₂]; exact le_refl _) (by decide) (by decide) (by decide)
    (by decide) (slots_sw F₂) (k₂ .x25 (by decide)) (k₂ .x26 (by decide))
  have B₂ := R₂.base
  have hB2 (p n : Word) (xs : List E) (h : HB s u p n xs) : HB s u₂ p n xs :=
    (HB.same m₁ h).step hpre (B.same x2₁ m₁) (by decide) (slots_sw F₂)
      (by simp only [heapNext, hN₂]; exact le_refl _)
  have st (n K : Nat) (hn : n + K = 5248) (x : Word)
      (h : u₂.getMem (u₁.getReg .x2 + BitVec.ofNat 64 n) = x) :
      u₂.getMem (s.getReg .x2 - BitVec.ofNat 64 K) = x := by
    rw [x2₁, a2 n (by omega), show 5248 - n = K by omega] at h; exact h
  have x10₂ : u₂.getReg .x10 = s.getReg .x10 := by
    rw [b8000961c_x10 h₂, k₁ .x8 (by decide), A.x8]
  have x11₂ : u₂.getReg .x11 = s.getReg .x2 - 3296 := by rw [b8000961c_x11 h₂, x2₁]; rv_eval []
  have x12₂ : u₂.getReg .x12 = 3 := b8000961c_x12 h₂
  have pa (i K : Nat) (hK : K + 16 * i = 3296) :
      s.getReg .x2 - 3296 + BitVec.ofNat 64 (16 * i) = s.getReg .x2 - BitVec.ofNat 64 K :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hK])
  have pl (i K : Nat) (hK : K + 16 * i + 8 = 3296) :
      s.getReg .x2 - 3296 + BitVec.ofNat 64 (16 * i) + 8 = s.getReg .x2 - BitVec.ofNat 64 K :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hK])
  have p0 : partPtr u₂ 0 = lp := by
    simp only [partPtr, x11₂]
    rw [pa 0 3296 rfl, st 1952 3296 rfl _ (b8000961c_m_x2_1952 h₂), k₁ .x24 (by decide), A.x24]
  have l0 : partLen u₂ 0 = ll.toNat := by
    simp only [partLen, x11₂]
    rw [pl 0 3288 rfl, st 1960 3288 rfl _ (b8000961c_m_x2_1960 h₂), k₁ .x21 (by decide), A.x21]
  have p1 : partPtr u₂ 1 = u.getMem (s.getReg .x2 - 4920) := by
    simp only [partPtr, x11₂]
    rw [pa 1 3280 rfl, st 1968 3280 rfl _ (b8000961c_m_x2_1968 h₂), m₁, x2₁]
    exact congrArg _ (a2 328 (by decide))
  have l1 : partLen u₂ 1 = (s.getReg .x12 - 4).toNat := by
    simp only [partLen, x11₂]
    rw [pl 1 3272 rfl, st 1976 3272 rfl _ (b8000961c_m_x2_1976 h₂), b80009610_x11 h₁, l32]
  have p2 : partPtr u₂ 2 = qp := by
    simp only [partPtr, x11₂]
    rw [pa 2 3264 rfl, st 1984 3264 rfl _ (b8000961c_m_x2_1984 h₂), k₁ .x27 (by decide), A.x27]
  have l2 : partLen u₂ 2 = ql.toNat := by
    simp only [partLen, x11₂]
    rw [pl 2 3256 rfl, st 1992 3256 rfl _ (b8000961c_m_x2_1992 h₂), k₁ .x19 (by decide), A.x19]
  have lowB := hB2 _ _ _ A.lowB
  have ptB₂ := (hB2 _ _ _ ptB).take (s.getReg .x12 - 4) hle
  have slotB := hB2 _ _ _ A.slotB
  have hhi := hH₂.hi
  obtain ⟨f1, f2⟩ := Open.outside_mono hof B₂.mono
  obtain ⟨g1, -⟩ := hof
  have hst : RtStack u₂ sliceConcatStack := hpre.stack.sub 5248 x2₂
    (by unfold verifyKeccakStack; decide) (by decide) (by decide) (by decide) (by decide)
  have stc : heapEnd ≤ (stackLo u₂ sliceConcatStack).toNat := by
    simp only [stackLo, x2₂]; unfold verifyKeccakStack at hb hab; addr_omega [hb, hab]
  have hpart {p n : Word} {xs : List E} (h : HB s u₂ p n xs) : n.toNat = 0 ∨
      (Region p (24 * n.toNat) ∧ Outside u₂ p (24 * n.toNat) ∧
        Apart p (24 * n.toNat) (stackLo u₂ sliceConcatStack) sliceConcatStack ∧
        Apart p (24 * n.toNat) (s.getReg .x10) 24) := by
    by_cases hz : n.toNat = 0
    · exact Or.inl hz
    right
    rcases h.reg with h0 | ⟨hR, -⟩
    · omega
    have hbuf := h.buf
    simp only [NewBuf] at hbuf
    have hm := B.mono
    refine ⟨hR, h.outside hH₂ hz, h.apart stc, ?_⟩
    rcases g1 with g1 | g1 <;> addr_omega [hbuf, g1, hhi, ho, hm]
  unfold verifyKeccakStack at hb hsm hab hnx hos
  have hcp : SliceConcatPre u₂ := {
    heap := hH₂
    out := by rw [x10₂]; addr_omega [ho]
    count := by rw [x12₂]; decide
    slices := by rw [x11₂, x12₂]; addr_omega [hb, hsm]
    stack := hst
    outFree := by rw [x10₂]; exact ⟨by omega, by addr_omega [f2]⟩
    outStack := by rw [x10₂]; simp only [stackLo, x2₂]; addr_omega [hos, hb]
    slicesFree := by rw [x11₂, x12₂]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    slicesStack := by rw [x11₂, x12₂]; simp only [stackLo, x2₂]; addr_omega [hb]
    slicesOut := by rw [x11₂, x12₂, x10₂]; addr_omega [hos, hb]
    part := by
      intro i hi
      rw [x12₂] at hi
      have hi' : i < 3 := hi
      rw [x10₂]
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · rw [p0, l0]; exact hpart lowB
      · rw [p1, l1]; exact hpart ptB₂
      · rw [p2, l2]; exact hpart slotB }
  obtain ⟨u₃, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hd⟩ := hC.call (hr₁.trans hr₂) (b8000961c_pc h₂) hcp
  swap
  · exact ⟨u₃, hr₃, Or.inr (Or.inr hd)⟩
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 5248 := (hpres₃.reg .x2).trans x2₂
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hos' := hpre.outSelf
  obtain ⟨sf1, sf2⟩ := hpre.selfFree
  unfold verifyKeccakStack at hss
  -- what `concat` writes: the result's header, its stack, `NEXT`, what it allocates
  have hW (a : Word) (ha : Within a (u₂.getReg .x10) 24 ∨
      Within a (stackLo u₂ sliceConcatStack) sliceConcatStack ∨ Within a nextAddr 8 ∨ Fresh u₂ u₃ a) :
      KW s u₃ a ∧ ¬ Within a (s.getReg .x2 - 104) 104 ∧ ¬ Within a (s.getReg .x11) 368 := by
    rw [x10₂] at ha
    have hm := B₂.mono
    have h3 := hpost₃.mono
    have hhi3 := hpost₃.heap.hi
    rcases ha with h | h | h | h
    · exact ⟨Or.inl (by addr_omega [h]), by addr_omega [h, hos, hb], by addr_omega [h, hos']⟩
    · have h' := stk_sw hpre x2₂ (k := sliceConcatStack) (by decide) h
      have := SW.kw hpre B₂ hpost₃.heap hpost₃.mono (rs := []) (sp := false) (by decide)
        (Or.inr (Or.inl h'))
      exact ⟨this.1, this.2, by unfold verifyKeccakStack at h'; addr_omega [h', hss, hb]⟩
    · have := SW.kw hpre B₂ hpost₃.heap hpost₃.mono (rs := []) (sp := false) (by decide)
        (Or.inr (Or.inr (Or.inl h)))
      exact ⟨this.1, this.2, by addr_omega [h, sf2]⟩
    · have := SW.kw hpre B₂ hpost₃.heap hpost₃.mono (rs := []) (sp := false) (by decide)
        (Or.inr (Or.inr (Or.inr (Or.inl h))))
      simp only [Fresh] at h
      exact ⟨this.1, this.2, by rcases sf1 with sf1 | sf1 <;> addr_omega [h, sf1, hm, hS, hhi3]⟩
  have B₃ := B₂.next hpre x2₃ hpost₃.heap hpost₃.mono hpost₃.frame fun a ha ↦
    ⟨(hW a ha).1, (hW a ha).2.1⟩
  have T₃ (T : TState) (hT : TranscriptAt u₂ (s.getReg .x11) T) : TranscriptAt u₃ (s.getReg .x11) T :=
    B₂.tat hpre hpost₃.heap hpost₃.frame (fun a ha ↦ ⟨(hW a ha).2.2, (hW a ha).1⟩) hT
  -- old buffers and frame slots are kept by `concat`
  have kc (y : Word) (hy : ∀ a, Within a y 8 → ¬ (Within a (u₂.getReg .x10) 24 ∨
      Within a (stackLo u₂ sliceConcatStack) sliceConcatStack ∨ Within a nextAddr 8 ∨
        Fresh u₂ u₃ a)) (hy8 : y.toNat + 8 ≤ 2 ^ 64) : u₃.getMem y = u₂.getMem y :=
    hpost₃.frame y fun i hi h ↦ hy _ (by addr_omega [hi, hy8]) h
  have kslot (J : Nat) (hJ : 128 ≤ J) (hJ' : J ≤ 5248) :
      u₃.getMem (s.getReg .x2 - BitVec.ofNat 64 J) = u₂.getMem (s.getReg .x2 - BitVec.ofNat 64 J) := by
    refine kc _ (fun a ha h ↦ ?_) (by addr_omega [hb, hJ'])
    have hm := B₂.mono
    have h3 := hpost₃.mono
    rw [x10₂] at h
    rcases h with h | h | h | h
    · addr_omega [ha, h, hos, hb, hJ, hJ']
    · simp only [stackLo, x2₂] at h; addr_omega [ha, h, hb, hJ, hJ']
    · addr_omega [ha, h, hnx, hb, hJ, hJ']
    · simp only [Fresh] at h; have := hpost₃.heap.hi; addr_omega [ha, h, hab, hb, hJ, hJ', this]
  have kbuf {p n : Word} {xs : List E} (h : HB s u₂ p n xs) : HB s u₃ p n xs := by
    have hbuf := h.buf
    simp only [NewBuf] at hbuf
    refine ⟨by simp only [NewBuf]; have := hpost₃.mono; omega, ?_, h.reg⟩
    rw [← h.elems]
    by_cases hz : n.toNat = 0
    · rw [hz]; rfl
    have hm := B₂.mono
    have hhi2 := hH₂.hi
    rcases h.reg with h0 | ⟨hR, hA⟩
    · omega
    have hst' := hA _ sliceConcatStack stc
    exact hpost₃.frame.eListAt fun i hi hw ↦ by
      rw [x10₂] at hw
      rcases hw with hw | hw | hw | hw
      · rcases g1 with g1 | g1 <;> addr_omega [hw, hi, hbuf, g1, hhi2, hm]
      · addr_omega [hw, hi, hst', hbuf, hhi2]
      · addr_omega [hw, hi, hbuf, hhi2]
      · simp only [Fresh] at hw; addr_omega [hw, hi, hbuf]
  have x8₃ : u₃.getReg .x8 = s.getReg .x10 := by
    rw [hpres₃.reg .x8, k₂ .x8 (by decide), k₁ .x8 (by decide), A.x8]
  have hval := hpost₃.value
  have hparts : (parts u₂).flatten = eListAt u₂ (partPtr u₂ 0) (partLen u₂ 0) ++
      (eListAt u₂ (partPtr u₂ 1) (partLen u₂ 1) ++ eListAt u₂ (partPtr u₂ 2) (partLen u₂ 2)) := by
    simp [parts, x12₂, List.range_succ]
  rw [hparts, p0, l0, p1, l1, p2, l2, lowB.elems, ptB₂.elems, slotB.elems, hl4, x10₂,
    ← List.append_assoc] at hval
  have oV := R₂.outV
  have f3 (K : Nat) (hK : 128 ≤ K) (hK' : K ≤ 5248) :
      u₃.getMem (s.getReg .x2 - BitVec.ofNat 64 K) = u₂.getMem (s.getReg .x2 - BitVec.ofNat 64 K) :=
    kslot K hK hK'
  refine ⟨u₃, hr₃, Or.inl ⟨_, _, _, {
    base := B₃
    pc := by rw [hpc₃, returnAddress_eq, b8000961c_x1 h₂]; decide
    x8 := x8₃
    x18 := by rw [hpres₃.reg .x18, k₂ .x18 (by decide), k₁ .x18 (by decide), A.x18]
    x20 := by rw [hpres₃.reg .x20, k₂ .x20 (by decide), k₁ .x20 (by decide), A.x20]
    x22 := by rw [hpres₃.reg .x22, k₂ .x22 (by decide), k₁ .x22 (by decide), A.x22]
    x25 := by rw [hpres₃.reg .x25, R₂.x25]
    x26 := by rw [hpres₃.reg .x26, R₂.x26]
    m40 := (f3 5208 (by decide) (by decide)).trans R₂.m40
    m56 := (f3 5192 (by decide) (by decide)).trans R₂.m56
    m400 := (f3 4848 (by decide) (by decide)).trans (by
      simp only [vecPtr]
      exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb])))
    m408 := (f3 4840 (by decide) (by decide)).trans (by
      simp only [vecLen]
      exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb])))
    oVB := (⟨oV.vec.raw, oV.vec.len, oV.buf⟩ : VB s u₂ _ _ _).mono hpost₃.mono
    oHB := kbuf (HB.of_vec hpre B₂ oV)
    sVB := A.slicesV.mono (hle₂.trans hpost₃.mono)
    sHB := kbuf (hB2 _ _ _ A.slicesB)
    inV := Open.newVecE_mono hval B₂.mono
    rest := ((A.rest.keep fun T hT ↦ Layer.transcriptAt_congr m₁ hT).keep fun T hT ↦
      (B.same x2₁ m₁).block_tat hpre (by decide) F₂ hT).keep T₃ }⟩⟩

theorem finish {s u : MachineState} {pt inp sl : List E} {word : E} {oc op on sc sp sn : Word}
    (hpre : VerifyKeccakPre s) (A : D3 s u ⟨some (pt, word), (inp, sl)⟩ word oc op on sc sp sn) :
    ∃ t, Reaches Image.code u t ∧ Done s t := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  have hos' := hpre.outSelf
  obtain ⟨g1, g2⟩ := hpre.outFree
  have B₃ := A.base
  have a2 (n : Nat) (hn : n ≤ 5248) :
      s.getReg .x2 - 5248 + BitVec.ofNat 64 n = s.getReg .x2 - BitVec.ofNat 64 (5248 - n) :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hn])
  unfold verifyKeccakStack at hb hos
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000964c_spec A.pc (by
      rv_eval [B₃.x2, A.x8]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho])
        | addr_omega [hos, hb, ho])
  have k₄ := b8000964c_keeps h₄
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 5248 := (k₄ .x2 (by decide)).trans B₃.x2
  have f₄ : MemFrame u u₄ (s.getReg .x10 + 24) 72 := by
    have f := b8000964c_frame h₄ (by rw [A.x8]; addr_omega [ho])
    rw [A.x8] at f
    exact f
  have hN₄ : u₄.getMem nextAddr = u.getMem nextAddr := f₄ _ (by addr_omega [ho, g2])
  have hH₄ : HeapOk u₄ := ⟨by simp only [heapNext, hN₄]; exact B₃.heap.lo,
    by simp only [heapNext, hN₄]; exact B₃.heap.hi⟩
  have hle₄ : heapNext u ≤ heapNext u₄ := by simp only [heapNext, hN₄]; exact le_refl _
  have B₄ := B₃.next hpre x2₄ hH₄ hle₄ (DFrame.of_memFrame f₄) fun a ha ↦
    ⟨Or.inl (by addr_omega [ha, ho]), by addr_omega [ha, hos, hb, ho]⟩
  have ob (k : Nat) (x : Word) (h : u₄.getMem (u.getReg .x8 + BitVec.ofNat 64 k) = x) :
      u₄.getMem (s.getReg .x10 + BitVec.ofNat 64 k) = x := by
    rw [A.x8] at h; exact h
  have fr (n K : Nat) (hn : n + K = 5248) :
      u.getMem (u.getReg .x2 + BitVec.ofNat 64 n) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 K) := by
    rw [B₃.x2, a2 n (by omega), show 5248 - n = K by omega]
  have hm := B₃.mono
  have hhi := B₃.heap.hi
  have hb4 {p n : Word} {xs : List E} (h : HB s u p n xs) : eListAt u₄ p n.toNat = xs := by
    have hbuf := h.buf
    simp only [NewBuf] at hbuf
    rw [← h.elems]
    by_cases hz : n.toNat = 0
    · rw [hz]; rfl
    exact (DFrame.of_memFrame f₄).eListAt fun i hi hw ↦ by
      rcases g1 with g1 | g1 <;> addr_omega [hw, hi, hbuf, g1, hhi, hm, ho]
  have h0 : NewVecE s u₄ (s.getReg .x10) inp := by
    have hb' := A.inV.buf
    simp only [NewBuf] at hb'
    refine newVecE_step A.inV (DFrame.of_memFrame f₄) hle₄ (fun y hy h ↦ by addr_omega [hy, h, ho])
      (by addr_omega [ho]) (fun y hy h ↦ ?_) hhi
    rcases hb' with ⟨-, hb0 | hb'⟩
    · simp only [Within, hb0] at hy; omega
    · rcases g1 with g1 | g1 <;> addr_omega [hy, h, hb', g1, hm, hhi, ho]
  have h24 : NewVecE s u₄ (s.getReg .x10 + 24) sl :=
    newVecE_of (A.sVB.mono hle₄) (hb4 A.sHB)
      (by rw [← A.x18]; exact ob 24 _ (b8000964c_m_x8_24 h₄))
      (by
        rw [← A.x20, show s.getReg .x10 + 24 + 8 = s.getReg .x10 + BitVec.ofNat 64 32 from
          BitVec.eq_of_toNat_eq (by addr_omega [ho])]
        exact ob 32 _ (b8000964c_m_x8_32 h₄))
      (by
        rw [← A.x22, show s.getReg .x10 + 24 + 16 = s.getReg .x10 + BitVec.ofNat 64 40 from
          BitVec.eq_of_toNat_eq (by addr_omega [ho])]
        exact ob 40 _ (b8000964c_m_x8_40 h₄))
  have hv48 : NewVecE s u₄ (s.getReg .x10 + 48) pt :=
    newVecE_of (A.oVB.mono hle₄) (hb4 A.oHB)
      ((ob 48 _ (b8000964c_m_x8_48 h₄)).trans ((fr 56 5192 rfl).trans A.m56))
      (by
        rw [show s.getReg .x10 + 48 + 8 = s.getReg .x10 + BitVec.ofNat 64 56 from
          BitVec.eq_of_toNat_eq (by addr_omega [ho])]
        exact (ob 56 _ (b8000964c_m_x8_56 h₄)).trans ((fr 400 4848 rfl).trans A.m400))
      (by
        rw [show s.getReg .x10 + 48 + 16 = s.getReg .x10 + BitVec.ofNat 64 64 from
          BitVec.eq_of_toNat_eq (by addr_omega [ho])]
        exact (ob 64 _ (b8000964c_m_x8_64 h₄)).trans ((fr 408 4840 rfl).trans A.m408))
  have hw : eAt u₄ (s.getReg .x10 + 48 + 24) = word := by
    apply eq_of_limbs
    have e72 := ob 72 _ (b8000964c_m_x8_72 h₄)
    have e80 := ob 80 _ (b8000964c_m_x8_80 h₄)
    have e88 := (ob 88 _ (b8000964c_m_x8_88 h₄)).trans ((fr 40 5208 rfl).trans A.m40)
    rw [A.x26] at e72
    rw [A.x25] at e80
    rw [limbs_eAt,
      show s.getReg .x10 + 48 + 24 = s.getReg .x10 + BitVec.ofNat 64 72 from
        BitVec.eq_of_toNat_eq (by addr_omega [ho]),
      show s.getReg .x10 + BitVec.ofNat 64 72 + 8 = s.getReg .x10 + BitVec.ofNat 64 80 from
        BitVec.eq_of_toNat_eq (by addr_omega [ho]),
      show s.getReg .x10 + BitVec.ofNat 64 72 + 16 = s.getReg .x10 + BitVec.ofNat 64 88 from
        BitVec.eq_of_toNat_eq (by addr_omega [ho]), e72, e80, e88]
  have hr' : Rest s u₄ (pure ⟨some (pt, word), (inp, sl)⟩) :=
    A.rest.keep fun T hT ↦ B₃.tat hpre hH₄ (DFrame.of_memFrame f₄)
      (fun a ha ↦ ⟨by addr_omega [ha, hos', ho], Or.inl (by addr_omega [ha, ho])⟩) hT
  obtain ⟨t, hr₅, pc, pres, same⟩ := exit hpre (b8000964c_pc h₄) B₄.x2 B₄.saved
  exact ⟨t, hr₄.trans hr₅, Or.inl ⟨pc, pres,
    post_ok B₄ (o := ⟨some (pt, word), (inp, sl)⟩) (cap_ne h0 hH₄) hr' h0 h24
      ⟨cap_ne hv48 hH₄, hv48, hw⟩ same⟩⟩

end Rv64Verifier.Gkr.Keccak
