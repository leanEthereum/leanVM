import Rv64Verifier.Proofs.Bus.VbbRun

/-!
# `verify_bus_balance`: calls of `eq_kernel`, `duplex`, `next_scalar` and `alloc`

Each from any site past the prologue, its result in the frame at `S - k`; each returns a step
(`Step`, `StepT` or `StepR`) and what it computes, or reaches a dead end.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

theorem heapRange {P : Word} {n : Nat} (ha : P.toNat % 8 = 0) (hlo : heapStart ≤ P.toNat)
    (hhi : P.toNat + 8 * n ≤ heapEnd) : ValidMemRange P n := by
  intro i hi
  apply validAccess_of_dword
  show Sym.validAccess 8 _ = true
  rw [Sym.validAccess_eight]
  simp only [heapStart, heapEnd] at hlo hhi
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem regionRange {a x : Word} {n m : Nat} (h : Region a n) (h1 : a.toNat ≤ x.toNat)
    (h2 : x.toNat + 8 * m ≤ a.toNat + n) (h3 : x.toNat % 8 = 0) : ValidMemRange x m := by
  intro i hi
  have hR := h
  simp only [Region, Mapped] at hR
  exact h.valid (by addr_omega [h1, h2, hi, hR]) (by addr_omega [h1, h2, hi, hR])
    (by addr_omega [h3, h2, hi, hR])

/-- A `Vec<E>` allocated since the entry: its elements lie in the heap below `NEXT`. -/
theorem NewVecE.inHeap {s u : MachineState} (hpre : BusBalancePre s) {a : Word}
    {xs : List E} (hv : NewVecE s u a xs) :
    (vecLen u a).toNat = 0 ∨ (heapNext s ≤ (vecPtr u a).toNat ∧
      (vecPtr u a).toNat + 24 * (vecLen u a).toNat ≤ heapNext u ∧ (vecPtr u a).toNat % 8 = 0) := by
  have hb := hv.buf
  have hl := hv.vec.len
  have hlo := hpre.heap.lo
  simp only [NewBuf] at hb
  by_cases h0 : (vecLen u a).toNat = 0
  · exact Or.inl h0
  · rcases hb.2 with hc | hc
    · exact absurd (by omega) h0
    · exact Or.inr ⟨hc.1, by omega, hb.1⟩

/-- A call of `eq_kernel` on the `Vec<E>` at `a`, of fewer than `64` elements, its result at
`S - k`. -/
theorem eqKernelCall (hEK : Vbb.EqKernelSpec) {s u₀ u : MachineState} (hpre : BusBalancePre s)
    (h : Inv s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x8000cb38) {k : Nat}
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 k) (hk1 : 128 ≤ k) (hk2 : k ≤ 1344)
    (hk8 : k % 8 = 0) {a : Word} {xs : List E} (hv : NewVecE s u a xs)
    (h11 : u.getReg .x11 = vecPtr u a) (h12 : u.getReg .x12 = vecLen u a)
    (hpos : 0 < (vecLen u a).toNat) (hsmall : (vecLen u a).toNat < 64) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      Step s u v (s.getReg .x2 - BitVec.ofNat 64 k) 24 ∧
      NewVecE s v (s.getReg .x2 - BitVec.ofNat 64 k) (eqKernelRust xs)) ∨ Dead Image.code v) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := Vbb.eqKernelStack) hpre h (n := 24) (by omega) hk2 hk8
    (by decide)
  have hsl : stackLo u Vbb.eqKernelStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 1232) := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hst := hpre.stack.above
  have hr4 := hpre.stack.rodata
  have hrb : rodataBase.toNat = 2684354560 := rfl
  rw [stackLo_eq] at hst hr4
  have hhi := h.heap.hi
  have hlo := hpre.heap.lo
  have hm := h.mono
  obtain ⟨i1, i2, i3⟩ : heapNext s ≤ (vecPtr u a).toNat ∧
      (vecPtr u a).toNat + 24 * (vecLen u a).toNat ≤ heapNext u ∧ (vecPtr u a).toNat % 8 = 0 := by
    rcases NewVecE.inHeap hpre hv with h0 | h0
    · omega
    · exact h0
  simp only [heapNext, heapEnd, heapStart] at hhi hlo hm i1 i2 hst
  have pre : Vbb.EqKernelPre u := {
    heap := h.heap
    out := by
      rw [h10]; exact regionRange o1 (Nat.le_refl _) (by omega) (by addr_omega [hb1, hb3, hk8, hk2])
    point := by
      rw [h11, h12]
      exact heapRange i3 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
    small := by rw [h12]; exact hsmall
    stack := hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := h10 ▸ o2
    outStack := h10 ▸ o3
    outRodata := by rw [h10]; simp only [rodataSize] at hr4 ⊢; addr_omega [hr4, hrb, hb1, hk1, hk2]
    pointFree := by
      rw [h11, h12]
      exact ⟨Or.inl (by simp only [heapNext]; omega), by addr_omega [i2, hhi]⟩
    pointStack := by rw [h11, h12, hsl]; addr_omega [i2, hhi, hst, hb1]
    pointOut := by rw [h11, h12, h10]; addr_omega [i2, hhi, hb1, hk1, hk2]
    rodata := h.rodata hpre }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hEK.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have hsp := hp.reg .x2
  have st : Step s u v (s.getReg .x2 - BitVec.ofNat 64 k) 24 := by
    refine ⟨fun x hx ↦ post.frame x fun i hi hw ↦ hx i hi ?_, post.heap, post.mono, hsp⟩
    simp only [Vbb.EqKernelW, hsl, h10] at hw
    rcases hw with hw | hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inl (by addr_omega [hw, hb1]))
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr hw))
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, st, ?_⟩⟩
  have hvec := post.vec
  have hfr := post.fresh
  have hlen := post.len
  rw [h10] at hvec hfr hlen
  have he := post.elems
  rw [h10, h11, h12] at he
  have hraw := hvec.raw
  simp only [RawVecOk, Buf, NewBuf] at hraw hfr
  refine ⟨hvec, ⟨hraw.1, ?_⟩, ?_⟩
  · rcases hraw.2 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ⟨?_, h0.2⟩
      rcases hfr.2 with h1 | h1
      · exact absurd h1 (by positivity)
      · exact Nat.le_trans h.mono h1.1
  · rw [he, ← hv.elems]
    rfl

/-- A call of `Sponge::duplex` on the transcript's sponge: what the transcript stands for has its
sponge permuted. -/
theorem duplexCall (hD : DuplexSpec) {s u₀ u : MachineState} (hpre : BusBalancePre s)
    (h : Inv s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x80007cd8)
    (h10 : u.getReg .x10 = s.getReg .x12 + 8) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      StepR s u v (fun _ ↦ False) ∧
      ∀ T, TranscriptAt u (s.getReg .x12) T →
        TranscriptAt v (s.getReg .x12) { T with sponge := spDuplex T.sponge }) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hS := hpre.self.self
  have ss := hpre.selfStack
  have sr := hpre.selfRodata
  rw [stackLo_eq] at ss
  have hsl : stackLo u duplexStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + duplexStack) := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have pre : DuplexPre u := {
    sponge := by rw [h10]; addr_omega [hS]
    stack := hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
    spongeStack := by rw [h10, hsl]; addr_omega [hS, ss, hb1]
    rodata := h.rodata hpre
    spongeRodata := by rw [h10]; addr_omega [sr, hS] }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hD.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have fr := post.frame
  rw [h10, hsl] at fr
  have hval := post.value
  rw [h10] at hval
  have hn : heapNext v = heapNext u := by
    have hx := hpre.stack.next
    rw [stackLo_eq] at hx
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hx, hw, hi, hb1, hS, hpre.selfFree.2])
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, ⟨fr.mono fun a ha ↦ ?_, ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩,
    hn.ge, hp.reg .x2⟩, fun T hT ↦ ?_⟩⟩
  · rcases ha with ha | ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hS]))
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))
  have hf := hpre.proofFree
  have bf := hpre.streamFree
  have ps := hpre.proofStack
  have hA := hpre.self.apart
  rw [stackLo_eq] at ps
  simp only [ProofApart] at ps hA
  obtain ⟨e0, e1, e2⟩ := h.stream hpre
  have hok := h.tok hpre
  have kept (y : Word) (hy : ∀ i < 8, ¬ (Within (y + BitVec.ofNat 64 i) (s.getReg .x12 + 8) 336 ∨
      Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - BitVec.ofNat 64 (1344 + duplexStack))
        duplexStack)) : v.getMem y = u.getMem y := fr y hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hT.stream]
    refine fr.eListAt_stream (fun i hi hw ↦ ?_) (fun i hi hw ↦ ?_) (fun i hi hw ↦ ?_)
    · rcases hw with hw | hw <;> addr_omega [hw, hi, hS, ss, hb1]
    · rw [e0] at hw
      rcases hw with hw | hw <;> addr_omega [hw, hi, hA.1, ps.1, hb1, hpre.self.proof]
    · rw [e1] at hw
      rw [e2] at hi
      rcases hpre.self.stream with h0 | h0
      · omega
      rcases hw with hw | hw <;> addr_omega [hw, hi, hA.2, ps.2, hb1, h0]
  · rw [hval, hT.sponge]
  · rw [← hT.streamOffset, kept _ fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hS, ss, hb1]]
  · rw [← hT.openingOffset, kept _ fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hS, ss, hb1]]

/-- A call of `Transcript::next_scalar`, its result at `S - k`: the tag `0` exactly when the
mirror reads the scalar after it. -/
theorem nextScalarCall (hN : NextScalarSpec) {s u₀ u : MachineState} (hpre : BusBalancePre s)
    (h : Inv s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x8000c720) {k : Nat}
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 k) (h11 : u.getReg .x11 = s.getReg .x12)
    (hk1 : 136 ≤ k) (hk2 : k ≤ 1344) (hk8 : k % 8 = 0) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      StepT s u v (s.getReg .x2 - BitVec.ofNat 64 k) 32 ∧ Inv s v ∧
      (v.getMem (s.getReg .x2 - BitVec.ofNat 64 k) ≠ 0 → ∀ T, TranscriptAt u (s.getReg .x12) T →
        TM.nextScalar.run T = none) ∧
      (v.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = 0 → ∀ T, TranscriptAt u (s.getReg .x12) T →
        ∃ T', TM.nextScalar.run T = some (eAt v (s.getReg .x2 - BitVec.ofNat 64 k + 8), T') ∧
          TranscriptAt v (s.getReg .x12) T')) ∨ Dead Image.code v) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have tp : TPre 32 nextScalarStack u := tpre hpre h (by omega) hk2 hk8 (by decide) (by decide)
    h10 h11
  have pre : NextScalarPre u := ⟨tp.out, tp.self, tp.stack, tp.outStack, tp.selfStack, tp.outSelf,
    tp.proofStack, tp.proofOut, tp.rodata, tp.outRodata, tp.selfRodata⟩
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hN.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have hsl : stackLo u nextScalarStack =
      s.getReg .x2 - BitVec.ofNat 64 (1344 + nextScalarStack) := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fr := post.frame
  rw [h10, h11, hsl] at fr
  have hn : heapNext v = heapNext u := by
    have hx := hpre.stack.next
    have hS := hpre.self.self
    rw [stackLo_eq] at hx
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw | hw <;> addr_omega [hx, hw, hi, hb1, hS, hpre.selfFree.2, hk2])
  have st : StepT s u v (s.getReg .x2 - BitVec.ofNat 64 k) 32 :=
    ⟨fr.mono fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl (Or.inl ha)
      · exact Or.inr ha
      · exact Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb1]))),
      ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩, hn.ge, hp.reg .x2⟩
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, st, h.afterT hpre (inFrame hpre (by omega) hk2) st,
    fun h0 T hT ↦ ?_, fun h0 T hT ↦ ?_⟩⟩
  · have hv := post.value T (h11 ▸ hT)
    rw [h10] at hv
    revert hv
    rcases TM.nextScalar.run T with _ | ⟨x, T'⟩
    · exact fun _ ↦ rfl
    · exact fun hv ↦ absurd hv.1 h0
  · have hv := post.value T (h11 ▸ hT)
    rw [h10, h11] at hv
    revert hv
    rcases TM.nextScalar.run T with _ | ⟨x, T'⟩
    · intro hv; rw [h0] at hv; exact absurd hv.1 (by decide)
    · intro hv; exact ⟨T', by rw [hv.2.1], hv.2.2⟩

/-- A call of the allocator. -/
theorem allocCall (hA : AllocSpec) {s u₀ u : MachineState} (h : Inv s u)
    (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x80000284) (h10 : u.getReg .x10 = 8) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ AllocPost u v) ∨
      Dead Image.code v) :=
  hA.call hr hpc ⟨h.heap, by rw [h10]; decide⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
