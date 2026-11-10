import Rv64Verifier.Proofs.Walk.R21A

/-!
# `walk` R21: what its callees ask, from `walk`'s facts

`tin`: the transcript at `tp` for a callee with an `m`-byte stack. `HeapBuf` buffers and the
weights whose buffers are such (`WeightIn`) are `Src` and apart from anything above the heap.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.PcsContracts Rv64Verifier.Pcs

/-- The transcript at `tp`, as a callee with an `m`-byte stack below the frame reads it. -/
theorem tin {s u : MachineState} (hpre : WalkPre s) (h : Inv s u)
    (hptr : u.getMem (tp s) = s.getReg .x13) {m : Nat} (hm : m ≤ 8736) :
    TranscriptIn u m (tp s) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  have hro := hpre.stack.rodata
  rw [stackLo_eq] at hab
  rw [stackLo_eq, stack_eq] at hx hro
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have hrs : rodataStart.toNat = 2684354560 := rfl
  have pRO := hpre.proofRO.2.1
  have sRO := hpre.streamRO.2.1
  rw [stackLo_eq, stack_eq] at pRO sRO
  obtain ⟨e0, e1, e2⟩ := proofVals hpre h hptr
  have hsl := stackLo_callee h m
  simp only [heapEnd] at hab
  refine ⟨tok hpre h hptr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsl, tp]; addr_omega [hb1, hm]
  · simp only [ProofApart, e0, e1, e2, hsl]
    exact ⟨by addr_omega [pRO, hb1, hm], by addr_omega [sRO, hb1, hm]⟩
  · rw [tp]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by addr_omega [hx, hb1]⟩
  · rw [e0]; exact outside_mono' hpre.proofRO.1 h.mono
  · rw [e1, e2]; exact outside_mono' hpre.streamRO.1 h.mono
  · rw [tp]; addr_omega [hro, hrb, hrs, hb1]

/-- The proof's bytes miss a frame range. -/
theorem proofApart_fr {s u : MachineState} (hpre : WalkPre s) (h : Inv s u)
    (hptr : u.getMem (tp s) = s.getReg .x13) {k n : Nat} (hk : n ≤ k) (hk2 : k ≤ 2656) :
    ProofApart u (tp s) (s.getReg .x2 - BitVec.ofNat 64 k) n := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have pRO := hpre.proofRO.2.1
  have sRO := hpre.streamRO.2.1
  rw [stackLo_eq, stack_eq] at pRO sRO
  obtain ⟨e0, e1, e2⟩ := proofVals hpre h hptr
  simp only [ProofApart, e0, e1, e2]
  exact ⟨by addr_omega [pRO, hb1, hk, hk2], by addr_omega [sRO, hb1, hk, hk2]⟩

theorem HeapBuf.mono {u v : MachineState} {p : Word} {n : Nat} (h : HeapBuf u p n)
    (hm : heapNext u ≤ heapNext v) : HeapBuf v p n :=
  ⟨h.1, by have := h.2.1; omega, h.2.2⟩

theorem Old.heapBuf {s u : MachineState} {p : Word} {n : Nat} (h : Old s u p n) (hs : HeapOk s) :
    HeapBuf u p n := by
  have := hs.lo
  exact ⟨h.1, h.2.1, h.2.2.imp_right fun h' ↦ by omega⟩

theorem HeapBuf.apart {u : MachineState} {p : Word} {n : Nat} (h : HeapBuf u p n) (hu : HeapOk u)
    {lo : Word} {m : Nat} (hl : heapEnd ≤ lo.toNat) : Apart p n lo m := by
  have := hu.hi
  have := h.2.1
  simp only [Apart]; omega

/-- A heap buffer is `Src` to a callee whose stack lies above the heap. -/
theorem HeapBuf.src {u : MachineState} {p : Word} {n : Nat} (h : HeapBuf u p n) (hu : HeapOk u)
    {k : Nat} (hk : heapEnd ≤ (stackLo u k).toNat) : Src u k p n := by
  have hh := hu.hi
  have hb := h.2.1
  refine ⟨h.2.2.imp_right fun h' ↦ ?_, h.apart hu hk, (heap_ok hu hb).1⟩
  simp only [Region, Mapped, heapStart, heapEnd] at h' hh ⊢
  exact ⟨Or.inl ⟨by omega, by omega⟩, h.1⟩

/-- Part of a heap buffer. -/
theorem HeapBuf.sub {u : MachineState} {a : Word} {n : Nat} (h : HeapBuf u a n) (hu : HeapOk u)
    (hs : heapStart ≤ a.toNat) {off m : Nat} (ho : off + m ≤ n) (h8 : off % 8 = 0) :
    HeapBuf u (a + BitVec.ofNat 64 off) m := by
  have hh := hu.hi
  have hb := h.2.1
  have ha := h.1
  simp only [heapNext, heapStart, heapEnd] at hh hb hs
  have e : (a + BitVec.ofNat 64 off).toNat = a.toNat + off := by addr_omega [hh, hb, ho]
  refine ⟨by rw [e]; omega, by rw [e]; simp only [heapNext]; omega, Or.inr ?_⟩
  rw [e]; simp only [heapStart]; omega

theorem WeightIn.src {u : MachineState} {a : Word} (h : WeightIn u a) (hu : HeapOk u) {k : Nat}
    (hk : heapEnd ≤ (stackLo u k).toNat) (ha : HeapBuf u a 64) (hs : heapStart ≤ a.toNat) :
    WeightSrc u k a := by
  refine ⟨ha.src hu hk, ?_⟩
  unfold WeightIn RingIn at h
  split_ifs at h ⊢
  · exact h.src hu hk
  · exact ⟨(ha.sub hu hs (off := 8) (m := 48) (by omega) (by omega)).src hu hk, h.1.src hu hk,
      h.2.src hu hk⟩
  · have := (ha.sub hu hs (off := 0) (m := 48) (by omega) (by omega)).src hu hk
    rw [show a + BitVec.ofNat 64 0 = a by simp] at this
    exact ⟨this, h.1.src hu hk, h.2.src hu hk⟩

theorem WeightIn.apart {u : MachineState} {a : Word} (h : WeightIn u a) (hu : HeapOk u)
    {lo : Word} {m : Nat} (hl : heapEnd ≤ lo.toNat) : WeightApart u a lo m := by
  unfold WeightIn RingIn at h
  unfold WeightApart RingApart
  split_ifs at h ⊢
  · exact h.apart hu hl
  · exact ⟨h.1.apart hu hl, h.2.apart hu hl⟩
  · exact ⟨h.1.apart hu hl, h.2.apart hu hl⟩


/-- A step, then writes into what it allocated and into frame bytes `W'`: one step (as `R19A`'s
`StepW.thenW`). -/
theorem StepW.thenE {s a b c : MachineState} (hpre : WalkPre s) {W W' : Word → Prop} {T : Prop}
    (ha : HeapOk a) (st : StepW s a b W T) (hW' : ∀ x, W' x → InF s x) {X : Word} {n : Nat}
    (fr : DFrame b c fun x ↦ W' x ∨ Within x X n) (h1 : heapNext a ≤ X.toNat)
    (h2 : X.toNat + n ≤ heapNext b) (sp : c.getReg .x2 = b.getReg .x2) :
    StepW s a c (fun x ↦ W x ∨ W' x) T := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hb := st.heap.hi
  have hm := st.mono
  have hl := ha.lo
  have hn : c.getMem nextAddr = b.getMem nextAddr := fr nextAddr fun i hi hw ↦ by
    simp only [heapNext, heapEnd, heapStart] at hb hm h1 h2 hl
    rcases hw with hw | hw
    · have := hW' _ hw; simp only [InF] at this; addr_omega [this, hi, hb1]
    · simp only [Within] at hw; addr_omega [hw, hi, h2, hb]
  have hn' : heapNext c = heapNext b := by simp only [heapNext, hn]
  refine ⟨(st.frame.mono fun x hx ↦ ?_).trans fr fun x hx ↦ ?_, ⟨hn' ▸ st.heap.lo, hn' ▸ st.heap.hi⟩,
    hn' ▸ st.mono, sp.trans st.sp⟩
  · simp only [Fresh] at hx ⊢
    rw [hn']
    rcases hx with hx | hx | hx | hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hx)))
  · simp only [Fresh]
    rw [hn']
    rcases hx with hx | hx
    · exact Or.inl (Or.inr hx)
    · simp only [Within] at hx
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))

end Rv64Verifier.Proofs.Walk
