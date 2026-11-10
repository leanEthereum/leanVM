import Rv64Verifier.Proofs.Walk.Exit

/-!
# `walk`: calls of the transcript's callees

A transcript callee's precondition (`tpre`, `TPre` for its result at `S - k`), and its frame as a
step (`StepT`: a `Step` that may also write the transcript's sponge and offsets, `352` bytes from
`tp + 8`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Transcript

theorem outside_mono' {s u : MachineState} {a : Word} {n : Nat} (h : Outside s a n)
    (hm : heapNext s ≤ heapNext u) : Outside u a n :=
  ⟨h.1.imp_left fun h' ↦ by omega, h.2⟩

/-- The proof's address, stream buffer and length, as the transcript at `tp` reads them. -/
theorem proofVals {s u : MachineState} (hpre : WalkPre s) (h : Inv s u)
    (hptr : u.getMem (tp s) = s.getReg .x13) :
    proofAt u (tp s) = s.getReg .x13 ∧ streamPtr u (tp s) = vecPtr s (s.getReg .x13) ∧
      streamLen u (tp s) = (vecLen s (s.getReg .x13)).toNat := by
  have hP := hpre.proof
  have e8 : u.getMem (s.getReg .x13 + 8) = s.getMem (s.getReg .x13 + 8) :=
    h.word hpre.proofRO (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP])
  have e16 : u.getMem (s.getReg .x13 + 16) = s.getMem (s.getReg .x13 + 16) :=
    h.word hpre.proofRO (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP])
  refine ⟨hptr, ?_, ?_⟩
  · simp only [streamPtr, proofAt, hptr, vecPtr, e8]
  · simp only [streamLen, proofAt, hptr, vecLen, e16]

/-- The transcript at `tp` and the proof it reads lie in memory. -/
theorem tok {s u : MachineState} (hpre : WalkPre s) (h : Inv s u)
    (hptr : u.getMem (tp s) = s.getReg .x13) : TranscriptOk u (tp s) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have pRO := hpre.proofRO.2.1
  have sRO := hpre.streamRO.2.1
  rw [stackLo_eq, stack_eq] at pRO sRO
  obtain ⟨e0, e1, e2⟩ := proofVals hpre h hptr
  refine ⟨by rw [tp]; addr_omega [hb1, hb2, hb3], by rw [e0]; exact hpre.proof, ?_, ?_⟩
  · rw [e1, e2]; exact hpre.stream
  · simp only [ProofApart, e0, e1, e2]
    rw [tp]
    exact ⟨by addr_omega [pRO, hb1], by addr_omega [sRO, hb1]⟩

/-- A step that writes no memory keeps what the transcript stands for. -/
theorem TranscriptAt.same {s u v : MachineState} (hpre : WalkPre s) (h : Inv s u)
    (hptr : u.getMem (tp s) = s.getReg .x13) (hm : ∀ a, v.getMem a = u.getMem a) {T : TState}
    (hT : TranscriptAt u (tp s) T) : TranscriptAt v (tp s) T :=
  (DFrame.of_same hm fun _ ↦ False).transcriptAt hT (tok hpre h hptr) (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) (fun _ _ h ↦ h) (fun _ _ h ↦ h)

theorem NewVecE.widen' {s u v : MachineState} {a : Word} {xs : List E} (h : NewVecE u v a xs)
    (hm : heapNext s ≤ heapNext u) : NewVecE s v a xs := by
  have hb := h.buf
  simp only [NewBuf] at hb
  exact ⟨h.vec, ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨by omega, h'.2⟩⟩, h.elems⟩

/-- The precondition of a transcript callee with an `m`-byte stack, its `n`-byte result at
`S - k`, above the transcript. -/
theorem tpre {s u : MachineState} (hpre : WalkPre s) (h : Inv s u)
    (hptr : u.getMem (tp s) = s.getReg .x13) {k n m : Nat} (hk1 : 104 + n ≤ k) (hk2 : k ≤ 2080)
    (hk8 : k % 8 = 0) (hm : m ≤ 8736) (hm8 : m % 8 = 0)
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 k) (h11 : u.getReg .x11 = tp s) :
    TPre n m u := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  have hro := hpre.stack.rodata
  rw [stackLo_eq] at hab
  rw [stackLo_eq, stack_eq] at hx hro
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have hrs : rodataStart.toNat = 2684354560 := rfl
  have hP := hpre.proof
  have pRO := hpre.proofRO.2.1
  have sRO := hpre.streamRO.2.1
  have hR := hpre.stream
  rw [stackLo_eq, stack_eq] at pRO sRO
  obtain ⟨e0, e1, e2⟩ := proofVals hpre h hptr
  have hsl := stackLo_callee h m
  simp only [heapEnd] at hab
  refine {
    heap := h.heap
    out := by rw [h10]; addr_omega [hb1, hb2, hb3, hk1, hk2, hk8]
    self := by
      rw [h11]
      refine ⟨by rw [tp]; addr_omega [hb1, hb2, hb3], by rw [e0]; exact hP, ?_, ?_⟩
      · rw [e1, e2]; exact hR
      · simp only [ProofApart, e0, e1, e2]
        rw [tp]
        exact ⟨by addr_omega [pRO, hb1], by addr_omega [sRO, hb1]⟩
    stack := hpre.stack.sub 2656 h.sp (by rw [stack_eq]; omega) (by decide) hm8 (by decide)
      (by decide)
    outStack := by rw [h10, hsl]; addr_omega [hb1, hk1, hk2, hm]
    selfStack := by rw [h11, hsl, tp]; addr_omega [hb1, hm]
    outSelf := by rw [h10, h11, tp]; addr_omega [hb1, hk1, hk2]
    proofStack := by
      rw [h11]; simp only [ProofApart, e0, e1, e2, hsl]
      exact ⟨by addr_omega [pRO, hb1, hm], by addr_omega [sRO, hb1, hm]⟩
    proofOut := by
      rw [h11, h10]; simp only [ProofApart, e0, e1, e2]
      exact ⟨by addr_omega [pRO, hb1, hk1, hk2], by addr_omega [sRO, hb1, hk1, hk2]⟩
    outFree := by rw [h10]; exact ⟨Or.inr (by addr_omega [hab, hb1, hk1, hk2]),
      by addr_omega [hx, hb1, hk1, hk2]⟩
    selfFree := by rw [h11, tp]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by addr_omega [hx, hb1]⟩
    proofFree := by rw [h11, e0]; exact outside_mono' hpre.proofRO.1 h.mono
    streamFree := by rw [h11, e1, e2]; exact outside_mono' hpre.streamRO.1 h.mono
    rodata := h.rodata hpre
    outRodata := by rw [h10]; addr_omega [hro, hrb, hrs, hb1, hk1, hk2]
    selfRodata := by rw [h11, tp]; addr_omega [hro, hrb, hrs, hb1] }

/-! ## Steps that use the transcript -/

/-- A step writing `Below` or the transcript's sponge and offsets, keeping `sp`. -/
structure StepT (s v w : MachineState) (lo : Word) (n : Nat) : Prop where
  frame : DFrame v w fun a ↦ Below s v w lo n a ∨ Within a (tp s + 8) 352
  heap : HeapOk w
  mono : heapNext v ≤ heapNext w
  sp : w.getReg .x2 = v.getReg .x2

theorem Inv.afterT {s v w : MachineState} (hpre : WalkPre s) (h : Inv s v) {lo : Word}
    {n : Nat} (hl : InFrame s lo n) (st : StepT s v w lo n) : Inv s w := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine h.loc hpre (st.frame.mono fun a ha ↦ ?_) st.heap st.mono st.sp
  rcases ha with ha | ha
  · exact Below.loc hpre hl ha
  · exact Or.inl (by rw [tp] at ha; addr_omega [ha, hb1])

/-- A doubleword in the frame apart from what a step writes keeps its value. -/
theorem StepT.word {s v w : MachineState} (hpre : WalkPre s) {lo : Word} {n : Nat}
    (st : StepT s v w lo n) {x : Word} (hx : Apart x 8 lo n) (ht : Apart x 8 (tp s + 8) 352)
    (hy : (s.getReg .x2 - 2656).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat) :
    w.getMem x = v.getMem x := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hh := st.heap.hi
  have hn := hpre.stack.next
  have ha := hpre.stack.above
  rw [stackLo_eq, stack_eq] at hn
  rw [stackLo_eq] at ha
  refine st.frame x fun i hi hw ↦ ?_
  simp only [Below, Fresh, heapNext, heapEnd] at hw hh ha
  rcases hw with (hw | hw | hw | ⟨-, hw⟩) | hw <;>
    addr_omega [hx, ht, hy, hw, hi, hb1, hb2, hh, hn, ha]

/-- A transcript callee's frame (`TFrame`) as a `StepT`, its result at `S - k`. -/
theorem TFrame.stepT {s u v : MachineState} (hpre : WalkPre s) (h : Inv s u) {k n m : Nat}
    (hm : m ≤ 8736) (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 k)
    (h11 : u.getReg .x11 = tp s) (hf : TFrame n m u v) (hheap : HeapOk v)
    (hmono : heapNext u ≤ heapNext v) (hsp : v.getReg .x2 = u.getReg .x2) :
    StepT s u v (s.getReg .x2 - BitVec.ofNat 64 k) n := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine ⟨hf.mono fun a ha ↦ ?_, hheap, hmono, hsp⟩
  rw [stackLo_callee h, h10, h11] at ha
  rcases ha with ha | ha | ha | ha | ha
  · exact Or.inl (Or.inl ha)
  · exact Or.inr (by rw [tp] at ha ⊢; addr_omega [ha, hb1])
  · exact Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb1, hm])))
  · exact Or.inl (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr ha)))

end Rv64Verifier.Proofs.Walk
