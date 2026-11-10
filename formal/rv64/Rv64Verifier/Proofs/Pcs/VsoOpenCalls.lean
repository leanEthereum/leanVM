import Rv64Verifier.Proofs.Pcs.VsoOpenBase

/-!
# `verify_stacked_opening`'s level loop: the opening's callees, from its frame

`next_scalars`, `samples` and `next_scalar` with their result in the frame, and `grow_one` of the
pending claims' `Vec` (80-byte elements, at `0x8000c7d0`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A frame slot of 24 bytes. -/
@[rv_addr] def Slot24 (s : MachineState) (o : Word) : Prop :=
  (s.getReg .x2 - 1040).toNat ≤ o.toNat ∧ o.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
    o.toNat % 8 = 0

/-- What an allocating transcript function with its result at `o` in the frame asks. -/
theorem tpreV {s t : MachineState} {nx o : Word} (k : ℕ) (hk : 1040 + k ≤ 2464) (hk8 : k % 8 = 0)
    (hpre : VsoPre s) (hinv : InvR s t nx) (hheap : HeapOk t) (hx10 : t.getReg .x10 = o)
    (hx11 : t.getReg .x11 = s.getReg .x10) (ho : Slot24 s o) :
    TPre 24 k t := by
  have hb := bounds hpre
  have hst := hpre.stack
  rw [vso_stack] at hst
  obtain ⟨hnx, hro⟩ := sfacts hpre
  have hsp := hinv.sp
  have hI := hpre.self
  have hIs := hI.stack
  have hPs := hI.proofStack
  rw [stackLo_vso, vso_stack] at hIs hPs
  simp only [ProofApart] at hPs
  simp only [Slot24] at ho
  obtain ⟨hTok, e0, e1, e2⟩ := trR_facts hpre hinv
  have hsu : heapNext s ≤ heapNext t := by
    have hn : heapNext t = nx.toNat := by simp only [heapNext, hinv.next]
    rw [hn]; exact hinv.mono
  have hsl : (stackLo t k).toNat = (s.getReg .x2).toNat - 1040 - k := by
    simp only [stackLo, hsp]; addr_omega [hb, hk]
  exact {
    heap := hheap
    out := by rw [hx10]; exact stack_region hpre (by addr_omega [ho, hb]) (by addr_omega [ho, hb]) ho.2.2
    self := by rw [hx11]; exact hTok
    stack := hst.sub 1040 hsp (by omega) (by decide) hk8 (by decide) (by decide)
    outStack := by rw [hx10]; simp only [Apart]; addr_omega [ho, hb, hsl, hk]
    selfStack := by rw [hx11]; simp only [Apart]; addr_omega [hIs, hb, hsl, hk]
    outSelf := by rw [hx10, hx11]; addr_omega [ho, hIs, hb]
    proofStack := by
      rw [hx11]; simp only [ProofApart, e0, e1, e2]
      exact ⟨by simp only [Apart] at hPs ⊢; addr_omega [hPs.1, hb, hsl, hk],
        by simp only [Apart] at hPs ⊢; addr_omega [hPs.2, hb, hsl, hk]⟩
    proofOut := by
      rw [hx11, hx10]; simp only [ProofApart, e0, e1, e2]
      exact ⟨by addr_omega [hPs.1, ho, hb], by addr_omega [hPs.2, ho, hb]⟩
    outFree := by
      rw [hx10]; exact stack_outside hpre (by addr_omega [ho, hb]) (by addr_omega [ho, hb])
    selfFree := by rw [hx11]; exact outside_mono hI.free hsu
    proofFree := by rw [hx11, e0]; exact outside_mono hI.proofFree hsu
    streamFree := by rw [hx11, e1, e2]; exact outside_mono hI.streamFree hsu
    rodata := hinv.rodata' hpre
    outRodata := by rw [hx10]; addr_omega [hro, ho, hb]
    selfRodata := by rw [hx11]; exact hI.rodata }

/-- The frame of an allocating transcript function, in the function's terms. -/
theorem tframeV {s t v : MachineState} {o : Word} {k : ℕ} (hk : 1040 + k ≤ 2464)
    (hpre : VsoPre s) (hsp : t.getReg .x2 = s.getReg .x2 - 1040) (hx10 : t.getReg .x10 = o)
    (hx11 : t.getReg .x11 = s.getReg .x10) (h : TFrame 24 k t v) :
    DFrame t v fun a ↦ Within a o 24 ∨ Within a (s.getReg .x10 + 8) 344 ∨
      Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh t v a := by
  have hb := bounds hpre
  simp only [TFrame] at h
  rw [hx10, hx11] at h
  refine h.mono fun a ha ↦ ?_
  rcases ha with ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · simp only [stackLo, hsp] at ha
    exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb, hk])))
  · exact Or.inr (Or.inr (Or.inr ha))

/-! ## `Transcript::next_scalars` -/

theorem callNextScalars (hNS : NextScalarsSpec) {s t : MachineState} {nx o : Word}
    (hpre : VsoPre s) (hinv : InvR s t nx) (hheap : HeapOk t) (hpc : t.pc = 0x80004818)
    (hx10 : t.getReg .x10 = o) (hx11 : t.getReg .x11 = s.getReg .x10) (ho : Slot24 s o) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      DFrame t v (fun a ↦ Within a o 24 ∨ Within a (s.getReg .x10 + 8) 344 ∨
        Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh t v a) ∧
      (vecCap v o = errNiche → v.getMem (o + 8) ≠ errNiche) ∧
      (vecCap v o ≠ errNiche →
        VecOk v o 24 8 ∧ NewBuf t v (vecPtr v o) ((vecCap v o).toNat * 24) 8) ∧
      ∀ T, TranscriptAt t (s.getReg .x10) T →
        match (Model.TM.nextScalars (t.getReg .x12).toNat).run T with
        | some (xs, T') => vecCap v o ≠ errNiche ∧ NewVecE t v o xs ∧
            TranscriptAt v (s.getReg .x10) T'
        | none => vecCap v o = errNiche)) := by
  have hpreN : NextScalarsPre t :=
    tpreV nextScalarsStack (by decide) (by decide) hpre hinv hheap hx10 hx11 ho
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hNS.call (Reaches.refl t) hpc hpreN
  swap
  · exact ⟨v, hr, Or.inl hdead⟩
  have herr := hpost.err
  have hok := hpost.ok
  simp only [VecResult] at hok
  rw [hx10] at herr hok
  refine ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono,
    tframeV (by decide) hpre hinv.sp hx10 hx11 hpost.frame, herr, hok, fun T hT ↦ ?_⟩⟩
  have hv := hpost.value T (by rw [hx11]; exact hT)
  rw [hx10, hx11] at hv
  exact hv

/-! ## `Transcript::samples` -/

theorem callSamples (hS : SamplesSpec) {s t : MachineState} {nx o : Word}
    (hpre : VsoPre s) (hinv : InvR s t nx) (hheap : HeapOk t) (hpc : t.pc = 0x8000c618)
    (hx10 : t.getReg .x10 = o) (hx11 : t.getReg .x11 = s.getReg .x10) (ho : Slot24 s o) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      DFrame t v (fun a ↦ Within a o 24 ∨ Within a (s.getReg .x10 + 8) 344 ∨
        Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh t v a) ∧
      ∀ T, TranscriptAt t (s.getReg .x10) T → ∃ xs T',
        (Model.TM.samples (t.getReg .x12).toNat).run T = some (xs, T') ∧ NewVecE t v o xs ∧
          TranscriptAt v (s.getReg .x10) T')) := by
  have hpreS : SamplesPre t :=
    tpreV samplesStack (by decide) (by decide) hpre hinv hheap hx10 hx11 ho
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hS.call (Reaches.refl t) hpc hpreS
  swap
  · exact ⟨v, hr, Or.inl hdead⟩
  refine ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono,
    tframeV (by decide) hpre hinv.sp hx10 hx11 hpost.frame, fun T hT ↦ ?_⟩⟩
  have hv := hpost.value T (by rw [hx11]; exact hT)
  rw [hx10, hx11] at hv
  exact hv

/-! ## `Transcript::next_scalar` -/

theorem callNextScalar (hN : NextScalarSpec) {s t : MachineState} {nx o : Word}
    (hpre : VsoPre s) (hinv : InvR s t nx) (hpc : t.pc = 0x8000c720)
    (hx10 : t.getReg .x10 = o) (hx11 : t.getReg .x11 = s.getReg .x10)
    (ho : (s.getReg .x2 - 1040).toNat ≤ o.toNat ∧ o.toNat + 32 ≤ (s.getReg .x2 - 104).toNat ∧
      o.toNat % 8 = 0) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      DFrame t v (fun a ↦ Within a o 32 ∨ Within a (s.getReg .x10 + 8) 344 ∨
        Within a (s.getReg .x2 - 2464) 1424) ∧
      (v.getMem o ≠ 0 → v.getMem (o + 8) = 3) ∧
      ∀ T, TranscriptAt t (s.getReg .x10) T →
        match Model.TM.nextScalar.run T with
        | some (x, T') => v.getMem o = 0 ∧ eAt v (o + 8) = x ∧ TranscriptAt v (s.getReg .x10) T'
        | none => v.getMem o = 1 ∧ v.getMem (o + 8) = 3)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  rw [vso_stack] at hst
  obtain ⟨-, hro⟩ := sfacts hpre
  have hsp := hinv.sp
  have hI := hpre.self
  have hIs := hI.stack
  have hPs := hI.proofStack
  rw [stackLo_vso, vso_stack] at hIs hPs
  simp only [ProofApart] at hPs
  obtain ⟨hTok, e0, e1, e2⟩ := trR_facts hpre hinv
  have hsl : stackLo t nextScalarStack = s.getReg .x2 - 2016 := by
    simp only [stackLo, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack, hsp,
      Nat.reduceAdd]
    rv_eval []
  have hpreN : NextScalarPre t := {
    out := by rw [hx10]; exact stack_region hpre (by addr_omega [ho, hb]) (by addr_omega [ho, hb]) ho.2.2
    self := by rw [hx11]; exact hTok
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    outStack := by rw [hx10, hsl]; addr_omega [ho, hb]
    selfStack := by rw [hx11, hsl]; addr_omega [hIs, hb]
    outSelf := by rw [hx10, hx11]; addr_omega [ho, hIs, hb]
    proofStack := by
      rw [hx11, hsl]; simp only [ProofApart, e0, e1, e2]
      exact ⟨by addr_omega [hPs.1, hb], by addr_omega [hPs.2, hb]⟩
    proofOut := by
      rw [hx11, hx10]; simp only [ProofApart, e0, e1, e2]
      exact ⟨by addr_omega [hPs.1, ho, hb], by addr_omega [hPs.2, ho, hb]⟩
    rodata := hinv.rodata' hpre
    outRodata := by rw [hx10]; addr_omega [hro, ho, hb]
    selfRodata := by rw [hx11]; exact hI.rodata }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hN.call (Reaches.refl t) hpc hpreN
  swap
  · exact ⟨v, hr, Or.inl hdead⟩
  have hfr := hpost.frame
  have herr := hpost.err
  rw [hx10, hx11, hsl] at hfr
  rw [hx10] at herr
  refine ⟨v, hr, Or.inr ⟨hpc', hpres, hfr.mono fun a ha ↦ ?_, herr, fun T hT ↦ ?_⟩⟩
  · rcases ha with ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (by addr_omega [ha, hb]))
  · have hv := hpost.value T (by rw [hx11]; exact hT)
    rw [hx10, hx11] at hv
    exact hv

/-! ## `grow_one` of the pending claims -/

theorem callGrow80 (hG : GrowOneFreshSpec 0x8000c7d0 80 8) {s t : MachineState} {nx A : Word}
    (hpre : VsoPre s) (hinv : InvR s t nx) (hheap : HeapOk t) (hpc : t.pc = 0x8000c7d0)
    (hx10 : t.getReg .x10 = A)
    (hA : (s.getReg .x2 - 1040).toNat ≤ A.toNat ∧ A.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      A.toNat % 8 = 0)
    (hv : VecOk t A 80 8) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      DFrame t v (fun a ↦ Within a A 16 ∨ Within a (s.getReg .x2 - 1200) 160 ∨
        Within a nextAddr 8 ∨ Fresh t v a) ∧
      vecLen v A = vecLen t A ∧ (vecCap t A).toNat + 1 ≤ (vecCap v A).toNat ∧
      RawVecOk v A 80 8 ∧ NewBuf t v (vecPtr v A) ((vecCap v A).toNat * 80) 8)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := hinv.sp
  have hsl : stackLo t growOneStack = s.getReg .x2 - 1200 := by
    simp only [stackLo, growOneStack, hsp]; rv_eval []
  have hpreG : GrowOnePre 80 8 t := {
    heap := hheap
    self := by rw [hx10]; valid_sub hst.valid [hb, hA]
    raw := by rw [hx10]; exact hv.raw
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := by
      rw [hx10]; exact stack_outside hpre (by addr_omega [hA, hb]) (by addr_omega [hA, hb])
    selfStack := by rw [hx10, hsl]; addr_omega [hA, hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost, hnew⟩ | hdead⟩ := hG.call (Reaches.refl t) hpc hpreG
  swap
  · exact ⟨v, hr, Or.inl hdead⟩
  have hfr := DFrame.of_byteFrame hpost.frame
  rw [hx10, hsl] at hfr
  rw [hx10] at hnew
  have hcap := hpost.cap
  have hraw' := hpost.raw
  rw [hx10] at hcap hraw'
  have hhv := hpost.heap.hi
  have e2 : vecLen v A = vecLen t A := hfr _ fun i hi hx ↦ by
    rcases hx with hx | hx | hx | hx
    · addr_omega [hx, hi, hA]
    · addr_omega [hx, hi, hA, hb]
    · addr_omega [hx, hi, hA, hb, hnx]
    · simp only [Fresh] at hx; addr_omega [hx.2, hi, hA, hb, hhv]
  exact ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono, hfr, e2, hcap, hraw', hnew⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
