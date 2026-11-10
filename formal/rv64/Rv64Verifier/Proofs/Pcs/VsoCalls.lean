import Rv64Verifier.Proofs.Pcs.VsoLevel

/-!
# `verify_stacked_opening`'s level loop: its callees, from its frame

Each callee's contract instantiated from the function's frame (`sp = S - 1040`, the callees'
stacks below it), its precondition discharged from `InvR` and the entry's facts, its frame
stated in the entry's terms.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem InvR.rodata' {s u : MachineState} {nx : Word} (hpre : VsoPre s) (h : InvR s u nx) :
    RodataOk u := by
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hrr := hpre.rootRodata
  exact h.rodata hpre.rodata (fun a ha hr ↦ by
    rcases ha with ha | ha
    · have := hI.rodata; simp only [W] at ha; addr_omega [this, ha, hr, hS]
    · addr_omega [hrr, ha, hr]) hpre.stack.rodata

/-! ## `Sponge::duplex` -/

theorem callDuplex (hD : DuplexSpec) {s t : MachineState} {nx : Word} (hpre : VsoPre s)
    (hinv : InvR s t nx) (hpc : t.pc = 0x80007cd8) (hx10 : t.getReg .x10 = s.getReg .x10 + 8) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      DFrame t v (fun a ↦ Within a (s.getReg .x10 + 8) 336 ∨
        Within a (s.getReg .x2 - 1920) 880) ∧
      spongeAt v (s.getReg .x10 + 8) = spDuplex (spongeAt t (s.getReg .x10 + 8)))) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hsp := hinv.sp
  have hsl : stackLo t duplexStack = s.getReg .x2 - 1920 := by
    simp only [stackLo, duplexStack, keccakFStack, memStack, hsp, Nat.reduceAdd]; rv_eval []
  have hpreD : DuplexPre t := {
    sponge := by rw [hx10]; exact region_sub hI.ok.self 8 336 (by decide) (by decide)
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    spongeStack := by rw [hx10, hsl]; addr_omega [hIs, hS, hb]
    rodata := hinv.rodata' hpre
    spongeRodata := by rw [hx10]; have := hI.rodata; addr_omega [this, hS] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hD.call (Reaches.refl t) hpc hpreD
  · have hfr := hpost.frame
    have hval := hpost.value
    rw [hx10, hsl] at hfr
    rw [hx10] at hval
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, hfr, hval⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- After a `duplex`, the transcript stands for the mirror's after a `sample`. -/
theorem tr_duplex {s u v : MachineState} {nx : Word} {T : Model.TState} (hpre : VsoPre s)
    (hinv : InvR s u nx) (hT : TranscriptAt u (s.getReg .x10) T)
    (hX : DFrame u v fun a ↦ Within a (s.getReg .x10 + 8) 336 ∨
      Within a (s.getReg .x2 - 1920) 880)
    (hsp : spongeAt v (s.getReg .x10 + 8) = spDuplex (spongeAt u (s.getReg .x10 + 8))) :
    TranscriptAt v (s.getReg .x10) { T with sponge := spDuplex T.sponge } := by
  have hb := bounds hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  have hPs := hI.proofStack
  rw [stackLo_vso, vso_stack] at hIs hPs
  obtain ⟨-, e0, e1, e2⟩ := trR_facts hpre hinv
  have hpa := hpre.proofSponge
  simp only [ProofApart] at hpa hPs
  have hP := Region.bounds hI.ok.proof
  have hB : streamLen s (s.getReg .x10) = 0 ∨
      (streamPtr s (s.getReg .x10)).toNat + 24 * streamLen s (s.getReg .x10) ≤ 2 ^ 64 := by
    rcases hI.ok.stream with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by have := Region.bounds h0; omega)
  have keep (y : Word) (hy1 : (s.getReg .x10 + 344).toNat ≤ y.toNat)
      (hy2 : y.toNat + 8 ≤ (s.getReg .x10).toNat + 360) : v.getMem y = u.getMem y :=
    hX y fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hy1, hy2, hS, hIs, hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hT.stream]
    apply hX.eListAt_stream
    · intro i hi hw; rcases hw with hw | hw <;> addr_omega [hw, hi, hS, hIs, hb]
    · rw [e0]; intro i hi hw
      rcases hw with hw | hw
      · addr_omega [hw, hi, hpa.1, hP, hS]
      · addr_omega [hw, hi, hPs.1, hP, hb]
    · rw [e1, e2]; intro i hi hw
      rcases hB with h0 | h0
      · rw [h0] at hi; omega
      rcases hw with hw | hw
      · addr_omega [hw, hi, hpa.2, h0, hS]
      · addr_omega [hw, hi, hPs.2, h0, hb]
  · rw [hsp, hT.sponge]
  · rw [keep _ (by addr_omega [hS]) (by addr_omega [hS]), hT.streamOffset]
  · rw [keep _ (by addr_omega [hS]) (by addr_omega [hS]), hT.openingOffset]

/-! ## `grow_one` of a `Vec<E>` in the frame -/

theorem callGrow24 (hG : GrowOneFreshSpec 0x80011c78 24 8) {s t : MachineState} {nx A : Word}
    (hpre : VsoPre s) (hinv : InvR s t nx) (hheap : HeapOk t) (hpc : t.pc = 0x80011c78)
    (hx10 : t.getReg .x10 = A)
    (hA : (s.getReg .x2 - 1040).toNat ≤ A.toNat ∧ A.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      A.toNat % 8 = 0)
    (hv : VecOk t A 24 8) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      DFrame t v (fun a ↦ Within a A 16 ∨ Within a (s.getReg .x2 - 1200) 160 ∨
        Within a nextAddr 8 ∨ Fresh t v a) ∧
      VecOk v A 24 8 ∧ vecEs v A = vecEs t A ∧ vecLen v A = vecLen t A ∧
      (vecCap t A).toNat + 1 ≤ (vecCap v A).toNat ∧
      NewBuf t v (vecPtr v A) ((vecCap v A).toNat * 24) 8)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := hinv.sp
  have hsl : stackLo t growOneStack = s.getReg .x2 - 1200 := by
    simp only [stackLo, growOneStack, hsp]; rv_eval []
  have hpreG : GrowOnePre 24 8 t := {
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
  have hbytes := hpost.bytes
  rw [hx10] at hcap hraw' hbytes
  have hhv := hpost.heap.hi
  have e2 : vecLen v A = vecLen t A := hfr _ fun i hi hx ↦ by
    rcases hx with hx | hx | hx | hx
    · addr_omega [hx, hi, hA]
    · addr_omega [hx, hi, hA, hb]
    · addr_omega [hx, hi, hA, hb, hnx]
    · simp only [Fresh] at hx; addr_omega [hx.2, hi, hA, hb, hhv]
  have hl := hv.len
  have hrawt := hv.raw
  have hraw2 := hraw'
  simp only [RawVecOk, Buf] at hrawt hraw2
  refine ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono, hfr, ⟨hraw', by rw [e2]; omega⟩, ?_,
    e2, hcap, hnew⟩⟩
  simp only [vecEs, e2]
  exact eListAt_eq_of_bytesAt (bytesAt_eq_iff.mpr fun i hi ↦ bytesAt_eq_iff.mp hbytes i (by
    omega)) hraw2.1 hrawt.1

/-! ## `poly_eval` into the frame -/

theorem callPolyEval (hPE : PolyEvalSpec) {s t : MachineState} {nx o p w c : Word}
    (hpre : VsoPre s) (hinv : InvR s t nx) (hpc : t.pc = 0x8000cef4)
    (hx10 : t.getReg .x10 = o) (hx11 : t.getReg .x11 = p) (hx12 : t.getReg .x12 = w)
    (hx13 : t.getReg .x13 = c)
    (ho : (s.getReg .x2 - 1040).toNat ≤ o.toNat ∧ o.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      o.toNat % 8 = 0)
    (hc : (s.getReg .x2 - 1040).toNat ≤ c.toNat ∧ c.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      c.toNat % 8 = 0)
    (hoc : Apart o 24 c 24)
    (hp : 24 * w.toNat = 0 ∨ heapStart ≤ p.toNat ∧ p.toNat + 24 * w.toNat ≤ heapEnd)
    (hp8 : p.toNat % 8 = 0) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      DFrame t v (fun a ↦ Within a o 24 ∨ Within a (s.getReg .x2 - 2464) 1424) ∧
      eAt v o = Model.polyEvalRust (eListAt t p w.toNat) (eAt t c))) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := hinv.sp
  have hsl : stackLo t polyEvalStack = s.getReg .x2 - 2160 := by
    simp only [stackLo, polyEvalStack, mulStack, hsp, Nat.reduceAdd]; rv_eval []
  have hpreP : PolyEvalPre t := {
    out := by rw [hx10]; exact stack_region hpre (by addr_omega [ho, hb]) (by addr_omega [ho, hb]) ho.2.2
    coeffs := by
      rw [hx11, hx12]
      rcases hp with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr (heap_region (by simp only [heapStart] at h0; omega) h0.2 hp8)
    point := by rw [hx13]; exact stack_region hpre (by addr_omega [hc, hb]) (by addr_omega [hc, hb]) hc.2.2
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    outStack := by rw [hx10, hsl]; addr_omega [ho, hb]
    coeffsStack := by
      rw [hx11, hx12, hsl]
      rcases hp with h0 | h0
      · exact Or.inl h0
      · simp only [heapEnd] at h0; addr_omega [h0.2, hb]
    pointStack := by rw [hx13, hsl]; addr_omega [hc, hb]
    outCoeffs := by
      rw [hx10, hx11, hx12]
      rcases hp with h0 | h0
      · exact Or.inr (Or.inl h0)
      · simp only [heapEnd] at h0; addr_omega [h0.2, ho, hb]
    outPoint := by rw [hx10, hx13]; exact hoc
    rodata := hinv.rodata' hpre
    outRodata := by
      rw [hx10]
      have := hst.rodata
      rw [stackLo_vso, vso_stack] at this
      addr_omega [this, ho, hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hPE.call (Reaches.refl t) hpc hpreP
  · have hfr := hpost.frame
    have hval := hpost.value
    rw [hx10, hsl] at hfr
    rw [hx10, hx11, hx12, hx13] at hval
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, hfr.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (by addr_omega [ha, hb]), hval⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-! ## `sumcheck_round_poly(3, claim, None)` into the frame -/

theorem callRoundPoly (hRP : RoundPolyErrSpec) {s t : MachineState} {nx o cl : Word}
    (hpre : VsoPre s) (hinv : InvR s t nx) (hheap : HeapOk t) (hpc : t.pc = 0x8000c334)
    (hx10 : t.getReg .x10 = o) (hx11 : t.getReg .x11 = s.getReg .x10) (hx12 : t.getReg .x12 = 3)
    (hx13 : t.getReg .x13 = cl) (hx14 : t.getReg .x14 = s.getReg .x2 - 384)
    (hnone : t.getMem (s.getReg .x2 - 384) = 0)
    (ho : (s.getReg .x2 - 1040).toNat ≤ o.toNat ∧ o.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      o.toNat % 8 = 0)
    (hc : (s.getReg .x2 - 1040).toNat ≤ cl.toNat ∧ cl.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      cl.toNat % 8 = 0) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      DFrame t v (fun a ↦ Within a o 24 ∨ Within a (s.getReg .x10 + 8) 344 ∨
        Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh t v a) ∧
      (vecCap v o = errNiche → v.getMem (o + 8) ≠ okTag) ∧
      (vecCap v o ≠ errNiche →
        VecOk v o 24 8 ∧ NewBuf t v (vecPtr v o) ((vecCap v o).toNat * 24) 8) ∧
      ∀ T, TranscriptAt t (s.getReg .x10) T →
        match (Model.TM.sumcheckRoundPoly 3 (eAt t cl) none).run T with
        | some (q, T') => vecCap v o ≠ errNiche ∧ NewVecE t v o q ∧
            TranscriptAt v (s.getReg .x10) T'
        | none => vecCap v o = errNiche)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, hro⟩ := sfacts hpre
  have hsp := hinv.sp
  have hI := hpre.self
  have hIs := hI.stack
  have hPs := hI.proofStack
  rw [stackLo_vso, vso_stack] at hIs hPs
  simp only [ProofApart] at hPs
  obtain ⟨hTok, e0, e1, e2⟩ := trR_facts hpre hinv
  have hsu : heapNext s ≤ heapNext t := by
    have hn : heapNext t = nx.toNat := by simp only [heapNext, hinv.next]
    rw [hn]; exact hinv.mono
  have hsl : stackLo t roundPolyStack = s.getReg .x2 - 2464 := by
    simp only [stackLo, roundPolyStack, nextScalarsStack, shuntNextStack, nextScalarStack,
      absorbStack, duplexStack, keccakFStack, memStack, hsp]
    addr_omega [hb]
  have hpreR : RoundPolyPre t := {
    heap := hheap
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
    outFree := by
      rw [hx10]; exact stack_outside hpre (by addr_omega [ho, hb]) (by addr_omega [ho, hb])
    selfFree := by rw [hx11]; exact outside_mono hI.free hsu
    proofFree := by rw [hx11, e0]; exact outside_mono hI.proofFree hsu
    streamFree := by rw [hx11, e1, e2]; exact outside_mono hI.streamFree hsu
    rodata := hinv.rodata' hpre
    outRodata := by rw [hx10]; addr_omega [hro, ho, hb]
    selfRodata := by rw [hx11]; exact hI.rodata
    count := by rw [hx12]; decide
    claim := by rw [hx13]; exact stack_region hpre (by addr_omega [hc, hb]) (by addr_omega [hc, hb]) hc.2.2
    eqFactor := by
      rw [hx14]; exact stack_region hpre (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
    claimFree := by
      rw [hx13]; exact stack_outside hpre (by addr_omega [hc, hb]) (by addr_omega [hc, hb])
    eqFactorFree := by rw [hx14]; exact stack_outside hpre (by addr_omega [hb]) (by addr_omega [hb])
    claimStack := by rw [hx13, hsl]; addr_omega [hc, hb]
    eqFactorStack := by rw [hx14, hsl]; addr_omega [hb]
    claimSelf := by rw [hx13, hx11]; addr_omega [hc, hIs, hb]
    eqFactorSelf := by rw [hx14, hx11]; addr_omega [hIs, hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost, herr⟩ | hdead⟩ := hRP.call (Reaches.refl t) hpc hpreR
  swap
  · exact ⟨v, hr, Or.inl hdead⟩
  have hfr := hpost.frame
  simp only [TFrame] at hfr
  rw [hx10, hx11, hsl] at hfr
  have hok := hpost.ok
  simp only [VecResult] at hok
  rw [hx10] at hok herr
  have hnone' : optEAt t (t.getReg .x14) = none := by
    rw [hx14, optEAt, ite_eq_left_of_eq_true _ _ (eq_true hnone)]
  refine ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono, hfr, herr, hok, fun T hT ↦ ?_⟩⟩
  have hv := hpost.value T (by rw [hx11]; exact hT)
  have h3 : ((3 : Word)).toNat = 3 := rfl
  rw [hx12, hx13, hnone', h3, hx10, hx11] at hv
  exact hv

end Rv64Verifier.Proofs.Pcs.Vso
