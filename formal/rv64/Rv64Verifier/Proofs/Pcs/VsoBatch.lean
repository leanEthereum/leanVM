import Rv64Verifier.Proofs.Pcs.VsoHead
import Rv64Verifier.Proofs.Transcript.Samples

/-!
# `verify_stacked_opening`: the batching challenge, the scales and the target

From `0x80009eb0` (the values copied): `duplex`, the challenge's lanes to `S - 384`,
`powers(S - 776, S - 384, n)`, `dot(S - 752, scales, values)`; at `0x80009f08` the mirror's first
three lines have run (`Batched`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts
  Rv64Verifier.MultilinearContracts Rv64Verifier.Blocks.F38 LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A call from the function's frame (`sp = S - 1040`) to a callee with a `k`-byte stack that
writes `X` (in the frame, below the saved registers), its stack, `NEXT` and the heap it
allocates. -/
theorem Inv.call {s u v : MachineState} {nx : Word} (hpre : VsoPre s) (h : Inv s u nx) {k : Nat}
    (hk : 1040 + k ≤ vsoStack) {X : Word → Prop}
    (hX : ∀ a, X a → Within a (s.getReg .x2 - 1040) 936)
    (hf : DFrame u v fun a ↦ X a ∨ Within a (stackLo u k) k ∨ Within a nextAddr 8 ∨ Fresh u v a)
    (hheap : HeapOk v) (hmono : heapNext u ≤ heapNext v) (hsp : v.getReg .x2 = u.getReg .x2) :
    Inv s v (v.getMem nextAddr) := by
  have hb := bounds hpre
  have hab := hpre.stack.above
  have hnx8 := hpre.stack.next
  have hsp₀ := h.sp
  have hn : heapNext u = nx.toNat := by simp only [heapNext, h.next]
  refine Inv.step' hpre h hf (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl
    (by simp only [heapNext] at hn hmono; omega) hheap.hi hsp
  · rcases ha with ha | ha | ha | ha
    · exact frame_wr hpre (hX a ha)
    · exact Or.inr (Or.inl (by
        simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
          shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack,
          stackLo, hsp₀] at ha hk ⊢
        addr_omega [ha, hb, hk]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨by simp only [Fresh] at ha; have := h.mono; omega,
        by simp only [Fresh, heapNext] at ha; exact ha.2⟩))
  · rcases ha with ha | ha | ha | ha
    · exact frame_slot hpre (hX a ha)
    · simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
        shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack,
        stackLo, hsp₀] at ha hk
      addr_omega [ha, hb, hk]
    · addr_omega [ha, hb, hnx8]
    · simp only [Fresh] at ha
      have := hheap.hi
      addr_omega [ha, hb, hab, this]

/-- At `0x80009f08`: the challenge drawn, its powers at `S - 776` (a new `Vec`), their dot product
with the values at `S - 752`. -/
structure Batched (s u : MachineState) (nx : Word) : Prop extends Args s u where
  inv : Inv s u nx
  pc : u.pc = 0x80009f08
  x25 : u.getReg .x25 = s.getReg .x10 + 8
  vec : VecOk u (s.getReg .x2 - 776) 24 8
  len : vecLen u (s.getReg .x2 - 776) = s.getReg .x15
  buf : NewBuf s u (vecPtr u (s.getReg .x2 - 776)) (24 * ncl s) 8
  value : ∀ T, TranscriptAt s (s.getReg .x10) T → ∃ c T', (Model.TM.sample).run T = some (c, T') ∧
    TranscriptAt u (s.getReg .x10) T' ∧
    vecEs u (s.getReg .x2 - 776) = Verifier.powers c (ncl s) ∧
    eAt u (s.getReg .x2 - 752) = Model.dotRust (Verifier.powers c (ncl s)) (valuesOf s)

theorem region_sub {a : Word} {n : Nat} (h : Region a n) (k m : Nat) (hk : k + m ≤ n)
    (h8 : k % 8 = 0) : Region (a + BitVec.ofNat 64 k) m := by
  obtain ⟨hM, hal⟩ := h
  simp only [Mapped] at hM
  simp only [Region, Mapped]
  rcases hM with hM | hM
  · exact ⟨Or.inl (by addr_omega [hM, hk]), by addr_omega [hal, h8, hM, hk]⟩
  · exact ⟨Or.inr (by addr_omega [hM, hk]), by addr_omega [hal, h8, hM, hk]⟩

/-- At `0x80009ec0`: the sponge duplexed, the transcript standing for the mirror's after
`TM.sample`. -/
structure Sampled (s u : MachineState) (nx VP : Word) : Prop extends Args s u where
  inv : Inv s u nx
  pc : u.pc = 0x80009ec0
  x25 : u.getReg .x25 = s.getReg .x10 + 8
  x23 : u.getReg .x23 = VP
  x24 : u.getReg .x24 = s.getReg .x15
  buf : VBuf s VP nx
  vals : ∀ i < ncl s, eAt u (VP + BitVec.ofNat 64 (24 * i)) = eAt s (claimAddr s i + 64)
  tr : ∀ T, TranscriptAt s (s.getReg .x10) T →
    TranscriptAt u (s.getReg .x10) { T with sponge := spDuplex T.sponge }

theorem sample {s u : MachineState} {nx VP : Word} (hD : DuplexSpec) (hpre : VsoPre s)
    (h : Copied s u nx VP) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ Sampled s v nx VP) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hnx8 := hst.next
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
    shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack,
    stackLo] at hIs
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009eb0_spec h.pc trivial
  have k₁ := b80009eb0_keeps h₁
  have hm₁ := b80009eb0_mem_same h₁
  have inv₁ : Inv0 s t₁ nx := h.inv.same' hm₁ (k₁ .x2 (by decide))
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := inv₁.sp
  have hx10₁ : t₁.getReg .x10 = s.getReg .x10 + 8 := by rw [b80009eb0_x10 h₁, h.x27]
  have hsl : stackLo t₁ duplexStack = s.getReg .x2 - 1920 := by
    simp only [stackLo, duplexStack, keccakFStack, memStack, hsp₁, Nat.reduceAdd]; rv_eval []
  have hpreD : DuplexPre t₁ := {
    sponge := by rw [hx10₁]; exact region_sub hI.ok.self 8 336 (by decide) (by decide)
    stack := hst.sub 1040 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    spongeStack := by rw [hx10₁, hsl]; addr_omega [hIs, hS, hb]
    rodata := inv₁.rodata hpre.rodata (fun _ h ↦ h.elim) hst.rodata
    spongeRodata := by rw [hx10₁]; have := hI.rodata; addr_omega [this, hS] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hD.call hr₁ (b80009eb0_pc h₁) hpreD
  swap
  · exact ⟨t₂, hr₂, Or.inl hdead⟩
  have hfr := hpost₂.frame
  rw [hx10₁, hsl] at hfr
  have hfree := hI.free
  simp only [Outside] at hfree
  have inv₂ : Inv s t₂ nx := Inv.step' (nx' := nx) hpre inv₁.toInv hfr
    (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by simp only [W]; addr_omega [ha, hS])
      · exact Or.inr (Or.inl (by
          simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack,
            nextScalarsStack, shuntNextStack, nextScalarStack, absorbStack, duplexStack,
            keccakFStack, memStack, stackLo]
          addr_omega [ha, hb])))
    (fun a ha ↦ by
      rcases ha with ha | ha
      · addr_omega [ha, hIs, hS, hb]
      · addr_omega [ha, hb])
    (by
      rw [hfr _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hfree.2, hS, hb, hnx8],
        inv₁.next])
    (Nat.le_refl _) inv₁.fits (hpres₂.reg .x2)
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x20, .x21, .x22, .x23, .x24, .x26, .x27]) :
      t₂.getReg r = u.getReg r := by
    rw [hpres₂ r (by simp only [calleeSaved]; exact Runtime.mem_of_mem hr _)]
    exact k₁ r (Runtime.mem_of_mem hr _)
  refine ⟨t₂, hr₂, Or.inr {
    toArgs := h.toArgs.of_eq fun r hr ↦ hreg r (by simp only [List.mem_cons] at hr ⊢; tauto)
    inv := inv₂
    pc := by rw [hpc₂, returnAddress_eq, b80009eb0_x1 h₁]; decide
    x25 := by
      rw [hpres₂ .x25 (by simp only [calleeSaved]; decide), b80009eb0_x25 h₁, h.x27]
    x23 := by rw [hreg .x23 (by decide), h.x23]
    x24 := by rw [hreg .x24 (by decide), h.x24]
    buf := h.buf
    vals := fun i hi ↦ by
      have hPr := h.buf.range.resolve_left (by omega)
      have hfit := inv₁.fits
      have hab := hst.above
      rw [DFrame.eAt hfr (p := VP + BitVec.ofNat 64 (24 * i)) fun j hj hw ↦ by
          simp only [ncl] at hi hPr
          rcases hw with hw | hw
          · rcases hfree.1 with h1 | h1
            · addr_omega [hw, hj, hi, hPr, h1, hS, hfit, hb, hab]
            · addr_omega [hw, hj, hi, hPr, h1, hS, hfit]
          · addr_omega [hw, hj, hi, hPr, hfit, hb, hab]]
      rw [show eAt t₁ (VP + BitVec.ofNat 64 (24 * i)) = eAt u (VP + BitVec.ofNat 64 (24 * i)) by
        unfold eAt; simp only [hm₁]]
      exact h.vals i hi
    tr := fun T hT ↦ by
      have h1 := Inv0.transcriptAt hpre inv₁ hT
      have hP := hI.ok.proof
      have hPs := hI.proofStack
      have hPf := hI.proofFree
      have hBs := hI.streamFree
      have hpa := hpre.proofSponge
      simp only [Outside, ProofApart] at hPf hBs hpa
      have hfit := inv₁.fits
      have hm0 := src_misses hfit hI.stack hI.free
      obtain ⟨e0, e1, e2⟩ := inv₁.mem.stream' (fun y hy ↦ hm0 y (by addr_omega [hy, hS]))
        (by addr_omega [hS]) (src_misses hfit hPs.1 hPf) (by have := hP; simp only [Region, Mapped] at this; addr_omega [this])
      have hPb := Region.bounds hP
      have hB : streamLen s (s.getReg .x10) = 0 ∨
          (streamPtr s (s.getReg .x10)).toNat + 24 * streamLen s (s.getReg .x10) ≤ 2 ^ 64 := by
        rcases hI.ok.stream with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (by have := Region.bounds h0; omega)
      have keep (y : Word) (hy1 : (s.getReg .x10 + 344).toNat ≤ y.toNat)
          (hy2 : y.toNat + 8 ≤ (s.getReg .x10).toNat + 360) : t₂.getMem y = t₁.getMem y :=
        hfr y fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hy1, hy2, hS, hIs, hb]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← h1.stream]
        apply hfr.eListAt_stream
        · intro i hi hw; rcases hw with hw | hw <;> addr_omega [hw, hi, hS, hIs, hb]
        · rw [e0]; intro i hi hw
          rcases hw with hw | hw
          · addr_omega [hw, hi, hpa.1, hPb, hS]
          · have := hPs.1; simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack,
              nextScalarsStack, shuntNextStack, nextScalarStack, absorbStack, duplexStack,
              keccakFStack, memStack, stackLo] at this
            addr_omega [hw, hi, this, hPb, hb]
        · rw [e1, e2]; intro i hi hw
          rcases hB with h0 | h0
          · rw [h0] at hi; omega
          rcases hw with hw | hw
          · addr_omega [hw, hi, hpa.2, h0, hS]
          · have := hPs.2; simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack,
              nextScalarsStack, shuntNextStack, nextScalarStack, absorbStack, duplexStack,
              keccakFStack, memStack, stackLo] at this
            addr_omega [hw, hi, this, h0, hb]
      · have := hpost₂.value
        rw [hx10₁] at this
        rw [this, h1.sponge]
      · rw [keep _ (by addr_omega [hS]) (by addr_omega [hS]), h1.streamOffset]
      · rw [keep _ (by addr_omega [hS]) (by addr_omega [hS]), h1.openingOffset] }⟩

theorem stack_outside {s u : MachineState} (hpre : VsoPre s) {a : Word} {n : Nat}
    (h1 : (s.getReg .x2 - 2464).toNat ≤ a.toNat) (h2 : a.toNat + n ≤ (s.getReg .x2).toNat) :
    Outside u a n := by
  have hb := bounds hpre
  have hab := hpre.stack.above
  have hnx8 := hpre.stack.next
  simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
    shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack,
    stackLo] at hab hnx8
  simp only [Outside]
  exact ⟨Or.inr (by addr_omega [hab, h1, hb]), by addr_omega [hnx8, h1, h2, hb]⟩

/-- **The scales and the target**: from `0x80009ec0`, `powers` and `dot`. -/
theorem target {s u : MachineState} {nx VP : Word} (hP : PowersSpec) (hDot : DotSpec)
    (hpre : VsoPre s) (h : Sampled s u nx VP) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ ∃ nx', Batched s v nx') := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
    shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack,
    stackLo] at hIs
  have hsp := h.inv.sp
  have hro := hst.rodata
  have hwro : ∀ a, W s a → ¬ Within a rodataBase Rv64Verifier.rodataSize := fun a ha hr ↦ by
    have := hI.rodata; simp only [W] at ha; addr_omega [ha, hr, this, hS]
  -- the challenge's lanes, and `powers`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009ec0_spec h.pc (by
    rv_eval [hsp, h.x27]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hI.ok.self (by addr_omega [hS]) (by addr_omega [hS]) (by addr_omega [hS]))
  have k₁ := b80009ec0_keeps h₁
  have hm₁ := b80009ec0_frame h₁ (by rw [hsp]; addr_omega [hb])
  rw [hsp] at hm₁
  rv_eval [] at hm₁
  have inv₁ : Inv s t₁ nx := Inv.step' hpre h.inv (DFrame.of_memFrame hm₁)
    (fun a ha ↦ frame_wr hpre (by addr_omega [ha, hb]))
    (fun a ha ↦ by addr_omega [ha, hb])
    ((hm₁ _ (by addr_omega [hb, hnx8])).trans h.inv.next) (Nat.le_refl _) h.inv.fits
    (k₁ .x2 (by decide))
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := inv₁.sp
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 776 := by rw [b80009ec0_x10 h₁, hsp]; rv_eval []
  have hx11₁ : t₁.getReg .x11 = s.getReg .x2 - 384 := by rw [b80009ec0_x11 h₁, hsp]; rv_eval []
  have hx12₁ : t₁.getReg .x12 = s.getReg .x15 := by rw [b80009ec0_x12 h₁, h.x20]
  have hslP : stackLo t₁ powersStack = s.getReg .x2 - 2208 := by
    simp only [stackLo, powersStack, mulStack, hsp₁, Nat.reduceAdd]; rv_eval []
  have hfit := inv₁.fits
  have hn₁ : heapNext t₁ = nx.toNat := by simp only [heapNext, inv₁.next]
  have hpreP : PowersPre t₁ := {
    heap := inv₁.heap hpre.heap
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    base := by rw [hx11₁]; valid_sub hst.valid [hb]
    stack := hst.sub 1040 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [hx10₁]; exact stack_outside hpre (by addr_omega [hb]) (by addr_omega [hb])
    outStack := by rw [hx10₁, hslP]; addr_omega [hb]
    outRodata := by rw [hx10₁]; addr_omega [hro, hb]
    baseFree := by rw [hx11₁]; exact stack_outside hpre (by addr_omega [hb]) (by addr_omega [hb])
    baseStack := by rw [hx11₁, hslP]; addr_omega [hb]
    baseOut := by rw [hx11₁, hx10₁]; addr_omega [hb]
    rodata := inv₁.rodata hpre.rodata hwro hro }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ :=
    hP.call hr₁ (b80009ec0_pc h₁) hpreP
  swap
  · exact ⟨t₂, hr₂, Or.inl hdead⟩
  have hfr₂ : DFrame t₁ t₂ fun a ↦ Within a (s.getReg .x2 - 776) 24 ∨
      Within a (stackLo t₁ powersStack) powersStack ∨ Within a nextAddr 8 ∨ Fresh t₁ t₂ a := by
    have := hpost₂.frame; simp only [PowersW, hx10₁] at this; exact this
  have inv₂ : Inv s t₂ (t₂.getMem nextAddr) := Inv.call hpre inv₁ (by decide)
    (fun a ha ↦ by addr_omega [ha, hb]) hfr₂ hpost₂.heap hpost₂.mono (hpres₂.reg .x2)
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := inv₂.sp
  have hlen₂ : vecLen t₂ (s.getReg .x2 - 776) = s.getReg .x15 := by
    have := hpost₂.len; rw [hx10₁, hx12₁] at this; exact this
  have hnew₂ := hpost₂.fresh
  rw [hx10₁, hx12₁] at hnew₂
  -- `dot`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009eec_spec
    (by rw [hpc₂, returnAddress_eq, b80009ec0_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      and_intros <;> valid_access hst.valid [hb])
  have k₃ := b80009eec_keeps h₃
  have hm₃ := b80009eec_mem_same h₃
  have inv₃ : Inv s t₃ (t₂.getMem nextAddr) := Inv.same' inv₂ hm₃ (k₃ .x2 (by decide))
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := inv₃.sp
  set PP := vecPtr t₂ (s.getReg .x2 - 776) with hPP
  have hreg₂ (r : Reg) (hr : r ∈ [Reg.x8, .x20, .x21, .x22, .x23, .x24, .x26, .x27]) :
      t₃.getReg r = u.getReg r := by
    rw [k₃ r (Runtime.mem_of_mem hr _), hpres₂ r (by simp only [calleeSaved]; exact Runtime.mem_of_mem hr _),
      k₁ r (Runtime.mem_of_mem hr _)]
  have hx10₃ : t₃.getReg .x10 = s.getReg .x2 - 752 := by rw [b80009eec_x10 h₃, hsp₂]; rv_eval []
  have hx11₃ : t₃.getReg .x11 = PP := by
    rw [b80009eec_x11 h₃, hsp₂, hPP, vecPtr]; rv_eval []
  have hx12₃ : t₃.getReg .x12 = s.getReg .x15 := by
    rw [b80009eec_x12 h₃, hsp₂, ← hlen₂, vecLen]; rv_eval []
  have hx13₃ : t₃.getReg .x13 = VP := by
    rw [b80009eec_x13 h₃, hpres₂ .x23 (by decide), k₁ .x23 (by decide), h.x23]
  have hx14₃ : t₃.getReg .x14 = s.getReg .x15 := by
    rw [b80009eec_x14 h₃, hpres₂ .x24 (by decide), k₁ .x24 (by decide), h.x24]
  have hslD : stackLo t₃ dotStack = s.getReg .x2 - 2160 := by
    simp only [stackLo, dotStack, mulStack, hsp₃, Nat.reduceAdd]; rv_eval []
  have hfit₂ := hpost₂.heap.hi
  have hn₂ : heapNext t₂ = (t₂.getMem nextAddr).toNat := rfl
  have hVr := h.buf.range
  have hVa := h.buf.align
  have hlo := hpre.heap.lo
  have hm₁n := h.inv.mono
  simp only [ncl] at hVr
  have hPPb : (s.getReg .x15).toNat = 0 ∨
      (nx.toNat ≤ PP.toNat ∧ PP.toNat + 24 * (s.getReg .x15).toNat ≤ heapNext t₂) := by
    rcases hnew₂.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by rw [← hn₁]; exact h0.1, h0.2⟩
  have vrange (a : Word) (ha : a.toNat % 8 = 0) (hr : (s.getReg .x15).toNat = 0 ∨
      (heapNext s ≤ a.toNat ∧ a.toNat + 24 * (s.getReg .x15).toNat ≤ heapNext t₂)) :
      ValidMemRange a (3 * (s.getReg .x15).toNat) := by
    rcases hr with h0 | h0
    · intro i hi; omega
    · simp only [heapStart] at hlo
      exact Region.vrange (heap_region (a := a) (n := 24 * (s.getReg .x15).toNat) (by omega)
        (by omega) ha) (by omega) (by omega) ha
  have hpreD : DotPre t₃ := {
    ret := by rw [hx10₃]; valid_sub hst.valid [hb]
    left := by
      rw [hx11₃, hx12₃]
      exact vrange PP hnew₂.1 (by rcases hPPb with h0 | h0
                                  · exact Or.inl h0
                                  · exact Or.inr ⟨by omega, h0.2⟩)
    right := by
      rw [hx13₃, hx14₃]
      exact vrange VP hVa (by rcases hVr with h0 | h0
                              · exact Or.inl h0
                              · exact Or.inr ⟨h0.1, by have := hpost₂.mono; omega⟩)
    stack := (hst.sub 1040 hsp₃ (by decide) (by decide) (by decide) (by decide) (by decide)).toStackOk
    retLeft := by
      rw [hx10₃, hx11₃, hx12₃]
      rcases hPPb with h0 | h0
      · simp [Apart, h0]
      · addr_omega [h0, hfit₂, hab, hb]
    retRight := by
      rw [hx10₃, hx13₃, hx14₃]
      rcases hVr with h0 | h0
      · simp [Apart, h0]
      · addr_omega [h0, hfit, hab, hb]
    retStack := by rw [hx10₃, hslD]; addr_omega [hb]
    leftStack := by
      rw [hx11₃, hx12₃, hslD]
      rcases hPPb with h0 | h0
      · simp [Apart, h0]
      · addr_omega [h0, hfit₂, hab, hb]
    rightStack := by
      rw [hx13₃, hx14₃, hslD]
      rcases hVr with h0 | h0
      · simp [Apart, h0]
      · addr_omega [h0, hfit, hab, hb]
    rodata := inv₃.rodata hpre.rodata hwro hro
    retRodata := by rw [hx10₃]; addr_omega [hro, hb]
    stackRodata := by rw [hslD]; addr_omega [hro, hb] }
  obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hdead⟩ :=
    hDot.call hr₃ (b80009eec_pc h₃) hpreD
  swap
  · exact ⟨t₄, hr₂.trans hr₄, Or.inl hdead⟩
  have hfr₄ := hpost₄.frame
  rw [hx10₃, hslD] at hfr₄
  have hD₄ := DFrame.of_two hfr₄
  have hnext₄ : t₄.getMem nextAddr = t₂.getMem nextAddr := by
    rw [hfr₄ _ (by addr_omega [hb, hnx8]) (by addr_omega [hb, hnx8]), hm₃]
  have inv₄ : Inv s t₄ (t₂.getMem nextAddr) := Inv.step' hpre inv₃ hD₄
    (fun a ha ↦ by
      rcases ha with ha | ha
      · exact frame_wr hpre (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl (by
          simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack,
            nextScalarsStack, shuntNextStack, nextScalarStack, absorbStack, duplexStack,
            keccakFStack, memStack, stackLo]
          addr_omega [ha, hb])))
    (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb])
    hnext₄ (Nat.le_refl _) inv₃.fits (hpres₄.reg .x2)
  have hn₄ : heapNext t₄ = heapNext t₂ := by simp only [heapNext, hnext₄]
  have keep4 (y : Word) (h1 : (s.getReg .x2 - 776).toNat ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2 - 752).toNat) : t₄.getMem y = t₂.getMem y := by
    rw [hfr₄ y (by addr_omega [h1, h2, hb]) (by addr_omega [h1, h2, hb]), hm₃]
  have w0 : t₄.getMem (s.getReg .x2 - 776) = t₂.getMem (s.getReg .x2 - 776) :=
    keep4 _ (by addr_omega [hb]) (by addr_omega [hb])
  have w1 : t₄.getMem (s.getReg .x2 - 776 + 8) = t₂.getMem (s.getReg .x2 - 776 + 8) :=
    keep4 _ (by addr_omega [hb]) (by addr_omega [hb])
  have w2 : t₄.getMem (s.getReg .x2 - 776 + 16) = t₂.getMem (s.getReg .x2 - 776 + 16) :=
    keep4 _ (by addr_omega [hb]) (by addr_omega [hb])
  have hvec₂ := hpost₂.vec
  rw [hx10₁] at hvec₂
  have hvec : VecOk t₄ (s.getReg .x2 - 776) 24 8 := by
    refine ⟨?_, ?_⟩
    · have r := hvec₂.raw
      simp only [RawVecOk, Buf, vecCap, vecPtr] at r ⊢
      rw [w0, w1, hn₄]; exact r
    · have l := hvec₂.len
      simp only [vecCap, vecLen] at l ⊢
      rw [w0, w2]; exact l
  have hPP4 : vecPtr t₄ (s.getReg .x2 - 776) = PP := by simp only [vecPtr, hPP]; rw [w1]
  have hlen4 : vecLen t₄ (s.getReg .x2 - 776) = s.getReg .x15 := by
    simp only [vecLen] at hlen₂ ⊢; rw [w2]; exact hlen₂
  -- the buffers `dot` and `powers` leave alone
  have hPP3 : eListAt t₃ PP (s.getReg .x15).toNat = Verifier.powers (eAt t₁ (s.getReg .x2 - 384))
      (s.getReg .x15).toNat := by
    have he := hpost₂.elems
    rw [hx10₁, hx11₁, hx12₁] at he
    rw [← he]
    simp only [vecEs, ← hPP, hlen₂, eListAt, eAt, hm₃]
  have hPPe : eListAt t₄ PP (s.getReg .x15).toNat = Verifier.powers (eAt t₁ (s.getReg .x2 - 384))
      (s.getReg .x15).toNat := by
    rw [hD₄.eListAt fun i hi hw ↦ by
        rcases hPPb with h0 | h0
        · omega
        · rcases hw with hw | hw <;> addr_omega [hw, hi, h0, hfit₂, hab, hb]]
    exact hPP3
  have hVPe : eListAt t₃ VP (s.getReg .x15).toNat = valuesOf s := by
    have e1 : eListAt t₃ VP (s.getReg .x15).toNat = eListAt t₁ VP (s.getReg .x15).toNat := by
      rw [show eListAt t₃ VP (s.getReg .x15).toNat = eListAt t₂ VP (s.getReg .x15).toNat by
        simp only [eListAt, eAt, hm₃]]
      exact hfr₂.eListAt fun i hi hw ↦ by
        rcases hVr with h0 | h0
        · omega
        · simp only [Fresh] at hw
          rcases hw with hw | hw | hw | hw
          · addr_omega [hw, hi, h0, hfit, hab, hb]
          · rw [hslP] at hw; addr_omega [hw, hi, h0, hfit, hab, hb]
          · addr_omega [hw, hi, h0, hfit, hnx8, hb]
          · rw [hn₁] at hw; addr_omega [hw, hi, h0]
    have e2 : eListAt t₁ VP (s.getReg .x15).toNat = eListAt u VP (s.getReg .x15).toNat :=
      (DFrame.of_memFrame hm₁).eListAt fun i hi hw ↦ by
        rcases hVr with h0 | h0
        · omega
        · addr_omega [hw, hi, h0, hfit, hab, hb]
    rw [e1, e2]
    simp only [eListAt, valuesOf, claimsAt, ncl, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    simp only [Function.comp, stackClaimAt]
    exact h.vals i (by simp only [ncl]; exact hi)
  -- what the calls since `u` wrote: the stack, `NEXT`, the heap from `nx`
  have hX : DFrame u t₄ fun a ↦ Within a (s.getReg .x2 - 2464) 2464 ∨ Within a nextAddr 8 ∨
      (nx.toNat ≤ a.toNat ∧ a.toNat < heapNext t₂) := by
    refine (((DFrame.of_memFrame hm₁).mono fun a ha ↦ Or.inl (by addr_omega [ha, hb])).trans
      hfr₂ fun a ha ↦ ?_).trans ((DFrame.of_same hm₃ _).trans hD₄ fun a ha ↦ ha) fun a ha ↦ ?_
    · simp only [Fresh] at ha
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · rw [hslP] at ha; exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ⟨by rw [← hn₁]; exact ha.1, ha.2⟩)
    · rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
  have missX (a : Word) (n : Nat) (hs : Apart a n (stackLo s vsoStack) vsoStack)
      (hf : Outside s a n) : Misses (fun a ↦ Within a (s.getReg .x2 - 2464) 2464 ∨
        Within a nextAddr 8 ∨ (nx.toNat ≤ a.toNat ∧ a.toNat < heapNext t₂)) a n := by
    simp only [Outside] at hf
    simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
      shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack,
      stackLo] at hs
    intro y hy hw
    rcases hw with hw | hw | hw
    · addr_omega [hy, hw, hs, hb]
    · addr_omega [hy, hw, hf.2]
    · rcases hf.1 with h1 | h1
      · addr_omega [hy, hw.1, h1, hm₁n]
      · addr_omega [hy, hw.2, h1, hfit₂]
  have hpa := hpre.proofSponge
  simp only [ProofApart] at hpa
  have hP := Region.bounds hI.ok.proof
  have hm8 : Misses (Wr s vsoStack (W s) nx) (s.getReg .x10) 8 := fun y hy hW ↦ by
    rcases hW with hW | hW
    · simp only [W] at hW; addr_omega [hy, hW, hS]
    · exact src_misses h.inv.fits hI.stack hI.free y (by addr_omega [hy, hS]) (Or.inr hW)
  have hm48 : Misses (Wr s vsoStack (W s) nx) (proofAt s (s.getReg .x10)) 48 := fun y hy hW ↦ by
    rcases hW with hW | hW
    · simp only [W] at hW; addr_omega [hy, hW, hpa.1, hP]
    · exact src_misses h.inv.fits hI.proofStack.1 hI.proofFree y hy (Or.inr hW)
  obtain ⟨e0, e1, e2⟩ := h.inv.mem.stream' hm8 (by omega) hm48 (by omega)
  have hTok : TranscriptOk u (s.getReg .x10) := h.inv.mem.transcriptOk hI.ok hm8 hm48
  have hreg₄ (r : Reg) (hr : r ∈ [Reg.x8, .x20, .x21, .x22, .x26, .x27]) :
      t₄.getReg r = u.getReg r := by
    rw [hpres₄ r (by simp only [calleeSaved]; exact Runtime.mem_of_mem hr _)]
    exact hreg₂ r ((List.Sublist.subset (by decide :
      [Reg.x8, .x20, .x21, .x22, .x26, .x27].Sublist [Reg.x8, .x20, .x21, .x22, .x23, .x24, .x26,
        .x27])) hr)
  have hc (T : Model.TState) (hT : TranscriptAt s (s.getReg .x10) T) :
      eAt t₁ (s.getReg .x2 - 384) = (spSqueeze T.sponge).1 := by
    have hsq : (spSqueeze T.sponge).1 = Compile.challengeOf (spDuplex T.sponge).state := rfl
    have hsp' : spongeAt u (s.getReg .x10 + 8) = spDuplex T.sponge := (h.tr T hT).sponge
    rw [hsq, ← hsp']
    show _ = Compile.challengeOf (stateAt u (s.getReg .x10 + 8 + 128))
    rw [Samples.challengeOf_stateAt]
    have m0 := b80009ec0_m_x2_656 h₁
    have m1 := b80009ec0_m_x2_664 h₁
    have m2 := b80009ec0_m_x2_672 h₁
    rw [hsp, h.x27] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    unfold eAt
    rv_eval [m0, m1, m2]
  refine ⟨t₄, hr₂.trans hr₄, Or.inr ⟨_, {
    toArgs := h.toArgs.of_eq hreg₄
    inv := inv₄
    pc := by rw [hpc₄, returnAddress_eq, b80009eec_x1 h₃]; decide
    x25 := by
      rw [hpres₄ .x25 (by simp only [calleeSaved]; decide), k₃ .x25 (by decide),
        hpres₂ .x25 (by simp only [calleeSaved]; decide), k₁ .x25 (by decide), h.x25]
    vec := hvec
    len := hlen4
    buf := by
      rw [hPP4]
      refine ⟨hnew₂.1, ?_⟩
      rcases hnew₂.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨by rw [hn₁] at h0; omega, by rw [hn₄]; exact h0.2⟩
    value := fun T hT ↦ ⟨(spSqueeze T.sponge).1, { T with sponge := (spSqueeze T.sponge).2 }, rfl,
      ?_, ?_, ?_⟩ }⟩⟩
  · have hsq : (spSqueeze T.sponge).2 = spDuplex T.sponge := rfl
    rw [hsq]
    exact hX.transcriptAt (h.tr T hT) hTok
      (fun y hy ↦ missX _ 368 hI.stack hI.free y (by addr_omega [hy, hS]))
      (by rw [e0]; exact missX _ 48 hI.proofStack.1 hI.proofFree)
      (by rw [e1, e2]; exact missX _ _ hI.proofStack.2 hI.streamFree)
      (fun y hy ↦ missX _ 368 hI.stack hI.free y (by addr_omega [hy, hS]))
  · simp only [vecEs, hPP4, hlen4, ncl]
    rw [hPPe, hc T hT]
  · have hv := hpost₄.value
    rw [hx10₃, hx11₃, hx12₃, hx13₃, hPP3, hVPe, hc T hT] at hv
    exact hv

/-- **The first three lines of `verify_stacked_opening`**: from the entry to `0x80009f08`, the
batching challenge drawn, the scales and the target in the frame, or a dead end. -/
theorem head (hT : TryAllocZeroedSpec) (hD : DuplexSpec) (hP : PowersSpec) (hDot : DotSpec)
    {s : MachineState} (hpc : s.pc = 0x80009db8) (hpre : VsoPre s) :
    ∃ v, Reaches Image.code s v ∧ (Dead Image.code v ∨ ∃ nx, Batched s v nx) := by
  obtain ⟨u₁, h₁, hu₁⟩ := setup hT hpc hpre
  rcases hu₁ with hd | ⟨nx, VP, hu₁⟩
  · exact ⟨u₁, h₁, Or.inl hd⟩
  obtain ⟨u₂, h₂, hu₂⟩ := copy hpre hu₁
  obtain ⟨u₃, h₃, hu₃⟩ := sample hD hpre hu₂
  rcases hu₃ with hd | hu₃
  · exact ⟨u₃, h₁.trans (h₂.trans h₃), Or.inl hd⟩
  obtain ⟨u₄, h₄, hu₄⟩ := target hP hDot hpre hu₃
  exact ⟨u₄, h₁.trans (h₂.trans (h₃.trans h₄)), hu₄⟩

end Rv64Verifier.Proofs.Pcs.Vso

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.head
