import Rv64Verifier.Proofs.Walk.Calls
import Rv64Verifier.Proofs.Transcript.NextScalar
import Rv64Verifier.Proofs.Transcript.NextScalarsModel

/-!
# `walk`: `next_scalars(8)`

`announcedCall`: the announced sizes' `next_scalars(8)` into `S - 928`. Its `Err` is copied to the
result (`0x800011a8`) and the function returns; otherwise, at `0x8000116c`, the `Vec` at `S - 928`
holds the scalars and the code runs `walkRust` past them, and the stream is not empty: they were
read from it.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem byteAt_congr {u v : MachineState} {a : Word} (ha : a.toNat % 8 = 0)
    (h : v.getMem a = u.getMem a) : byteAt v a = byteAt u a := by
  rw [byteAt_of_within ha (le_refl _) (by omega), byteAt_of_within ha (le_refl _) (by omega), h]

/-- A `Vec` whose words are kept keeps its shape. -/
theorem NewVecE.same {s u v : MachineState} {a : Word} {xs : List E} (h : NewVecE s u a xs)
    (hm : ∀ x, v.getMem x = u.getMem x) : NewVecE s v a (vecEs v a) := by
  obtain ⟨⟨hr, hl⟩, hb, -⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_, rfl⟩
  · simp only [RawVecOk, Buf, vecPtr, vecCap, heapNext, hm] at hr ⊢; exact hr
  · simp only [vecLen, vecCap, hm] at hl ⊢; exact hl
  · simp only [NewBuf, vecPtr, vecCap, heapNext, hm] at hb ⊢; exact hb

/-- What `walk` runs once the announced scalars `a` are read. -/
def afterScalars (s : MachineState) (a : List E) : TM SummaryRust :=
  ((TM.require (a.all fun value ↦ value.limb 1 = 0 ∧ value.limb 2 = 0) >>= fun _ ↦
    announcedTail (Proofs.Bytecode.readBytecode s (s.getReg .x11)) a) >>=
      bodyRest (Proofs.Bytecode.readBytecode s (s.getReg .x11)) (bytesAt s (s.getReg .x12) 32)) >>=
    finishRust

/-- Reading `n > 0` scalars needs one left. -/
theorem stream_pos {n : Nat} {T T' : TState} {xs : List E} (hn : 0 < n)
    (h : (TM.nextScalars n).run T = some (xs, T')) : T.streamOffset < T.proof.stream.length := by
  by_contra hc
  rw [nextScalars_fail (d := 0) (T' := T) (xs := []) rfl
    (NextScalar.nextScalar_none (List.getElem?_eq_none (by omega))) hn] at h
  cases h

/-- At `0x8000116c`: the scalars in the `Vec` at `S - 928`, `s0`/`s1` its buffer and length; the
stream is not empty. -/
structure Announced (OI : MachineState → Word → List (List Opening) → Prop)
    (s v : MachineState) : Prop where
  inv : Inv s v
  regs : Regs s v
  proofPtr : v.getMem (tp s) = s.getReg .x13
  checked : byteAt v (tp s + 360) = 1
  x8 : v.getReg .x8 = vecPtr v (s.getReg .x2 - 928)
  x9 : v.getReg .x9 = vecLen v (s.getReg .x2 - 928)
  vec : NewVecE s v (s.getReg .x2 - 928) (vecEs v (s.getReg .x2 - 928))
  tracks : Tracks OI s v (afterScalars s (vecEs v (s.getReg .x2 - 928)))
  streamNE : (vecLen s (s.getReg .x13)).toNat ≠ 0

theorem announcedCall (hNS : NextScalarsSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u : MachineState} (hpre : WalkPre s) (hpc : u.pc = 0x80004818) (h : Start OI s u) :
    ∃ v, Reaches Image.code u v ∧
      ((v.pc = 0x8000116c ∧ Announced OI s v) ∨ Done OI s v ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have pre : NextScalarsPre u := tpre hpre h.inv h.proofPtr (k := 928) (n := 24)
    (m := nextScalarsStack) (by omega) (by omega) (by omega) (by decide) (by decide) h.x10 h.x11
  obtain ⟨w, hr, ⟨hpcw, hpw, post⟩ | hd⟩ := hNS.call (Reaches.refl u) hpc pre
  swap
  · exact ⟨w, hr, Or.inr (Or.inr hd)⟩
  have st := TFrame.stepT hpre h.inv (k := 928) (by decide) h.x10 h.x11 post.frame post.heap
    post.mono (hpw.reg .x2)
  have Iw := h.inv.afterT hpre (inFrame hpre (by omega) (by omega)) st
  have spw : w.getReg .x2 = s.getReg .x2 - 2656 := Iw.sp
  have ptrw : w.getMem (tp s) = s.getReg .x13 := by
    rw [← h.proofPtr]; exact st.word hpre (by rw [tp]; addr_omega [hb1]) (by rw [tp]; addr_omega [hb1])
      (by rw [tp]; addr_omega [hb1])
  obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80001158_spec
    (by rw [hpcw, returnAddress_eq, h.x1]; decide) (by
      rv_eval [spw]
      and_intros <;> valid_access hval [hb1])
  have k₂ := b80001158_keeps h₂
  have hm₂ := b80001158_mem_same h₂
  have Iv := Iw.same hm₂ (k₂ .x2 (by decide))
  have e928 : w.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [spw]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have regs : Regs s v := h.regs.keep fun r hr ↦ by
    rw [k₂ r (mem_of_mem hr _), hpw.reg r (mem_six hr)]
  by_cases hc : w.getMem (w.getReg .x2 + 1728) = (0xffffffffffffffff : Word)
  · -- `Err`: copied to the result, return
    have hR := hpre.out
    have hO := hpre.outStack
    rw [stackLo_eq, stack_eq] at hO
    have x23 : v.getReg .x23 = s.getReg .x10 := regs.x23
    obtain ⟨t, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800011a8_spec (b80001158_pc_taken h₂ hc) (by
      rv_eval [x23]
      and_intros <;> exact Region.valid hR (by addr_omega [hR]) (by addr_omega [hR])
        (by addr_omega [hR]))
    have fr₀ := b800011a8_frame h₃ (by rw [x23]; addr_omega [hR])
    rw [x23] at fr₀
    have fr := DFrame.of_memFrame fr₀
    have hx := hpre.outFree.2
    have he : heapNext t = heapNext v := by
      simp only [heapNext]
      exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by addr_omega [hx, hw, hi])
    have It : Inv s t := Iv.step hpre fr
      (fun a ha ↦ ⟨Or.inl (by addr_omega [ha, hR]), by addr_omega [ha, hO, hb1]⟩)
      ⟨he ▸ Iv.heap.lo, he ▸ Iv.heap.hi⟩ he.ge (b800011a8_keeps h₃ .x2 (by decide))
    obtain ⟨t', hr₄, hd⟩ := errExit (OI := OI) hpre It (b800011a8_pc h₃) (by
      rw [← x23, b800011a8_m_x23_0 h₃, b80001158_x10 h₂]; rfl)
    exact ⟨t', hr.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inl hd)⟩
  · -- `Ok`
    refine ⟨v, hr.trans hr₂, Or.inl ⟨b80001158_pc_not_taken h₂ hc, {
      inv := Iv
      regs := regs
      proofPtr := by rw [hm₂]; exact ptrw
      checked := ?_
      x8 := by
        have a8 : w.getReg .x2 + 1736 = s.getReg .x2 - 928 + 8 := by
          rw [spw]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
        rw [b80001158_x8 h₂, a8, vecPtr, hm₂]
      x9 := by
        have a16 : w.getReg .x2 + 1744 = s.getReg .x2 - 928 + 16 := by
          rw [spw]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
        rw [b80001158_x9 h₂, a16, vecLen, hm₂]
      vec := ?_
      tracks := ?_
      streamNE := ?_ }⟩⟩
    · have ha : (tp s + 360).toNat % 8 = 0 := by rw [tp]; addr_omega [hb1, hb3]
      rw [byteAt_congr ha (hm₂ _), byteAt_congr ha (st.word hpre (by rw [tp]; addr_omega [hb1])
        (by rw [tp]; addr_omega [hb1]) (by rw [tp]; addr_omega [hb1]))]
      exact h.checked
    · have hok := post.ok
      rw [h.x10] at hok
      obtain ⟨hv, hb⟩ := hok (by rw [vecCap, ← e928]; exact hc)
      exact NewVecE.same (u := w) (NewVecE.widen' ⟨hv, hb, rfl⟩ h.inv.mono) hm₂
    · have tr := h.tracks
      unfold prog at tr
      rw [walkRust_announced] at tr
      refine Tracks.bind (v := v) tr (KeepsProof.nextScalars _) fun T hT ↦ ?_
      have hv := post.value T (by rw [h.x11]; exact hT)
      have e8 : (u.getReg .x12).toNat = 2 + LayoutMirror.nTablesRust := by rw [h.x12]; rfl
      rw [e8, h.x10, h.x11] at hv
      split at hv
      · rename_i xs T' heq
        obtain ⟨-, hn, hT'⟩ := hv
        refine ⟨T', ?_, TranscriptAt.same hpre Iw ptrw hm₂ hT'⟩
        rw [heq]
        congr
        rw [← hn.elems]
        simp only [vecEs, vecPtr, vecLen, hm₂, eListAt, eAt]
      · exact absurd (by rw [vecCap, ← e928] at hv; exact hv) hc
    · have hT₀ : TranscriptAt u (u.getReg .x11)
          ⟨⟨eListAt u (streamPtr u (u.getReg .x11)) (streamLen u (u.getReg .x11)), []⟩,
            spongeAt u (u.getReg .x11 + 8), (u.getMem (u.getReg .x11 + 344)).toNat,
            (u.getMem (u.getReg .x11 + 352)).toNat, []⟩ := ⟨rfl, rfl, rfl, rfl⟩
      have hv := post.value _ hT₀
      have e8 : (u.getReg .x12).toNat = 2 + LayoutMirror.nTablesRust := by rw [h.x12]; rfl
      rw [e8, h.x10] at hv
      split at hv
      · rename_i xs T' heq
        have hp := stream_pos (by decide) heq
        simp only [eListAt_length] at hp
        rw [h.x11, (proofVals hpre h.inv h.proofPtr).2.2] at hp
        omega
      · exact absurd (by rw [vecCap, ← e928] at hv; exact hv) hc

/-- **From the entry to the announced sizes' check** (`0x8000116c`), or the function has returned
`Err`, or the run reached a dead end. -/
theorem toScalars (hMS : MemsetSpec 0x800126f4) (hMC : MemcpySpec 0x800126e4)
    (hK : Contracts.KeccakFSpec) (hNS : NextScalarsSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s : MachineState}
    (hpc : s.pc = 0x80000ef8) (hpre : WalkPre s) :
    ∃ v, Reaches Image.code s v ∧
      ((v.pc = 0x8000116c ∧ Announced OI s v) ∨ Done OI s v ∨ Dead Image.code v) := by
  obtain ⟨u, r₁, ⟨p₁, h₁⟩ | d⟩ := start hMS hMC hK (OI := OI) hpc hpre
  · obtain ⟨v, r₂, hv⟩ := announcedCall hNS hpre p₁ h₁
    exact ⟨v, r₁.trans r₂, hv⟩
  · exact ⟨u, r₁, Or.inr (Or.inr d)⟩

end Rv64Verifier.Proofs.Walk
