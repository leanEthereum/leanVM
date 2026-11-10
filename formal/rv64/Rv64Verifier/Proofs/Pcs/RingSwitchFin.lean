import Rv64Verifier.Proofs.Pcs.RingSwitchImgLoop

/-!
# `ring_switch`: `poly_eval` and the epilogue

`0x80009b00` calls `poly_eval(out, I, n, GEN)`; `0x80009b20` moves `point` (read through the
pointer saved at `F`) and the coefficients' `Vec` (`F + 152`) into the result, restores and
returns (`fin`).
-/

namespace Rv64Verifier.Proofs.Pcs.RingSwitch
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F36
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem limbs_gen : Model.limbs LeanVM.Protocol.Verifier.gen = (2, 0, 0) := by decide +kernel

/-- `GEN` in `.rodata`. -/
theorem gen_at {u : MachineState} (h : RodataOk u) : eAt u 0xa00000c8 = LeanVM.Protocol.Verifier.gen := by
  apply eAt_eq_of_limbs
  rw [limbs_gen]
  rv_eval [h.word (a := 0xa00000c8) (v := 2), h.word (a := 0xa00000d0) (v := 0),
    h.word (a := 0xa00000d8) (v := 0)]

/-- What the function may write after `B2`: the images loop's, and the result. -/
def w3 (s : MachineState) (I : Word) (a : Word) : Prop := w2 s I a ∨ Within a (s.getReg .x10) 72

/-- An input of the function, read in place: not written from entry to `t`. -/
theorem src_miss {s t : MachineState} (hpre : RingSwitchPre s) (ht : heapNext t ≤ heapEnd)
    {a : Word} {n : Nat} (hs : Src s ringSwitchStack a n) (ho : Apart (s.getReg .x10) 72 a n)
    (hp : Apart a n (s.getReg .x14 + 8) 344) :
    ∀ x, Within x a n → ¬ (Within x (s.getReg .x10) 72 ∨ W0 s x ∨ Fresh s t x) := by
  have hb := bounds hpre
  have hS := hs.stack
  have hF := hs.free
  simp only [Outside] at hF
  intro x hx hW
  rcases hW with hW | (hW | hW | hW) | hW
  · addr_omega [hx, hW, ho]
  · addr_omega [hx, hW, hp]
  · addr_omega [hx, hW, hS, hb]
  · addr_omega [hx, hW, hF.2]
  · simp only [Fresh] at hW
    rcases hF.1 with h1 | h1
    · addr_omega [hx, hW.1, h1]
    · addr_omega [hx, hW.2, h1, ht]

/-- The transcript across a frame from `B` on that misses it: `w` only in the stack frame, the
heap allocated since `s`, or the result. -/
theorem tr_move' {s B B' : MachineState} {w : Word → Prop} {nx : Word} (hpre : RingSwitchPre s)
    (hs : heapNext s ≤ heapNext B) (hf : DFrame B B' (Wr B 1120 w nx))
    (hspB : B.getReg .x2 = s.getReg .x2 - 464) (hfit : nx.toNat ≤ heapEnd)
    (hw : ∀ a, w a → ((s.getReg .x2).toNat - 464 ≤ a.toNat ∧ a.toNat < (s.getReg .x2).toNat) ∨
      (heapNext s ≤ a.toNat ∧ a.toNat < heapEnd) ∨ Within a (s.getReg .x10) 72)
    (heq : proofAt B (s.getReg .x14) = proofAt s (s.getReg .x14) ∧
      streamPtr B (s.getReg .x14) = streamPtr s (s.getReg .x14) ∧
      streamLen B (s.getReg .x14) = streamLen s (s.getReg .x14))
    (hok : TranscriptOk B (s.getReg .x14)) :
    ∀ T, TranscriptAt B (s.getReg .x14) T → TranscriptAt B' (s.getReg .x14) T := by
  have hb := bounds hpre
  have hTi := hpre.self
  have hP := Region.bounds hTi.ok.self
  have hQ := Region.bounds hTi.ok.proof
  simp only [transcriptSize] at hP
  have hTS := hTi.stack
  have hPS := hTi.proofStack
  have hfree := hTi.free
  have hpfree := hTi.proofFree
  have hsfree := hTi.streamFree
  have hoS := hpre.outSelf
  have hoP := hpre.outProof
  simp only [Outside] at hfree hpfree hsfree
  simp only [ProofApart, transcriptSize] at hoP hoS
  have hmiss (x : Word) (h1 : x.toNat < (s.getReg .x2).toNat - 1584 ∨ (s.getReg .x2).toNat ≤ x.toNat)
      (h2 : x.toNat < heapNext s ∨ heapEnd ≤ x.toNat) (h3 : ¬ Within x nextAddr 8)
      (h4 : ¬ Within x (s.getReg .x10) 72) : ¬ Wr B 1120 w nx x := by
    rintro (hW | hW | hW | hW)
    · rcases hw x hW with hW | hW | hW
      · omega
      · omega
      · exact h4 hW
    · simp only [stackLo, hspB] at hW; addr_omega [hW, h1, hb]
    · exact h3 hW
    · omega
  obtain ⟨h1, h2, h3⟩ := heq
  intro T hT
  refine transcriptAt_frame hf hT hok
    (fun x hx ↦ hmiss x (by addr_omega [hx, hP, hTS, hb]) (by addr_omega [hx, hP, hfree.1])
      (by addr_omega [hx, hP, hfree.2]) (by addr_omega [hx, hP, hoS]))
    (fun x hx ↦ by
      rw [h1] at hx
      exact hmiss x (by addr_omega [hx, hQ, hPS.1, hb]) (by addr_omega [hx, hQ, hpfree.1])
        (by addr_omega [hx, hQ, hpfree.2]) (by addr_omega [hx, hQ, hoP.1]))
    (fun x hx ↦ by
      rw [h2, h3] at hx
      exact hmiss x (by addr_omega [hx, hPS.2, hb]) (by addr_omega [hx, hsfree.1])
        (by addr_omega [hx, hsfree.2]) (by addr_omega [hx, hoP.2]))

theorem run_ringSwitch {T T' : Model.TState} {ch : List E} (point sl : List E)
    (h : (Model.TM.samples 6).run T = some (ch, T')) :
    (ringSwitchRust point sl).run T = some ((Model.polyEvalRust (sl.map fun v ↦ ringMapRust v ch)
      LeanVM.Protocol.Verifier.gen, ⟨point, ringCoefficientsRust ch⟩), T') := by
  rw [ringSwitchRust, StateT.run_bind, show ringMapShiftsRust.length = 6 from rfl, h]
  rfl

section
variable {s B2 u : MachineState} {C chP I nx : Word} {ch : List E}

theorem fin (hPE : MultilinearContracts.PolyEvalSpec) (hpre : RingSwitchPre s)
    (hctx : Ctx2 s B2 C chP I ch) (he : IExit s B2 u I ch nx) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ RingSwitchPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp : u.getReg .x2 = s.getReg .x2 - 464 := he.ph.sp.trans hctx.sp
  have hH := hctx.heap.hi
  have hC := hctx.cHi
  have hI := hctx.iR
  have hiA := hctx.iA
  have hcL := hctx.chLo
  have hcC := hctx.chC
  have hlo := hpre.heap.lo
  simp only [heapStart] at hlo
  have hO := hpre.out.region
  have hOb := Region.bounds hO
  have hOs := hpre.out.stack
  have hOf := hpre.out.free
  have hOr := hpre.out.rodata
  simp only [Outside] at hOf
  have hout : u.getMem (s.getReg .x2 - 456) = s.getReg .x10 :=
    (keepF2 hpre hctx he.ph (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans hctx.out
  have hiP : u.getMem (s.getReg .x2 - 440) = I :=
    (keepF2 hpre hctx he.ph (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans hctx.iP
  -- `poly_eval`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009b00_spec he.pc (by
    rv_eval [hsp]
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80009b00_keeps h₁
  have hm₁ := b80009b00_mem_same h₁
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 464 := (k₁ .x2 (by decide)).trans hsp
  have hx10₁ : t₁.getReg .x10 = s.getReg .x10 := by rw [b80009b00_x10 h₁, hsp]; rv_eval [hout]
  have hx8₁ : t₁.getReg .x8 = s.getReg .x10 := by rw [b80009b00_x8 h₁, hsp]; rv_eval [hout]
  have hx11₁ : t₁.getReg .x11 = I := by rw [b80009b00_x11 h₁, hsp]; rv_eval [hiP]
  have hx12₁ : (t₁.getReg .x12).toNat = nS s := by
    rw [b80009b00_x12 h₁, he.x21]
    have hR := hpre.slices.region
    rcases hR with h0 | hR
    · simp only [nS]; rw [show (s.getReg .x13).toNat = 0 by omega]; rfl
    · have := Region.bounds hR; simp only [nS] at this ⊢; addr_omega [this]
  have hsl₁ : stackLo t₁ MultilinearContracts.polyEvalStack = s.getReg .x2 - 1584 := by
    simp only [stackLo, MultilinearContracts.polyEvalStack, mulStack, hsp₁, Nat.reduceAdd]; rv_eval []
  have ph₁ := (he.ph.widen (w' := w3 s I) fun a ha ↦ Or.inl ha).same hm₁ (k₁ .x2 (by decide))
  have hro₁ := rodataU2 hpre hctx (he.ph.same hm₁ (k₁ .x2 (by decide)))
  have hgR : Region (0xa00000c8 : Word) 24 := by simp only [Region, Mapped]; decide
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hPE.call hr₁ (b80009b00_pc h₁) {
    ret := by rw [hx10₁]; exact Region.vrange hO (by omega) (by omega) hOb.2.2
    coeffs := by
      rw [hx11₁, hx12₁]
      simp only [nS] at hI ⊢
      rcases hI with hI | hI
      · rw [hI]; intro i hi; omega
      · exact MultilinearWords.heap_valid_range hiA (by simp only [heapStart]; omega)
          (by simp only [heapEnd] at hH ⊢; omega)
    point := by rw [b80009b00_x13 h₁]; exact Region.vrange hgR (by decide) (by decide) (by decide)
    stack := (hst.sub 464 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)).toStackOk
    retCoeffs := by
      rw [hx10₁, hx11₁, hx12₁]
      simp only [nS] at hI ⊢
      rcases hI with hI | hI
      · rw [hI]; simp [Apart]
      · rcases hOf.1 with h1 | h1
        · addr_omega [h1, hI.1, hcL, hcC]
        · addr_omega [h1, hI.2, hH]
    retPoint := by rw [hx10₁, b80009b00_x13 h₁]; addr_omega [hOr]
    retStack := by
      rw [hx10₁, hsl₁]; simp only [MultilinearContracts.polyEvalStack, mulStack]
      addr_omega [hOs, hb]
    coeffsStack := by
      rw [hx11₁, hx12₁, hsl₁]; simp only [MultilinearContracts.polyEvalStack, mulStack]
      simp only [nS] at hI ⊢
      rcases hI with hI | hI
      · rw [hI]; simp [Apart]
      · addr_omega [hI.2, hH, hb]
    pointStack := by
      rw [b80009b00_x13 h₁, hsl₁]; simp only [MultilinearContracts.polyEvalStack, mulStack]
      addr_omega [hb]
    rodata := hro₁
    retRodata := by rw [hx10₁]; addr_omega [hOr]
    stackRodata := by
      rw [hsl₁]; simp only [MultilinearContracts.polyEvalStack, mulStack]; addr_omega [hb] }
  swap
  · exact ⟨t₂, hr₂, Or.inr hd⟩
  have hv₂ := hpost₂.value
  rw [hx10₁, hx11₁, hx12₁, b80009b00_x13 h₁, gen_at hro₁] at hv₂
  have hf₂ := hpost₂.frame
  rw [hx10₁, hsl₁] at hf₂
  simp only [MultilinearContracts.polyEvalStack, mulStack, Nat.reduceAdd] at hf₂
  have ph₂ := ph₁.step (dframe_of_two hf₂)
    (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (Or.inr (by addr_omega [ha]))
      · exact Or.inr (Or.inl (by simp only [stackLo, hctx.sp]; addr_omega [ha, hb])))
    ((hf₂ _ (by addr_omega [hOf.2]) (by addr_omega [hb])).trans ph₁.next)
    (Nat.le_refl _) ph₁.fits (hpres₂.reg .x2)
  -- what `t₂` keeps
  have hfB2 := hctx.frame
  have hn₂ : heapNext t₂ = nx.toNat := by simp only [heapNext, ph₂.next]
  have hm₂ : heapNext B2 ≤ heapNext t₂ := hn₂ ▸ ph₂.mono
  have hmo := hctx.mono
  have hfs₂ : DFrame s t₂ fun a ↦ Within a (s.getReg .x10) 72 ∨ W0 s a ∨ Fresh s t₂ a := by
    refine (hfB2.mono fun a ha ↦ ?_).trans ph₂.mem fun a ha ↦ ?_
    · rcases ha with ha | ha
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh] at ha ⊢
        exact Or.inr (Or.inr ⟨ha.1, by omega⟩)
    · rcases ha with ((ha | ha) | ha) | ha | ha | ha
      · exact Or.inr (Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb]))))
      · simp only [nS] at hI ha
        rcases hI with hI | hI
        · simp only [hI] at ha; addr_omega [ha]
        · exact Or.inr (Or.inr ⟨by addr_omega [ha, hI.1, hcL, hcC], by addr_omega [ha, hI.2, hm₂]⟩)
      · exact Or.inl ha
      · simp only [stackLo, hctx.sp] at ha
        exact Or.inr (Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb]))))
      · exact Or.inr (Or.inl (Or.inr (Or.inr ha)))
      · exact Or.inr (Or.inr ⟨by omega, by rw [hn₂]; exact ha.2⟩)
  have kB (a : Word) (h1 : (s.getReg .x2).toNat - 464 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 288 ∨
        (s.getReg .x2).toNat - 104 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₂.getMem a = B2.getMem a := by
    have hfit := ph₂.fits
    refine DFrame.word ph₂.mem (fun x hx hW ↦ ?_) (by addr_omega [h2, hb])
    rcases hW with ((hW | hW) | hW) | hW | hW | hW
    · addr_omega [hW, hx, h1, h2, hb]
    · simp only [nS] at hI hW
      rcases hI with hI | hI
      · simp only [hI] at hW; addr_omega [hW]
      · addr_omega [hW, hx, h1, hI.2, hH, hb]
    · addr_omega [hW, hx, h1, h2, hOs, hb]
    · simp only [stackLo, hctx.sp] at hW; addr_omega [hW, hx, h1, h2, hb]
    · addr_omega [hW, hx, h1, hb]
    · addr_omega [hW.2, hx, h1, hfit, hb]
  have hP := hpre.point
  have hPR := hP.region.resolve_left (by decide)
  have hPRb := Region.bounds hPR
  have kP (k : Nat) (hk : k = 0 ∨ k = 8 ∨ k = 16) :
      t₂.getMem (s.getReg .x11 + BitVec.ofNat 64 k) = s.getMem (s.getReg .x11 + BitVec.ofNat 64 k) :=
    hfs₂.word (fun x hx ↦ src_miss hpre (by rw [hn₂]; exact ph₂.fits) hP hpre.outPoint
      hpre.pointSponge x (by addr_omega [hx, hk, hPRb])) (by addr_omega [hk, hPRb])
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 464 := (hpres₂.reg .x2).trans hsp₁
  have hx8₂ : t₂.getReg .x8 = s.getReg .x10 := (hpres₂.reg .x8).trans hx8₁
  have hpt₂ : t₂.getMem (s.getReg .x2 - 464) = s.getReg .x11 :=
    (kB _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))).trans hctx.pt
  -- the epilogue
  obtain ⟨t, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009b20_spec
    (by rw [hpc₂, returnAddress_eq, b80009b00_x1 h₁]; decide) (by
      rv_eval [hsp₂, hx8₂, hpt₂]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid hPR (by addr_omega [hPRb]) (by addr_omega [hPRb]) (by addr_omega [hPRb])
        | exact Region.valid hO (by addr_omega [hOb]) (by addr_omega [hOb]) (by addr_omega [hOb])
        | addr_omega [hOs, hOb, hb])
  have hm₃ := b80009b20_frame h₃ (by rw [hx8₂]; addr_omega [hOb])
  rw [hx8₂] at hm₃
  have hmem₃ : DFrame B2 t (Wr B2 1120 (w3 s I) nx) :=
    ph₂.mem.trans (DFrame.of_memFrame hm₃) fun a ha ↦ Or.inl (Or.inr (by addr_omega [ha, hOb]))
  have hnt : t.getMem nextAddr = nx := (hm₃ _ (by addr_omega [hOf.2, hOb])).trans ph₂.next
  have hnT : heapNext t = nx.toNat := by simp only [heapNext, hnt]
  have hfit := ph₂.fits
  have hHt : HeapOk t := ⟨by rw [hnT]; have := hpre.heap.lo; omega, by rw [hnT]; exact hfit⟩
  have hfs : DFrame s t fun a ↦ Within a (s.getReg .x10) 72 ∨ W0 s a ∨ Fresh s t a :=
    (hfs₂.mono fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh, hn₂] at ha ⊢; rw [hnT]; exact Or.inr (Or.inr ha)).trans
      (DFrame.of_memFrame hm₃) fun a ha ↦ Or.inl (by addr_omega [ha, hOb])
  have hmiss (a : Word) (n : Nat) (hs : Src s ringSwitchStack a n)
      (ho : Apart (s.getReg .x10) 72 a n) (hp : Apart a n (s.getReg .x14 + 8) 344) :
      ∀ x, Within x a n → ¬ (Within x (s.getReg .x10) 72 ∨ W0 s x ∨ Fresh s t x) :=
    src_miss hpre (by rw [hnT]; exact hfit) hs ho hp
  -- the words read back
  have e24 := b80009b20_m_x8_24 h₃
  have e32 := b80009b20_m_x8_32 h₃
  have e40 := b80009b20_m_x8_40 h₃
  have e48 := b80009b20_m_x8_48 h₃
  have e56 := b80009b20_m_x8_56 h₃
  have e64 := b80009b20_m_x8_64 h₃
  rw [hx8₂, hsp₂] at e24 e32 e40 e48 e56 e64
  rv_eval [hpt₂] at e24 e32 e40 e48 e56 e64
  rw [kB _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), hctx.c0] at e48
  rw [kB _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), hctx.c1] at e56
  rw [kB _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), hctx.c2] at e64
  have p0 := kP 0 (Or.inl rfl)
  have p8 := kP 8 (Or.inr (Or.inl rfl))
  have p16 := kP 16 (Or.inr (Or.inr rfl))
  rv_eval [] at p0 p8 p16
  rw [p0] at e24
  rw [p8] at e32
  rw [p16] at e40
  -- the coefficients
  have kC (a : Word) (h0 : C.toNat ≤ a.toNat) (h1 : a.toNat + 8 ≤ C.toNat + 1536) :
      t.getMem a = B2.getMem a := by
    rw [hm₃ a (by rcases hOf.1 with h | h <;> addr_omega [h, h0, h1, hcL, hcC, hC, hH, hOb]),
      DFrame.word ph₂.mem (fun x hx hW ↦ ?_) (by addr_omega [h1, hC, hH])]
    rcases hW with ((hW | hW) | hW) | hW | hW | hW
    · addr_omega [hW, hx, h1, hC, hH, hb]
    · simp only [nS] at hI hW
      rcases hI with hI | hI
      · simp only [hI] at hW; addr_omega [hW]
      · addr_omega [hW, hx, h1, hI.1]
    · rcases hOf.1 with h | h <;> addr_omega [hW, hx, h, h0, h1, hcL, hcC, hC, hH]
    · simp only [stackLo, hctx.sp] at hW; addr_omega [hW, hx, h1, hC, hH, hb]
    · addr_omega [hW, hx, h1, hC, hH]
    · addr_omega [hW.1, hx, h1, hC]
  have hcoef : eListAt t C 64 = ringCoefficientsRust ch := by
    apply List.ext_getElem (by rw [eListAt_length, coeffs_length])
    intro l h1 h2
    rw [eListAt_length] at h1
    rw [eListAt_getElem, ← List.getD_eq_getElem _ 0 h2, coeffs_getD ch l h1, ← hctx.coeffs l h1]
    unfold eAt
    rw [kC _ (by addr_omega [h1, hC, hH]) (by addr_omega [h1, hC, hH]),
      kC _ (by addr_omega [h1, hC, hH]) (by addr_omega [h1, hC, hH]),
      kC _ (by addr_omega [h1, hC, hH]) (by addr_omega [h1, hC, hH])]
  -- the images
  have himg : eListAt t₁ I (nS s) =
      (eListAt s (s.getReg .x12) (nS s)).map fun v ↦ ringMapRust v ch := by
    apply List.ext_getElem (by simp [eListAt_length])
    intro l h1 h2
    rw [eListAt_length] at h1
    rw [List.getElem_map, eListAt_getElem, eListAt_getElem]
    simp only [eAt, hm₁]
    exact he.buf l h1
  -- the registers
  have sl : ∀ p ∈ slots, t₂.getMem (s.getReg .x2 - BitVec.ofNat 64 p.1) = s.getReg p.2 := by
    intro p hp
    have hb8 : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 ≤ 104 := by decide
    obtain ⟨h8, h104⟩ := hb8 p hp
    rw [kB _ (by addr_omega [h8, h104, hb]) (Or.inr ⟨by addr_omega [h8, h104, hb],
      by addr_omega [h8, h104, hb]⟩)]
    exact hctx.slots p hp
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  rv_eval [] at sl
  obtain ⟨s1, s8, s9, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27⟩ := sl
  have pc := b80009b20_pc h₃
  have x2 := b80009b20_x2 h₃
  have x8 := b80009b20_x8 h₃
  have x9 := b80009b20_x9 h₃
  have x18 := b80009b20_x18 h₃
  have x19 := b80009b20_x19 h₃
  have x20 := b80009b20_x20 h₃
  have x21 := b80009b20_x21 h₃
  have x22 := b80009b20_x22 h₃
  have x23 := b80009b20_x23 h₃
  have x24 := b80009b20_x24 h₃
  have x25 := b80009b20_x25 h₃
  have x26 := b80009b20_x26 h₃
  have x27 := b80009b20_x27 h₃
  rv_eval [hsp₂, s1, s8, s9, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27] at pc x2 x8 x9 x18
  rv_eval [hsp₂, s19, s20, s21, s22, s23, s24, s25, s26, s27] at x19 x20 x21 x22 x23 x24 x25 x26 x27
  have hcap : vecCap t (s.getReg .x10 + 48) = 64 := e48
  have hptr : vecPtr t (s.getReg .x10 + 48) = C := by simp only [vecPtr]; rv_eval [e56]
  have hlen : vecLen t (s.getReg .x10 + 48) = 64 := by simp only [vecLen]; rv_eval [e64]
  have hlC := hpre.heap.lo
  have hCe : vecEs t (s.getReg .x10 + 48) = ringCoefficientsRust ch := by
    rw [vecEs, hptr, hlen]; exact hcoef
  have hPB : Src s ringSwitchStack (s.getMem (s.getReg .x11 + 8))
      (24 * (s.getMem (s.getReg .x11 + 16)).toNat) := hpre.pointBuf
  have hPBo : Apart (s.getReg .x10) 72 (s.getMem (s.getReg .x11 + 8))
      (24 * (s.getMem (s.getReg .x11 + 16)).toNat) := hpre.outPointBuf
  have hPBs : Apart (s.getMem (s.getReg .x11 + 8)) (24 * (s.getMem (s.getReg .x11 + 16)).toNat)
      (s.getReg .x14 + 8) 344 := hpre.pointBufSponge
  have hph2 := ph₂.mono
  refine ⟨t, hr₂.trans hr₃, Or.inl ⟨pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 x19 fun r hr' ↦ ?_, {
      heap := hHt
      mono := by rw [hnT]; have := ph₂.mono; omega
      value := fun T hT ↦ ?_
      frame := ?_ }⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact x20
    · exact x21
    · exact x22
    · exact x23
    · exact x24
    · exact x25
    · exact x26
    · exact x27
  · obtain ⟨T', hrun, hT'⟩ := hctx.value T hT
    refine ⟨(Model.polyEvalRust ((eListAt s (s.getReg .x12) (nS s)).map fun v ↦ ringMapRust v ch)
      LeanVM.Protocol.Verifier.gen, ⟨vecEs s (s.getReg .x11), ringCoefficientsRust ch⟩), T', ?_,
      ?_, ?_, e24, ?_, ?_, ⟨⟨?_, ?_⟩, ?_, hCe⟩, ?_⟩
    · exact run_ringSwitch _ _ hrun
    · rw [← himg, ← hv₂]
      exact DFrame.eAt' (DFrame.of_memFrame hm₃) (fun x hx hW ↦ by addr_omega [hx, hW, hOb])
        (by addr_omega [hOb])
    · show (⟨vecEs t (s.getReg .x10 + 24), vecEs t (s.getReg .x10 + 24 + 24)⟩ : RingWeightRust) =
        ⟨vecEs s (s.getReg .x11), ringCoefficientsRust ch⟩
      rw [RingWeightRust.mk.injEq]
      refine ⟨?_, ?_⟩
      · simp only [vecEs, vecPtr, vecLen]
        rv_eval [e32, e40]
        refine DFrame.eList hfs (fun x hx ↦ hmiss _ _ hPB hPBo hPBs x hx) ?_
        rcases hPB.region with h0 | hR
        · left; omega
        · right; have := Region.bounds hR; omega
      · rw [show s.getReg .x10 + 24 + 24 = s.getReg .x10 + 48 by rv_eval []]; exact hCe
    · exact e32
    · exact e40
    · simp only [RawVecOk, Buf, hptr, hcap, show (64 : Word).toNat = 64 from rfl]
      exact ⟨hctx.cA, Or.inr ⟨by simp only [heapStart] at hlC ⊢; omega, by rw [hnT]; omega⟩⟩
    · rw [hlen, hcap]
    · simp only [NewBuf, hptr, hcap, show (64 : Word).toNat = 64 from rfl]
      exact ⟨hctx.cA, Or.inr ⟨by omega, by rw [hnT]; omega⟩⟩
    · exact tr_move' hpre hmo hmem₃ hctx.sp hfit (fun a ha ↦ by
        rcases ha with (ha | ha) | ha
        · exact Or.inl (by addr_omega [ha, hb])
        · simp only [nS] at hI ha
          rcases hI with hI | hI
          · simp only [hI] at ha; addr_omega [ha]
          · exact Or.inr (Or.inl (by addr_omega [ha, hI.1, hI.2, hcL, hcC, hH]))
        · exact Or.inr (Or.inr ha)) hctx.trEq hctx.tok T' hT'
  · refine hfs.mono fun a ha ↦ ?_
    rcases ha with ha | (ha | ha | ha) | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl (by simp only [stackLo, ringSwitchStack,
        MultilinearContracts.polyEvalStack, mulStack]; addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ha)))

end

end Rv64Verifier.Proofs.Pcs.RingSwitch
