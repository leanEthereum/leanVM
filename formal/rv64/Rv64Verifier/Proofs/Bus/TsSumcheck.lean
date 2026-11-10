import Rv64Verifier.Proofs.Bus.TsCalls

/-!
# `table_sumcheck`: `sumcheck`

`0x800080cc` calls `sumcheck(transcript, target, 4, &vec![None; n_rounds])` into `S - 152`; an
`Err` returns through `0x800084e0` (`errExit`), an `Ok` reaches `0x80008100` (`AfterSumcheck`).
Every transcript the entry's stands for is followed: the transcript is a function of memory, so
one (`exists_transcriptAt`) fixes the values the code computes.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The function returns with its contract, or reaches a dead end. -/
def Done (s t : MachineState) : Prop :=
  (t.pc = returnAddress s ∧ Preserves s t ∧ TableSumcheckPost s t) ∨ Dead Image.code t

/-- The mirror on the entry's arguments. -/
def mirror (s : MachineState) : TM (List (List E × List E)) :=
  tableSumcheckM (tablesAt s (s.getReg .x11) (s.getReg .x12).toNat)
    (natsAt s (s.getReg .x13) (s.getReg .x14).toNat)
    (formRowsAt s (s.getReg .x15) (s.getReg .x16).toNat)
    (eListAt s (s.getReg .x17) (s.getReg .x28).toNat)
    (eListAt s (s.getReg .x29) (s.getReg .x30).toNat)
    (eListAt s (s.getReg .x31) (tsEqLen s).toNat) (eAt s (tsTarget s))

theorem exists_transcriptAt (s : MachineState) (p : Word) : ∃ T, TranscriptAt s p T :=
  ⟨⟨⟨eListAt s (streamPtr s p) (streamLen s p), []⟩, spongeAt s (p + 8),
    (s.getMem (p + 344)).toNat, (s.getMem (p + 352)).toNat, []⟩, rfl, rfl, rfl, rfl⟩

theorem _root_.Rv64Verifier.Transcript.NewVecE.weaken {s u t : MachineState} {a : Word} {xs : List E} (h : NewVecE u t a xs)
    (hm : heapNext s ≤ heapNext u) : NewVecE s t a xs := by
  obtain ⟨hv, ⟨h1, h2⟩, he⟩ := h
  exact ⟨hv, ⟨h1, by omega⟩, he⟩

theorem eAt_of_same {s t : MachineState} (h : ∀ a, t.getMem a = s.getMem a) (a : Word) :
    eAt t a = eAt s a :=
  (DFrame.of_same h fun _ ↦ False).eAt fun _ _ h ↦ h

theorem optEListAt_of_same {s t : MachineState} (h : ∀ a, t.getMem a = s.getMem a) (a : Word)
    (n : Nat) : optEListAt t a n = optEListAt s a n := by
  simp only [optEListAt, optEAt, h, eAt_of_same h]

/-- A `Vec<E>` whose header and elements miss a frame keeps them. -/
theorem _root_.Rv64Verifier.Transcript.NewVecE.dframe {s t t' : MachineState} {w : Word → Prop}
    {a : Word} {xs : List E}
    (h : NewVecE s t a xs) (hf : DFrame t t' w) (hn : heapNext t ≤ heapNext t')
    (ha : ∀ i < 24, ¬ w (a + BitVec.ofNat 64 i))
    (hb : ∀ i < 24 * (vecLen t a).toNat, ¬ w (vecPtr t a + BitVec.ofNat 64 i)) :
    NewVecE s t' a xs := by
  have off (k : Nat) (hk : k + 8 ≤ 24) : t'.getMem (a + BitVec.ofNat 64 k) =
      t.getMem (a + BitVec.ofNat 64 k) :=
    hf _ fun i hi ↦ by rw [add_ofNat_add]; exact ha _ (by omega)
  have e0 : vecCap t' a = vecCap t a := by
    have := off 0 (by omega); simp only [add_ofNat_zero] at this; exact this
  have e1 : vecPtr t' a = vecPtr t a := off 8 (by omega)
  have e2 : vecLen t' a = vecLen t a := off 16 (by omega)
  obtain ⟨⟨hr, hl⟩, hb', he⟩ := h
  simp only [RawVecOk, Buf, NewBuf, heapStart] at hr hb'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [RawVecOk, Buf, heapStart, e0, e1]; omega
  · rw [e0, e2]; exact hl
  · simp only [NewBuf, e0, e1]; omega
  · simp only [vecEs, e1, e2]; rw [← he]; exact hf.eListAt hb

theorem _root_.Rv64Verifier.Transcript.NewVecE.of_same {s t t' : MachineState} {a : Word}
    {xs : List E} (h : NewVecE s t a xs)
    (hm : ∀ a, t'.getMem a = t.getMem a) : NewVecE s t' a xs :=
  h.dframe (DFrame.of_same hm fun _ ↦ False) (by simp only [heapNext, hm]; exact le_refl _)
    (fun _ _ h ↦ h) fun _ _ h ↦ h

theorem Inv.same {s u v : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u)
    (hm : ∀ a, v.getMem a = u.getMem a) (hsp : v.getReg .x2 = u.getReg .x2) : Inv s v := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact h.step hpre (DFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim)
    ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩ hn.ge hsp

/-- The local writes and those to the target and the transcript's sponge and offsets. -/
def LocT (s u v : MachineState) (a : Word) : Prop :=
  Loc s u v a ∨ Within a (tsTarget s) 24 ∨ Within a (tsSelf s + 8) 344

theorem Inv.locT {s u v : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u)
    (hf : DFrame u v (LocT s u v)) (heap : HeapOk v) (mono : heapNext u ≤ heapNext v)
    (sp : v.getReg .x2 = u.getReg .x2) : Inv s v := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have tst := hpre.targetStack
  have ss := hpre.selfStack
  have hS := hpre.self.self
  simp only [stack_eq] at tst ss
  refine h.step hpre hf (fun a ha ↦ ?_) heap mono sp
  rcases ha with ha | ha | ha
  · exact Loc.w hpre h heap ha
  · exact ⟨Or.inr (Or.inl ha), by addr_omega [ha, tst, hb1]⟩
  · exact ⟨Or.inr (Or.inr (Or.inl ha)), by addr_omega [ha, ss, hS, hb1]⟩

/-- `Err` at `0x8000893c`: the function returns it, the mirror failing. -/
theorem errExit {s u : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u)
    (hpc : u.pc = 0x8000893c) (hcap : vecCap u (s.getReg .x10) = errNiche)
    (hnone : ∀ T, TranscriptAt s (tsSelf s) T → (mirror s).run T = none) :
    ∃ t, Reaches Image.code u t ∧ Done s t := by
  obtain ⟨t, hr, hpc', hp, hm⟩ := epilogue hpre h hpc
  have hn : heapNext t = heapNext u := by simp only [heapNext, hm]
  refine ⟨t, hr, Or.inl ⟨hpc', hp, ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩, hn ▸ h.mono,
    fun T hT ↦ ?_, fun a ha ↦ ?_⟩⟩
  · have e := hnone T hT
    simp only [mirror] at e
    rw [e]
    exact (hm _).trans hcap
  · rw [hm a]
    exact h.frame a fun i hi hw ↦ ha i hi (W.mono hn.ge hw)

/-- At `0x800080cc`: `vec![None; n_rounds]` at `S - 248`, the target and the transcript as at
the entry. -/
structure AtSumcheck (s v : MachineState) : Prop where
  inv : Inv s v
  regs : Regs s v
  args : Args s v
  len : (vecLen v (s.getReg .x2 - 248)).toNat = nRounds s
  buf : NewBuf s v (vecPtr v (s.getReg .x2 - 248)) (32 * nRounds s) 8
  elems : optEListAt v (vecPtr v (s.getReg .x2 - 248)) (nRounds s) =
    List.replicate (nRounds s) none
  below : (vecPtr v (s.getReg .x2 - 248)).toNat ≤ heapNext v
  target : eAt v (tsTarget s) = eAt s (tsTarget s)
  tr : ∀ T, TranscriptAt s (tsSelf s) T → TranscriptAt v (tsSelf s) T

/-- At `0x80008100`: `sumcheck` returned `Ok((challenges, claim))` at `S - 152`. -/
structure AfterSumcheck (s w : MachineState) (ch : List E) (cl : E) : Prop where
  inv : Inv s w
  regs : Regs s w
  args : Args s w
  x20 : w.getReg .x20 = vecPtr w (s.getReg .x2 - 152)
  x21 : w.getReg .x21 = vecLen w (s.getReg .x2 - 152)
  vec : NewVecE s w (s.getReg .x2 - 152) ch
  claim : eAt w (s.getReg .x2 - 128) = cl
  run : ∀ T, TranscriptAt s (tsSelf s) T → ∃ T',
    (TM.sumcheck (eAt s (tsTarget s)) 4 (List.replicate (nRounds s) none)).run T =
      some ((ch, cl), T') ∧ TranscriptAt w (tsSelf s) T'

theorem sumcheckStack_eq : sumcheckStack = 1632 := rfl

/-- `sumcheck`'s arguments, the claim at `tsTarget`, the equalities a buffer allocated. -/
theorem sumcheckPre {s v : MachineState} (hpre : TableSumcheckPre s) (h : Inv s v)
    (h10 : v.getReg .x10 = s.getReg .x2 - 152) (h11 : v.getReg .x11 = tsSelf s)
    (h12 : v.getReg .x12 = tsTarget s) (h13 : v.getReg .x13 = 4)
    (hbuf : NewBuf s v (v.getReg .x14) (32 * (v.getReg .x15).toNat) 8)
    (hbelow : (v.getReg .x14).toNat ≤ heapNext v) : SumcheckPre v := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  obtain ⟨e0, e1, e2⟩ := h.stream hpre
  have hst : RtStack v sumcheckStack :=
    hpre.stack.sub 496 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsl : stackLo v sumcheckStack = s.getReg .x2 - 2128 := by
    show v.getReg .x2 - BitVec.ofNat 64 1632 = _
    rw [h.sp]; addr_omega [hb1]
  have hm := h.mono
  have hn := h.heap.hi
  have ha := hpre.stack.above
  have hx := hpre.stack.next
  have hr := hpre.stack.rodata
  have hS := hpre.self.self
  have ss := hpre.selfStack
  have sf := hpre.selfFree
  have ps := hpre.proofStack
  have pf := hpre.proofFree
  have bf := hpre.streamFree
  have pt := hpre.proofTarget
  have tg := hpre.target
  have tf := hpre.targetFree
  have tst := hpre.targetStack
  have hrb : rodataBase.toNat = 2684354560 := rfl
  simp only [stack_eq] at ha hx hr ss ps tst
  simp only [ProofApart] at ps pt
  have hl := hpre.heap.lo
  simp only [Outside, NewBuf, heapNext, heapEnd, heapStart] at sf pf bf tf hbuf hm hn ha hbelow hl
  have hb : (v.getReg .x15).toNat = 0 ∨ ((s.getMem nextAddr).toNat ≤ (v.getReg .x14).toNat ∧
      (v.getReg .x14).toNat + 32 * (v.getReg .x15).toNat ≤ (v.getMem nextAddr).toNat) := by
    rcases hbuf.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr h0
  have hs8 : (tsSelf s).toNat + 368 ≤ 2 ^ 64 := by addr_omega [hS]
  refine {
    heap := h.heap
    out := by rw [h10]; addr_omega [hb1, hb2, hb3]
    self := h11 ▸ h.tok hpre
    stack := hst
    outStack := by rw [h10, hsl]; addr_omega [hb1]
    selfStack := by rw [h11, hsl]; addr_omega [hb1, ss]
    outSelf := by rw [h10, h11]; addr_omega [hb1, ss, hs8]
    proofStack := by
      simp only [ProofApart, h11, hsl, e0, e1, e2]
      exact ⟨by addr_omega [hb1, ps.1], by addr_omega [hb1, ps.2]⟩
    proofOut := by
      simp only [ProofApart, h10, h11, e0, e1, e2]
      exact ⟨by addr_omega [hb1, ps.1], by addr_omega [hb1, ps.2]⟩
    outFree := by rw [h10]; simp only [Outside, heapEnd]; addr_omega [hb1, ha, hx]
    selfFree := by rw [h11]; simp only [Outside, heapNext, heapEnd]; addr_omega [sf, hm]
    proofFree := by rw [h11, e0]; simp only [Outside, heapNext, heapEnd]; addr_omega [pf, hm]
    streamFree := by rw [h11, e1, e2]; simp only [Outside, heapNext, heapEnd]; addr_omega [bf, hm]
    rodata := h.rodata hpre
    outRodata := by rw [h10]; addr_omega [hb1, hr, hrb]
    selfRodata := h11 ▸ hpre.selfRodata
    count := by rw [h13]; decide
    claim := h12 ▸ tg
    eqs := by
      rcases hb with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by addr_omega [h0, hn, hbuf.1, hl])
    claimFree := by rw [h12]; simp only [Outside, heapNext, heapEnd]; addr_omega [tf, hm]
    eqsFree := Or.inr (by simp only [Outside, heapNext, heapEnd]; addr_omega [hb, hn, hbelow])
    claimStack := by rw [h12, hsl]; addr_omega [hb1, tst]
    eqsStack := by rw [hsl]; addr_omega [hb, hn, ha, hb1]
    claimSelf := h11 ▸ h12 ▸ hpre.targetSelf
    eqsSelf := by rw [h11]; addr_omega [hb, hn, sf, hm]
    claimOut := by rw [h10, h12]; addr_omega [hb1, tst]
    eqsOut := by rw [h10]; addr_omega [hb, hn, ha, hb1]
    claimEqs := by rw [h12]; addr_omega [hb, hn, tf, hm]
    proofClaim := by rw [h11, h12]; simp only [ProofApart, e0, e1, e2]; exact pt
    claimRodata := h12 ▸ hpre.targetRodata }


theorem stageB (hS : SumcheckSpec) {s v : MachineState} (hpre : TableSumcheckPre s)
    (h : AtSumcheck s v) (hpc : v.pc = 0x800080cc) :
    ∃ w, Reaches Image.code v w ∧
      ((∃ ch cl, w.pc = 0x80008100 ∧ AfterSumcheck s w ch cl) ∨ Done s w) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hA := hpre.args.region
  have I := h.inv
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800080cc_spec hpc (by
    rv_eval [I.sp]
    and_intros <;> first
      | valid_access hval [hb1]
      | (rcases hA with h0 | h0
         · omega
         · exact Region.valid h0 (by addr_omega [h0]) (by addr_omega [h0]) (by addr_omega [h0])))
  have hm₁ := b800080cc_mem_same h₁
  have k₁ := b800080cc_keeps h₁
  have I₁ : Inv s v₁ := I.same hpre hm₁ (k₁ .x2 (by decide))
  have R₁ : Regs s v₁ := h.regs.of fun r hr ↦ k₁ r (mem_of_mem hr _)
  have h10₁ : v₁.getReg .x10 = s.getReg .x2 - 152 := by
    rw [b800080cc_x10 h₁, I.sp]; addr_omega [hb1]
  have h11₁ : v₁.getReg .x11 = tsSelf s := by
    rw [b800080cc_x11 h₁, I.sp, show s.getReg .x2 - 496 + 512 = s.getReg .x2 + 16 by
      addr_omega [hb1, hb2]]
    exact I.word hpre.args (by addr_omega [hb1, hb2]) (by addr_omega [hb1, hb2])
  have h12₁ : v₁.getReg .x12 = tsTarget s := by rw [b800080cc_x12 h₁, h.regs.x27]
  have h13₁ := b800080cc_x13 h₁
  have h14₁ : v₁.getReg .x14 = vecPtr v (s.getReg .x2 - 248) := by
    rw [b800080cc_x14 h₁, I.sp]; simp only [vecPtr]; congr 1; addr_omega [hb1]
  have h15₁ : v₁.getReg .x15 = vecLen v (s.getReg .x2 - 248) := by
    rw [b800080cc_x15 h₁, I.sp]; simp only [vecLen]; congr 1; addr_omega [hb1]
  have hn₁ : heapNext v₁ = heapNext v := by simp only [heapNext, hm₁]
  have hbuf : NewBuf s v₁ (v₁.getReg .x14) (32 * (v₁.getReg .x15).toNat) 8 := by
    rw [h14₁, h15₁, h.len]; simp only [NewBuf, hn₁]; exact h.buf
  have hargs : TM.sumcheck (eAt v₁ (v₁.getReg .x12)) (v₁.getReg .x13).toNat
      (optEListAt v₁ (v₁.getReg .x14) (v₁.getReg .x15).toNat) =
      TM.sumcheck (eAt s (tsTarget s)) 4 (List.replicate (nRounds s) none) := by
    rw [h12₁, h13₁, h14₁, h15₁, h.len, eAt_of_same hm₁, h.target, optEListAt_of_same hm₁, h.elems]
    rfl
  obtain ⟨w₁, hr₂, ⟨hpc₂, hp₂, post⟩ | hd⟩ := hS.call hr₁ (b800080cc_pc h₁)
    (sumcheckPre hpre I₁ h10₁ h11₁ h12₁ h13₁ hbuf (by rw [h14₁, hn₁]; exact h.below))
  swap
  · exact ⟨w₁, hr₂, Or.inr (Or.inr hd)⟩
  have hsl : stackLo v₁ sumcheckStack = s.getReg .x2 - 2128 := by
    show v₁.getReg .x2 - BitVec.ofNat 64 1632 = _
    rw [I₁.sp]; addr_omega [hb1]
  have hf := post.frame
  rw [h10₁, h11₁, h12₁, hsl] at hf
  have hm₂ := post.mono
  have hn := post.heap.hi
  have I₂ : Inv s w₁ := I₁.locT hpre (hf.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha | ha
      · exact Or.inl (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)
      · exact Or.inl (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inl (Or.inr (Or.inl ha))
      · exact Or.inl (Or.inr (Or.inr ha))) post.heap hm₂ (hp₂.reg .x2)
  have R₂ : Regs s w₁ := R₁.call hp₂
  have tst := hpre.targetStack
  have ss := hpre.selfStack
  have hS' := hpre.self.self
  have ha' := hpre.stack.above
  have hx' := hpre.stack.next
  simp only [stack_eq] at tst ss ha' hx'
  have A₂ : Args s w₁ := (h.args.step (DFrame.of_same hm₁ fun _ ↦ False) (fun _ h ↦ h.elim) hb1).step
    hf (fun a ha ↦ by
      simp only [Fresh, heapNext, heapEnd] at ha ha' hn
      rcases ha with ha | ha | ha | ha | ha | ha <;>
        exact ⟨by addr_omega [ha, hb1, tst, ss, hS', ha', hx', hn],
          by addr_omega [ha, hb1, tst, ss, hS', ha', hx', hn]⟩) hb1
  -- the transcripts the entry's stands for
  have hT₁ (T : TState) (hT : TranscriptAt s (tsSelf s) T) : TranscriptAt v₁ (v₁.getReg .x11) T :=
    h11₁ ▸ I.transcript hpre I₁.heap (DFrame.of_same hm₁ _) (h.tr T hT)
  have hsp₂ : w₁.getReg .x2 = s.getReg .x2 - 496 := (hp₂.reg .x2).trans I₁.sp
  obtain ⟨w₂, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800080ec_spec
    (by rw [hpc₂, returnAddress_eq, b800080cc_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      and_intros <;> valid_access hval [hb1])
  have hm₃ := b800080ec_mem_same h₃
  have k₃ := b800080ec_keeps h₃
  have hcap : w₁.getMem (w₁.getReg .x2 + 344) = vecCap w₁ (s.getReg .x2 - 152) := by
    rw [hp₂.reg .x2, I₁.sp]; simp only [vecCap]; congr 1; addr_omega [hb1]
  by_cases herr : vecCap w₁ (s.getReg .x2 - 152) = errNiche
  · -- `Err`: `0x800084e0` stores it in the result
    have hpc₃ := b800080ec_pc_taken h₃ (by rw [hcap]; exact herr)
    have I₃ : Inv s w₂ := I₂.same hpre hm₃ (k₃ .x2 (by decide))
    have hx18 : w₂.getReg .x18 = s.getReg .x10 := by
      rw [k₃ .x18 (by decide)]; exact R₂.x18
    have ho := hpre.out
    obtain ⟨w₃, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800084e0_spec hpc₃ (by
      rv_eval [hx18]
      and_intros <;>
        exact Region.valid ho (by addr_omega [ho]) (by addr_omega [ho]) (by addr_omega [ho]))
    have hf₄ := DFrame.of_memFrame (b800084e0_frame h₄ (by rw [hx18]; addr_omega [ho]))
    rw [hx18] at hf₄
    have os := hpre.outStack
    simp only [stack_eq] at os
    have hn₄ : heapNext w₃ = heapNext w₂ := by
      simp only [heapNext]
      exact congrArg BitVec.toNat (hf₄ nextAddr fun i hi hw ↦ by
        have := hpre.outFree.2; addr_omega [hw, hi, this])
    have I₄ : Inv s w₃ := I₃.step hpre hf₄ (fun a ha ↦ ⟨Or.inl ha, by addr_omega [ha, os, hb1]⟩)
      ⟨hn₄ ▸ I₃.heap.lo, hn₄ ▸ I₃.heap.hi⟩ hn₄.ge (by rw [b800084e0_keeps h₄ .x2 (by decide)])
    obtain ⟨t, hr₅, ht⟩ := errExit hpre I₄ (b800084e0_pc h₄)
      (by rw [vecCap, ← hx18, b800084e0_m_x18_0 h₄, b800080ec_x10 h₃]; rfl) fun T hT ↦ by
        have hv := post.value T (hT₁ T hT)
        rw [hargs] at hv
        rcases e : (TM.sumcheck (eAt s (tsTarget s)) 4
          (List.replicate (nRounds s) none)).run T with _ | ⟨⟨pt, cl⟩, T'⟩
        · simp only [nRounds] at e
          simp [mirror, tableSumcheckM, StateT.run_bind, e]
        · rw [e, h10₁] at hv
          exact absurd herr hv.1
    exact ⟨t, hr₂.trans (hr₃.trans (hr₄.trans hr₅)), Or.inr ht⟩
  · -- `Ok`: the values, fixed by any transcript
    have hpc₃ := b800080ec_pc_not_taken h₃ (by rw [hcap]; exact herr)
    have I₃ : Inv s w₂ := I₂.same hpre hm₃ (k₃ .x2 (by decide))
    obtain ⟨T₀, hT₀⟩ := exists_transcriptAt s (tsSelf s)
    have hv₀ := post.value T₀ (hT₁ T₀ hT₀)
    rw [hargs, h10₁] at hv₀
    rcases e₀ : (TM.sumcheck (eAt s (tsTarget s)) 4
      (List.replicate (nRounds s) none)).run T₀ with _ | ⟨⟨ch, cl⟩, T₀'⟩
    · rw [e₀] at hv₀
      exact absurd hv₀ herr
    rw [e₀] at hv₀
    obtain ⟨-, hvec, hcl, -⟩ := hv₀
    refine ⟨w₂, hr₂.trans hr₃, Or.inl ⟨ch, cl, hpc₃, I₃, R₂.of fun r hr ↦ k₃ r (mem_of_mem hr _),
      A₂.step (DFrame.of_same hm₃ fun _ ↦ False) (fun _ h ↦ h.elim) hb1, ?_, ?_,
      (hvec.of_same hm₃).weaken (h.inv.mono.trans hn₁.symm.le), ?_, fun T hT ↦ ?_⟩⟩
    · rw [b800080ec_x20 h₃, hsp₂]; simp only [vecPtr, hm₃]; congr 1; addr_omega [hb1]
    · rw [b800080ec_x21 h₃, hsp₂]; simp only [vecLen, hm₃]; congr 1; addr_omega [hb1]
    · rw [eAt_of_same hm₃, ← hcl]; congr 1; addr_omega [hb1]
    · have hv := post.value T (hT₁ T hT)
      rw [hargs, h10₁] at hv
      rcases e : (TM.sumcheck (eAt s (tsTarget s)) 4
        (List.replicate (nRounds s) none)).run T with _ | ⟨⟨ch', cl'⟩, T'⟩
      · rw [e] at hv
        exact absurd hv herr
      rw [e] at hv
      obtain ⟨-, hvec', hcl', hT'⟩ := hv
      have ech : ch' = ch := hvec'.elems.symm.trans hvec.elems
      subst ech
      subst hcl'
      refine ⟨T', by rw [hcl], I₂.transcript hpre I₃.heap (DFrame.of_same hm₃ _) (h11₁ ▸ hT')⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
