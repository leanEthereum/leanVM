import Rv64Verifier.Proofs.Pcs.VsoMerkleSrc

/-!
# `verify_stacked_opening`'s level loop: `lam` and its powers

`0x8000a9d8` keeps the queries' buffer (`ra`) at `S - 824` and calls `duplex`; `0x8000a9e8` copies
the challenge `lam`'s lanes to `S - 384` and calls `powers(S - 488, S - 384, s10)`, which returns to
the Merkle checks' start `0x8000aa14` (`lamPowers`). The mirror draws `lam` with `TM.sample`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  Rv64Verifier.MultilinearContracts LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What `lamPowers` writes from `u`, the heap allocated up to `w`'s `NEXT`. -/
def LW (s u w : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10 + 8) 336 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a (s.getReg .x2 - 824) 8 ∨ Within a (s.getReg .x2 - 488) 24 ∨
    Within a (s.getReg .x2 - 384) 24 ∨ Within a nextAddr 8 ∨ Fresh u w a

/-- At `0x8000aa14`, after `lam` and its powers, from `u` on the transcript `T`. -/
structure LamOut (s u w : MachineState) (T : Model.TState) : Prop where
  pc : w.pc = 0x8000aa14
  sp : w.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s w (w.getMem nextAddr)
  fr : DFrame u w (LW s u w)
  mono : heapNext u ≤ heapNext w
  regs : ∀ r ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x26, .x27], w.getReg r = u.getReg r
  qp : w.getMem (s.getReg .x2 - 824) = u.getReg .x1
  tr : TranscriptAt w (s.getReg .x10) { T with sponge := spDuplex T.sponge }
  lam : eAt w (s.getReg .x2 - 384) = (spSqueeze T.sponge).1
  vec : VecOk w (s.getReg .x2 - 488) 24 8
  len : vecLen w (s.getReg .x2 - 488) = u.getReg .x26
  elems : vecEs w (s.getReg .x2 - 488) = Verifier.powers (spSqueeze T.sponge).1 (u.getReg .x26).toNat
  fresh : NewBuf u w (vecPtr w (s.getReg .x2 - 488)) (24 * (u.getReg .x26).toNat) 8

/-- **`lam` drawn and its powers**, from `0x8000a9d8` to `0x8000aa14`. -/
theorem lamPowers (hD : DuplexSpec) (hP : PowersSpec) {s u : MachineState} {T : Model.TState}
    (hpre : VsoPre s) (hinv : InvR s u (u.getMem nextAddr)) (hpc : u.pc = 0x8000a9d8)
    (h248 : u.getMem (s.getReg .x2 - 792) = s.getReg .x10 + 8) (hx20 : u.getReg .x20 = s.getReg .x10)
    (hT : TranscriptAt u (s.getReg .x10) T) :
    ∃ w, Reaches Image.code u w ∧ (Dead Image.code w ∨ LamOut s u w T) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hro := hst.rodata
  rw [stackLo_vso, vso_stack] at hro
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hsp : u.getReg .x2 = s.getReg .x2 - 1040 := hinv.sp
  have hu := hinv.heap hpre.heap
  -- `ra` kept, `duplex`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a9d8_spec hpc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000a9d8_keeps h₁
  have f₁ := DFrame.of_memFrame (b8000a9d8_frame h₁ (by rw [hsp]; addr_omega [hb]))
  rw [hsp, show s.getReg .x2 - 1040 + 216 = s.getReg .x2 - 824 by rv_eval []] at f₁
  have e₁ := b8000a9d8_m_x2_216 h₁
  rw [hsp, show s.getReg .x2 - 1040 + 216 = s.getReg .x2 - 824 by rv_eval []] at e₁
  have nx₁ : t₁.getMem nextAddr = u.getMem nextAddr := f₁ _ fun i hi hw ↦ by addr_omega [hw, hi, hb, hnx]
  have inv₁ : InvR s t₁ (t₁.getMem nextAddr) := by
    rw [nx₁]
    exact Inv.step' hpre hinv f₁ (fun a ha ↦ frame_wr hpre (by addr_omega [ha, hb]))
      (fun a ha ↦ by addr_omega [ha, hb]) nx₁ (le_refl _) hinv.fits (k₁ .x2 (by decide))
  have hT₁ : TranscriptAt t₁ (s.getReg .x10) T :=
    tr_keep hpre hinv hT f₁ fun a ha ↦ Or.inl (by addr_omega [ha, hb])
  obtain ⟨t₂, hr₂, hv₂⟩ := callDuplex hD hpre inv₁ (b8000a9d8_pc h₁) (by
    rw [b8000a9d8_x10 h₁, hsp, show s.getReg .x2 - 1040 + 248 = s.getReg .x2 - 792 by rv_eval []]
    exact h248)
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, X₂, hsp₂⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd⟩
  have nx₂ : t₂.getMem nextAddr = t₁.getMem nextAddr := X₂ _ fun i hi hw ↦ by
    have hf := hI.free.2
    rcases hw with hw | hw
    · addr_omega [hw, hi, hS, hf]
    · addr_omega [hw, hi, hb, hnx]
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1040 := by
    rw [hpres₂ .x2 (by decide), k₁ .x2 (by decide), hsp]
  have inv₂ : InvR s t₂ (t₂.getMem nextAddr) := by
    rw [nx₂]
    refine Inv.step' hpre inv₁ X₂ (fun a ha ↦ ?_) (fun a ha ↦ ?_) nx₂ (le_refl _) inv₁.fits
      (hpres₂ .x2 (by decide))
    · rcases ha with ha | ha
      · exact Or.inl (Or.inl (by simp only [W]; addr_omega [ha, hS]))
      · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · rcases ha with ha | ha
      · addr_omega [ha, hS, hIs, hb]
      · addr_omega [ha, hb]
  have hT₂ := tr_duplex hpre inv₁ hT₁ X₂ hsp₂
  have x20₂ : t₂.getReg .x20 = s.getReg .x10 := by
    rw [hpres₂ .x20 (by decide), k₁ .x20 (by decide), hx20]
  -- `lam`'s lanes, `powers`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000a9e8_spec
    (by rw [hpc₂, returnAddress_eq, b8000a9d8_x1 h₁]; decide) (by
      rv_eval [sp₂, x20₂]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid hI.ok.self (by addr_omega [hS]) (by addr_omega [hS]) (by addr_omega [hS]))
  have k₃ := b8000a9e8_keeps h₃
  have f₃ := DFrame.of_memFrame (b8000a9e8_frame h₃ (by rw [sp₂]; addr_omega [hb]))
  rw [sp₂, show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval []] at f₃
  have nx₃ : t₃.getMem nextAddr = t₂.getMem nextAddr := f₃ _ fun i hi hw ↦ by addr_omega [hw, hi, hb, hnx]
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₃ .x2 (by decide), sp₂]
  have inv₃ : InvR s t₃ (t₃.getMem nextAddr) := by
    rw [nx₃]
    exact Inv.step' hpre inv₂ f₃ (fun a ha ↦ frame_wr hpre (by addr_omega [ha, hb]))
      (fun a ha ↦ by addr_omega [ha, hb]) nx₃ (le_refl _) inv₂.fits (k₃ .x2 (by decide))
  have hT₃ := tr_keep hpre inv₂ hT₂ f₃ fun a ha ↦ Or.inl (by addr_omega [ha, hb])
  have hlam : eAt t₃ (s.getReg .x2 - 384) = (spSqueeze T.sponge).1 := by
    have hsq : (spSqueeze T.sponge).1 = Compile.challengeOf (spDuplex T.sponge).state := rfl
    rw [hsq, ← hT₁.sponge, ← hsp₂]
    show _ = Compile.challengeOf (stateAt t₂ (s.getReg .x10 + 8 + 128))
    rw [Samples.challengeOf_stateAt]
    have m0 := b8000a9e8_m_x2_656 h₃
    have m1 := b8000a9e8_m_x2_664 h₃
    have m2 := b8000a9e8_m_x2_672 h₃
    rw [sp₂, x20₂] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    unfold eAt
    rv_eval [m0, m1, m2]
  have hx10₃ : t₃.getReg .x10 = s.getReg .x2 - 488 := by rw [b8000a9e8_x10 h₃, sp₂]; rv_eval []
  have hx11₃ : t₃.getReg .x11 = s.getReg .x2 - 384 := by rw [b8000a9e8_x11 h₃, sp₂]; rv_eval []
  have hx26₃ : t₃.getReg .x26 = u.getReg .x26 := by
    rw [k₃ .x26 (by decide), hpres₂ .x26 (by decide), k₁ .x26 (by decide)]
  have hx12₃ : t₃.getReg .x12 = u.getReg .x26 := by rw [b8000a9e8_x12 h₃, ← hx26₃, k₃ .x26 (by decide)]
  have hslP : stackLo t₃ powersStack = s.getReg .x2 - 2208 := by
    simp only [stackLo, powersStack, mulStack, sp₃, Nat.reduceAdd]; rv_eval []
  have hpreP : PowersPre t₃ := {
    heap := inv₃.heap hpre.heap
    out := by rw [hx10₃]; valid_sub hst.valid [hb]
    base := by rw [hx11₃]; valid_sub hst.valid [hb]
    stack := hst.sub 1040 sp₃ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [hx10₃]; exact stack_outside hpre (by addr_omega [hb]) (by addr_omega [hb])
    outStack := by rw [hx10₃, hslP]; addr_omega [hb]
    outRodata := by rw [hx10₃]; addr_omega [hro, hb]
    baseFree := by rw [hx11₃]; exact stack_outside hpre (by addr_omega [hb]) (by addr_omega [hb])
    baseStack := by rw [hx11₃, hslP]; addr_omega [hb]
    baseOut := by rw [hx11₃, hx10₃]; addr_omega [hb]
    rodata := inv₃.rodata' hpre }
  obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hdead⟩ := hP.call (Reaches.refl t₃) (b8000a9e8_pc h₃) hpreP
  swap
  · exact ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl hdead⟩
  have X₄ : DFrame t₃ t₄ fun a ↦ Within a (s.getReg .x2 - 488) 24 ∨
      Within a (s.getReg .x2 - 2208) 1168 ∨ Within a nextAddr 8 ∨ Fresh t₃ t₄ a := by
    have := hpost₄.frame; simp only [PowersW, hx10₃] at this; rw [hslP] at this
    exact this
  have hn₃ : heapNext t₃ = heapNext u := by simp only [heapNext, nx₃, nx₂, nx₁]
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 1040 := by rw [hpres₄.reg .x2, sp₃]
  have hfit := hpost₄.heap.hi
  have inv₄ : InvR s t₄ (t₄.getMem nextAddr) := by
    refine Inv.step' hpre inv₃ X₄ (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl hpost₄.mono hfit
      (hpres₄.reg .x2)
    · rcases ha with ha | ha | ha | ha
      · exact frame_wr hpre (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
      · exact Or.inr (Or.inr (Or.inl ha))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr ⟨by have := inv₃.mono; simp only [heapNext] at *; omega,
          by simp only [heapNext] at ha; exact ha.2⟩))
    · rcases ha with ha | ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx]
      · simp only [Fresh, heapNext] at ha; addr_omega [ha.2, hb, hfit]
  have hT₄ := tr_keep hpre inv₃ hT₃ X₄ fun a ha ↦ by
    rcases ha with ha | ha | ha | ha
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inr (Or.inl ha)
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inl ⟨by have := inv₃.mono; simp only [heapNext] at *; omega,
        by simp only [heapNext] at hfit ha; omega⟩))
  have hlam₄ : eAt t₄ (s.getReg .x2 - 384) = (spSqueeze T.sponge).1 := by
    rw [← hlam]
    exact X₄.eAt fun i hi hw ↦ by
      rcases hw with hw | hw | hw | hw
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb, hnx]
      · simp only [Fresh, heapNext] at hw; addr_omega [hw.2, hi, hb, hfit]
  have X : DFrame u t₄ (LW s u t₄) :=
    (((f₁.mono fun a ha ↦ (Or.inr (Or.inr (Or.inl ha)) : LW s u t₄ a)).trans X₂ fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inl ha
        · exact Or.inr (Or.inl (by addr_omega [ha, hb]))).trans f₃
      fun a ha ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))).trans X₄ fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
          simp only [Fresh] at ha ⊢
          rw [← hn₃]
          exact ha
  have e₄ : t₄.getMem (s.getReg .x2 - 824) = u.getReg .x1 := by
    rw [← e₁]
    refine ((X₄ _ fun i hi hw ↦ ?_).trans (f₃ _ fun i hi hw ↦ ?_)).trans (X₂ _ fun i hi hw ↦ ?_)
    · rcases hw with hw | hw | hw | hw
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb, hnx]
      · simp only [Fresh, heapNext] at hw; addr_omega [hw.2, hi, hb, hfit]
    · addr_omega [hw, hi, hb]
    · rcases hw with hw | hw
      · addr_omega [hw, hi, hb, hS, hIs]
      · addr_omega [hw, hi, hb]
  refine ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr {
    pc := by rw [hpc₄, returnAddress_eq, b8000a9e8_x1 h₃]; decide
    sp := sp₄
    inv := inv₄
    fr := X
    mono := by rw [← hn₃]; exact hpost₄.mono
    regs := fun r hr ↦ by
      rw [hpres₄ r (by simp only [calleeSaved]; exact mem_of_mem hr _), k₃ r (mem_of_mem hr _),
        hpres₂ r (by simp only [calleeSaved]; exact mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
    qp := e₄
    tr := hT₄
    lam := hlam₄
    vec := by have := hpost₄.vec; rw [hx10₃] at this; exact this
    len := by have := hpost₄.len; rw [hx10₃, hx12₃] at this; exact this
    elems := by have := hpost₄.elems; rw [hx10₃, hx11₃, hx12₃, hlam] at this; exact this
    fresh := ?_ }⟩
  have h' := hpost₄.fresh
  rw [hx10₃, hx12₃] at h'
  simp only [NewBuf, heapNext] at h' ⊢
  simp only [heapNext] at hn₃
  rw [hn₃] at h'
  exact h'

end Rv64Verifier.Proofs.Pcs.Vso
