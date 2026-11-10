import Rv64Verifier.Proofs.Walk.Dr4

/-!
# `walk`: `tables()`, DEREF's stored values in place (R8)

From `AtDeref`: the three stored values summed (`deref0a`, `deref0b`, `deref1`, `deref2`), then the
block at `0x800026d4` laying them out at `sp + 2240 .. 2312` and an empty `Flushes` at `sp + 2312`,
to `state_step`'s call (`derefSums`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

/-- DEREF's three stored values at `sp + 2240 .. 2312`. -/
abbrev storeFs (s : MachineState) : List (Word × LayoutMirror.FormRust) :=
  [(s.getReg .x2 - 368, store2), (s.getReg .x2 - 392, store1), (s.getReg .x2 - 416, store0)]

set_option maxRecDepth 8192 in
/-- From `AtDeref` to `state_step` on the empty `Flushes` at `sp + 2312`, the stored values laid out. -/
theorem derefSums (hC : Rv64Verifier.Layout.ColSpec) (hP : Rv64Verifier.Layout.ProdSpec)
    (hA : Rv64Verifier.Layout.AddScaledSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} (hpre : WalkPre s)
    (h : AtDeref OI s u A k R Q B Bb) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004a90 ∧
      DS OI s t A k R Q B Bb (heapNext u) (L4 s setT) (s.getReg .x2 - 344) {} (heapNext t) (heapNext u)
        (storeFs s) ∧
      DRg s t 0xa00000b0 ∧ t.getReg .x10 = s.getReg .x2 - 344 ∧ t.getReg .x1 = 0x8000272c) ∨
      Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t₁, q₁, ⟨pc₁, D₁, r₁⟩ | d⟩ := deref0a hC hP hpre h
  swap
  · exact ⟨t₁, q₁, Or.inr d⟩
  obtain ⟨t₂, q₂, ⟨pc₂, S₂, K₂, r₂⟩ | d⟩ := deref0b hA hpre D₁ r₁ pc₁
  swap
  · exact ⟨t₂, q₁.trans q₂, Or.inr d⟩
  obtain ⟨t₃, q₃, ⟨pc₃, H₁, hH₁, S₃, K₃, r₃, G₃⟩ | d⟩ := deref1 hC hP hA hpre S₂ r₂ pc₂
  swap
  · exact ⟨t₃, q₁.trans (q₂.trans q₃), Or.inr d⟩
  obtain ⟨t₄, q₄, ⟨pc₄, H₂, hH₂, S₄, K₄, r₄, G₄, F₄⟩ | d⟩ := deref2 hC hP hA hpre S₃ r₃ G₃ pc₃
  swap
  · exact ⟨t₄, q₁.trans (q₂.trans (q₃.trans q₄)), Or.inr d⟩
  have Q₄ := q₁.trans (q₂.trans (q₃.trans q₄))
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 2656 := S₄.m.m.inv.sp
  have y23 := r₄.x23
  -- the stored values and the empty `Flushes` laid out
  obtain ⟨v, p, g⟩ := Sym.BlockSpec.reaches b800026d4_spec pc₄ (by
    rv_eval [sp₄, y23]
    and_intros <;> valid_access hval [hb1])
  have fr := mfr23 hpre y23 (N := 96) (M := 416) (n := 120) (by decide)
    (b800026d4_frame g (by rw [y23]; addr_omega [hb1]))
  have hS : InSlot s (s.getReg .x2 - 416) 120 := inSlot_off hpre (by decide)
  obtain ⟨M, hn⟩ := S₄.m.slotStep hpre hS (l4_off hpre (by decide)) fr (b800026d4_keeps g .x2 (by decide))
  have hu₄ := S₄.m.m.inv.heap.hi
  simp only [heapEnd] at hu₄
  have Kb : Keep t₄ v (heapNext t₄) := Keep.slot hpre hu₄ fr ⟨hS.1, hS.2.1⟩
  -- the heap's growth
  have e₁ : heapNext u ≤ heapNext t₁ := D₁.hlo₂
  have e₂ : heapNext t₁ ≤ heapNext t₂ := S₂.hH
  have e₃ : heapNext t₂ ≤ heapNext t₃ := le_trans hH₁ S₃.hH
  have e₄ : heapNext t₃ ≤ heapNext t₄ := le_trans hH₂ S₄.hH
  have hs : heapStart ≤ heapNext u := h.m.m.inv.heap.lo
  have o₀ : heapStart ≤ heapNext t₁ := le_trans hs e₁
  -- the first value, from `s0`, `s1`, `s3`
  have A₀ : SF v (s.getReg .x2 - 416) store0 (heapNext t₁) (heapNext t₂) :=
    S₂.sa.keep (K₃.trans ((K₄.mono e₃).trans (Kb.mono (le_trans e₃ e₄)))) o₀
      (by have h' := b800026d4_m_x23_96 g; rv_eval [y23] at h'; rw [h', F₄.h₁])
      (by have h' := b800026d4_m_x23_104 g; rv_eval [y23] at h' ⊢; rw [h', F₄.h₂]; rv_eval [])
      (by have h' := b800026d4_m_x23_112 g; rv_eval [y23] at h' ⊢; rw [h', F₄.h₃]; rv_eval [])
      S₂.m.m.inv.heap (by rw [hn]; exact le_trans e₃ e₄)
  -- the second, from `s4`, `s5`, `s6`
  have A₁ : SF v (s.getReg .x2 - 392) store1 H₁ (heapNext t₃) :=
    S₃.sa.keep (K₄.trans (Kb.mono e₄)) (le_trans o₀ (le_trans e₂ hH₁))
      (by have h' := b800026d4_m_x23_120 g; rv_eval [y23] at h' ⊢; rw [h', G₄.h₁])
      (by have h' := b800026d4_m_x23_128 g; rv_eval [y23] at h' ⊢; rw [h', G₄.h₂]; rv_eval [])
      (by have h' := b800026d4_m_x23_136 g; rv_eval [y23] at h' ⊢; rw [h', G₄.h₃]; rv_eval [])
      S₃.m.m.inv.heap (by rw [hn]; exact e₄)
  -- the third, moved from `sp + 2240`
  have A₂ : SF v (s.getReg .x2 - 368) store2 H₂ (heapNext t₄) :=
    S₄.sa.move fr (by mem_tac [y23] (b800026d4_m_x23_144 g)) (by mem_tac [y23] (b800026d4_m_x23_152 g))
      (by mem_tac [y23] (b800026d4_m_x23_160 g))
      (fun x _ hx hw ↦ by
        simp only [heapNext] at hx hu₄; simp only [Within] at hw
        addr_omega [hw, hx, hb1, hu₄]) S₄.m.m.inv.heap hn.ge
  -- the empty `Flushes`
  obtain ⟨fok, fval, fnd⟩ := flushesOk_empty (u := v) (a := s.getReg .x2 - 344)
    (by mem_tac [y23] (b800026d4_m_x23_168 g))
    (by have h' := b800026d4_m_x23_176 g; rv_eval [y23] at h' ⊢; rw [h', r₄.x25])
    (by mem_tac [y23] (b800026d4_m_x23_184 g)) (by mem_tac [y23] (b800026d4_m_x23_192 g))
    (by have h' := b800026d4_m_x23_200 g; rv_eval [y23] at h' ⊢; rw [h', r₄.x25])
    (by mem_tac [y23] (b800026d4_m_x23_208 g))
  have SL : SFs s v (heapNext u) (storeFs s) :=
    (((SFs.nil s v (heapNext u)).cons A₀ (le_trans e₁ (le_refl _)) (by rw [hn]; exact le_trans e₃ e₄)
      (Or.inl (inSlot_off hpre (by decide)))).cons A₁ (le_trans e₁ (le_trans e₂ hH₁))
      (by rw [hn]; exact e₄) (Or.inl (inSlot_off hpre (by decide)))).cons A₂
      (le_trans e₁ (le_trans e₂ (le_trans e₃ hH₂))) (by rw [hn]) (Or.inl (inSlot_off hpre (by decide)))
  refine ⟨v, Q₄.trans p, Or.inl ⟨b800026d4_pc g, ⟨M, ⟨fok, fval, fun x hx ↦ absurd hx (fnd x)⟩,
    inSlot_off hpre (by decide), SL, by rw [hn]; exact le_trans e₁ (le_trans e₂ (le_trans e₃ e₄))⟩,
    r₄.keeps (b800026d4_keeps g), by rw [b800026d4_x10 g]; exact spAdd hpre sp₄ (by decide),
    b800026d4_x1 g⟩⟩

end Rv64Verifier.Proofs.Walk
