import Rv64Verifier.Proofs.Walk.Dr9
import Rv64Verifier.Proofs.Walk.AtJump

/-!
# `walk`: `tables()`, DEREF's tail (R8)

From `0x800028c4`: `prod(fp, o3)`, `memory_cols(.., DEREF_CNT_LOCAL, v3)` (the columns in `.rodata`),
the `Flushes` moved to `sp + 1240`, `vec![ZERO; 15]` into `sp + 2144`, the `Flushes` moved to
`sp + 2168` and JUMP's empty `Flushes` at `sp + 1728`: the DEREF `Table` joins the finished ones, at
JUMP's first call (`derefTail`, ending in `AtJump`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

theorem cols_v3 {u : MachineState} (h : RodataOk u) :
    Rv64Verifier.Layout.colsAt u 0xa0000f18 3 = [8, 9, 10] := by
  have h0 : u.getMem 0xa0000f18 = 8 := h.word
  have h1 : u.getMem 0xa0000f20 = 9 := h.word
  have h2 : u.getMem 0xa0000f28 = 10 := h.word
  show [(u.getMem (0xa0000f18 + BitVec.ofNat 64 (8 * 0))).toNat,
    (u.getMem (0xa0000f18 + BitVec.ofNat 64 (8 * 1))).toNat,
    (u.getMem (0xa0000f18 + BitVec.ofNat 64 (8 * 2))).toNat] = _
  rw [show (0xa0000f18 : Word) + BitVec.ofNat 64 (8 * 0) = 0xa0000f18 by decide,
    show (0xa0000f18 : Word) + BitVec.ofNat 64 (8 * 1) = 0xa0000f20 by decide,
    show (0xa0000f18 : Word) + BitVec.ofNat 64 (8 * 2) = 0xa0000f28 by decide, h0, h1, h2]
  rfl

theorem derefFlushes_eq :
    (((((({} : LayoutMirror.FlushesRust).stateStep 0 1).bytecode 0 14 3 derefOps).memoryCols
      (LayoutMirror.prodRust 1 2 0) 11 [7]).memory (LayoutMirror.prodRust 7 3 0) 12
        [store0, store1, store2]).memoryCols (LayoutMirror.prodRust 1 4 0) 13 [8, 9, 10]) =
      LayoutMirror.flushesDerefRust := rfl

set_option maxRecDepth 8192 in
/-- From the target flush's return to JUMP's first call, the DEREF `Table` finished. -/
theorem derefTail (hP : Rv64Verifier.Layout.ProdSpec) (hK : Rv64Verifier.Layout.MemoryColsSpec)
    (hFE : MultilinearContracts.FromElemSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W H : Nat}
    {P : Word} (hpre : WalkPre s) (hWH : W ≤ H)
    (h : M8 OI s u A k R Q B Bb W (L4 s setT))
    (fb : FB u (s.getReg .x2 - 344) (((({} : LayoutMirror.FlushesRust).stateStep 0 1).bytecode 0 14 3
      derefOps).memoryCols (LayoutMirror.prodRust 1 2 0) 11 [7] |>.memory (LayoutMirror.prodRust 7 3 0)
        12 [store0, store1, store2]) H)
    (hH : H ≤ heapNext u) (r : DRg s u P) (x19 : u.getReg .x19 = 1) (x21 : u.getReg .x21 = 6)
    (x22 : u.getReg .x22 = 2) (hpc : u.pc = 0x800028c4) :
    ∃ t, Reaches Image.code u t ∧ (AtJump OI s t A k R Q B Bb ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I := h.m.inv
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  have hFo : InSlot s (s.getReg .x2 - 344) 48 := inSlot_off hpre (by decide)
  -- `prod(fp, o3)` into `sp + 1240`
  obtain ⟨u₁, p₁, g₁⟩ := Sym.BlockSpec.reaches b800028c4_spec hpc trivial
  have m₁ := b800028c4_mem_same g₁
  have D₀ : DS OI s u₁ A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 344) _ H (heapNext u₁) [] :=
    ⟨h.same hpre m₁ (b800028c4_keeps g₁ .x2 (by decide)), fb.same hpre hFo I.heap m₁, hFo,
      SFs.nil _ _ _, le_refl _⟩
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  obtain ⟨t₁, q₁, ⟨pc₁, hp₁, D₁, -, mo₁, -⟩ | d⟩ := prodD hP (o := s.getReg .x2 - 1416) hpre D₀
    (inSlot_off hpre (by decide)) (l4_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) (fun e he ↦ absurd he List.not_mem_nil)
    (b800028c4_pc g₁) (by rw [b800028c4_x10 g₁]; exact spAdd hpre sp (by decide))
  swap
  · exact ⟨t₁, p₁.trans q₁, Or.inr d⟩
  rw [b800028c4_x11 g₁, b800028c4_x12 g₁, b800028c4_x13 g₁] at D₁
  have Q₁ := p₁.trans q₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := D₁.m.m.inv.sp
  have R₁ := (r.keeps (b800028c4_keeps g₁)).pres hp₁
  have hH₁ : H ≤ heapNext t₁ := by rw [hn₁] at mo₁; omega
  -- `memory_cols(fp * o3, 13, v3)`
  obtain ⟨u₂, p₂, g₂⟩ := Sym.BlockSpec.reaches b800028dc_spec
    (by rw [pc₁, returnAddress_eq, b800028c4_x1 g₁]; decide) trivial
  have m₂ := b800028dc_mem_same g₂
  obtain ⟨D₂, hn₂⟩ := D₁.same hpre m₂ (b800028dc_keeps g₂ .x2 (by decide))
  have hnK : Rv64Verifier.Layout.memoryColsStack ≤ 8736 := by decide
  have hFo6 : InSlot s (s.getReg .x2 - 344) (8 * 6) := hFo
  obtain ⟨v1, v2, v3⟩ := slotW hpre D₂.m.m.inv hFo6 hnK
  have sa₂ := D₂.sl.sf _ (List.mem_singleton_self _)
  obtain ⟨w1, w2, w3⟩ := slotPre hpre D₂.m.m.inv (o := s.getReg .x2 - 1416) (inSlot_off hpre (by decide)) hnK
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - 344 := by rw [b800028dc_x10 g₂]; exact spAdd hpre sp₁ (by decide)
  have x11₂ : u₂.getReg .x11 = s.getReg .x2 - 1416 := by
    rw [b800028dc_x11 g₂]; exact spAdd hpre sp₁ (by decide)
  have pre : Rv64Verifier.Layout.MemoryColsPre u₂ := {
    heap := D₂.m.m.inv.heap
    stack := stk_sub hpre D₂.m.m.inv hnK (by decide)
    self := by rw [x10₂]; exact v1
    ok := by rw [x10₂]; exact D₂.fb.ok
    selfFree := by rw [x10₂]; exact v2
    selfStack := by rw [x10₂]; exact v3
    rodata := D₂.m.m.inv.rodata hpre
    address := by rw [x11₂]; exact w1
    addressOk := by rw [x11₂]; exact sa₂.ok
    addressFree := by rw [x11₂]; exact w2
    addressStack := by rw [x11₂]; exact w3
    len := by rw [b800028dc_x14 g₂]; decide
    columns := by
      rw [b800028dc_x13 g₂, b800028dc_x14 g₂]
      exact Rv64Verifier.Layout.validMemRange_of (by decide) (Or.inr ⟨by decide, by decide⟩)
    columnsFree := by
      rw [b800028dc_x13 g₂, b800028dc_x14 g₂]; exact ⟨Or.inr (by simp only [heapEnd]; decide), by addr_omega []⟩
    columnsStack := by
      rw [b800028dc_x13 g₂, b800028dc_x14 g₂, stackLo_callee D₂.m.m.inv]; addr_omega [hb1, hnK] }
  obtain ⟨t₃, q₃, ⟨pc₃, hp₃, ⟨g₃, gv₃⟩⟩ | d⟩ := hK u₂ (b800028dc_pc g₂) pre
  swap
  · exact ⟨t₃, Q₁.trans (p₂.trans q₃), Or.inr d⟩
  rw [x10₂] at g₃ gv₃
  rw [x11₂, b800028dc_x12 g₂, b800028dc_x13 g₂, b800028dc_x14 g₂, D₂.fb.val, sa₂.val,
    show (3 : Word).toNat = 3 from rfl, cols_v3 (D₂.m.m.inv.rodata hpre)] at gv₃
  have hHu₂ : H ≤ heapNext u₂ := by rw [hn₂]; exact hH₁
  obtain ⟨M₃, F₃⟩ := D₂.m.grow hpre D₂.fb hWH hHu₂ hFo (l4_off hpre (by decide)) g₃ hnK (hp₃.reg .x2)
  rw [gv₃] at F₃
  have Q₃ := Q₁.trans (p₂.trans q₃)
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := M₃.m.inv.sp
  have R₃ := (R₁.keeps (b800028dc_keeps g₂)).pres hp₃
  have y23 := R₃.x23
  -- the `Flushes` to `sp + 1240`, `vec![ZERO; 15]` into `sp + 2144`
  obtain ⟨u₄, p₄, g₄⟩ := Sym.BlockSpec.reaches b80002900_spec
    (by rw [pc₃, returnAddress_eq, b800028dc_x1 g₂]; decide) (by
      rv_eval [sp₃, y23]
      and_intros <;> valid_access hval [hb1])
  have fr₄ := mfr hpre sp₃ (N := 1240) (M := 1416) (by decide) (b80002900_frame g₄ (by rw [sp₃]; addr_omega [hb1]))
  obtain ⟨M₄, hn₄⟩ := M₃.slotStep hpre (inSlot_off hpre (by decide)) (l4_off hpre (by decide)) fr₄
    (b80002900_keeps g₄ .x2 (by decide))
  have hu₃ := M₃.m.inv.heap.hi
  simp only [heapEnd] at hu₃
  have F₄ := F₃.move (o := s.getReg .x2 - 1416) fr₄
    (by mem_tac [sp₃, y23] (b80002900_m_x2_1240 g₄)) (by mem_tac [sp₃, y23] (b80002900_m_x2_1248 g₄))
    (by mem_tac [sp₃, y23] (b80002900_m_x2_1256 g₄)) (by mem_tac [sp₃, y23] (b80002900_m_x2_1264 g₄))
    (by mem_tac [sp₃, y23] (b80002900_m_x2_1272 g₄)) (by mem_tac [sp₃, y23] (b80002900_m_x2_1280 g₄))
    (fun x _ h2 hw ↦ by simp only [Within] at hw; simp only [heapNext] at h2 hu₃; addr_omega [hw, h2, hb1, hu₃])
    (by addr_omega [hb1]) M₃.m.inv.heap hn₄.ge
  have sp₄ : u₄.getReg .x2 = s.getReg .x2 - 2656 := M₄.m.inv.sp
  obtain ⟨t₅, q₅, ⟨pc₅, hp₅, mo₅, M₅, F₅, P', Z₅⟩ | d⟩ := padCall hFE (o := s.getReg .x2 - 512) hpre M₄ F₄
    (inSlot_off hpre (by decide)) (inSlot_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) (l4_off hpre (by decide)) (b80002900_pc g₄)
    (by rw [b80002900_x10 g₄]; exact spAdd hpre sp₃ (by decide)) (b80002900_x11 g₄)
    (by rw [b80002900_x12 g₄]; decide)
  swap
  · exact ⟨t₅, Q₃.trans (p₄.trans q₅), Or.inr d⟩
  rw [b80002900_x12 g₄] at Z₅
  have Q₅ := Q₃.trans (p₄.trans q₅)
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 2656 := M₅.m.inv.sp
  have R₅ := (R₃.keeps (b80002900_keeps g₄)).pres hp₅
  have y23₅ := R₅.x23
  -- the `Flushes` to `sp + 2168`, JUMP's empty `Flushes` at `sp + 1728`
  obtain ⟨v, p₆, g₆⟩ := Sym.BlockSpec.reaches b8000294c_spec
    (by rw [pc₅, returnAddress_eq, b80002900_x1 g₄]; decide) (by
      rv_eval [sp₅, y23₅]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | addr_omega [hb1])
  have fr₆ : Rv64Verifier.Layout.DFrame t₅ v fun x ↦ Within x (s.getReg .x2 - 928) 48 ∨
      Within x (s.getReg .x2 - 488) 48 :=
    Expect.ldframe g₆ (by
      rv_eval [sp₅, y23₅]
      simp only [Within]
      and_intros
      all_goals first
        | exact Or.inl (by addr_omega [hb1])
        | exact Or.inr (by addr_omega [hb1]))
  have hu₅ := M₅.m.inv.heap.hi
  simp only [heapEnd] at hu₅
  have notHeap : ∀ x : Word, x.toNat < heapNext t₅ →
      ¬ (Within x (s.getReg .x2 - 928) 48 ∨ Within x (s.getReg .x2 - 488) 48) := fun x hx hw ↦ by
    simp only [heapNext] at hx hu₅
    simp only [Within] at hw; rcases hw with hw | hw <;> addr_omega [hw, hx, hb1, hu₅]
  have hn₆ : heapNext v = heapNext t₅ := by
    simp only [heapNext]; rw [fr₆ _ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1])
      (by decide)]
  have hv₆ : HeapOk v := ⟨hn₆ ▸ M₅.m.inv.heap.lo, hn₆ ▸ M₅.m.inv.heap.hi⟩
  have hA₆ := slotOk hpre M₅ (o := s.getReg .x2 - 928) (n := 48) (inSlot_off hpre (by decide))
    (l4_off hpre (by decide))
  have hB₆ := slotOk hpre M₅ (o := s.getReg .x2 - 488) (n := 48) (inSlot_off hpre (by decide))
    (l4_off hpre (by decide))
  have M₆ := M₅.step hpre fr₆ (fun a ha ↦ ?_) (fun a ha ↦ ?_) hv₆ hn₆.ge (b8000294c_keeps g₆ .x2 (by decide))
  rotate_left
  · rcases ha with ha | ha
    · exact ((hA₆ a ha).1).mono hn₆.ge
    · exact ((hB₆ a ha).1).mono hn₆.ge
  · rcases ha with ha | ha
    · exact (hA₆ a ha).2
    · exact (hB₆ a ha).2
  have F₆ := F₅.move (o := s.getReg .x2 - 512 + 24) fr₆
    (by mem_tac [sp₅, y23₅] (b8000294c_m_x23_24 g₆)) (by mem_tac [sp₅, y23₅] (b8000294c_m_x23_32 g₆))
    (by mem_tac [sp₅, y23₅] (b8000294c_m_x23_40 g₆)) (by mem_tac [sp₅, y23₅] (b8000294c_m_x23_48 g₆))
    (by mem_tac [sp₅, y23₅] (b8000294c_m_x23_56 g₆)) (by mem_tac [sp₅, y23₅] (b8000294c_m_x23_64 g₆))
    (fun x _ h2 hw ↦ notHeap x h2 hw) (by addr_omega [hb1]) M₅.m.inv.heap hn₆.ge
  have Z₆ := Z₅.frame fr₆ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1])
    (by addr_omega [hb1]) (fun x h1 h2 hw ↦ by
      have := Z₅.buf; exact notHeap x (by omega) hw) hn₆.ge
    (by have := Z₅.buf; simp only [heapNext] at this hu₅; omega)
  have T := tableOf (op := 3) Z₆ F₆ (by decide)
  have T1 : TableAt v (s.getReg .x2 - 512) derefT := T.1
  have hW₅ : W ≤ heapNext u₄ := by rw [hn₄]; have := g₃.mono; omega
  have M₇ := M₆.push (o := s.getReg .x2 - 512) (t := derefT) (inSlot_off hpre (by decide))
    T1 (fun x hx ↦ by have := T.2 x hx; omega)
  have x25 := R₅.x25
  refine ⟨v, Q₅.trans p₆, Or.inl ⟨b8000294c_pc g₆, M₇, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, b8000294c_x11 g₆,
    b8000294c_x12 g₆, b8000294c_x13 g₆, b8000294c_x1 g₆, ?_, ?_, ?_, ?_, ?_⟩⟩
  · mem_tac [sp₅] (b8000294c_m_x2_1728 g₆)
  · have h' := b8000294c_m_x2_1736 g₆; rv_eval [sp₅] at h' ⊢; rw [h', x25]
  · mem_tac [sp₅] (b8000294c_m_x2_1744 g₆)
  · mem_tac [sp₅] (b8000294c_m_x2_1752 g₆)
  · have h' := b8000294c_m_x2_1760 g₆; rv_eval [sp₅] at h' ⊢; rw [h', x25]
  · mem_tac [sp₅] (b8000294c_m_x2_1768 g₆)
  · rw [b8000294c_x10 g₆]; exact spAdd hpre sp₅ (by decide)
  · rw [b8000294c_keeps g₆ .x19 (by decide), hp₅.reg .x19, b80002900_keeps g₄ .x19 (by decide), hp₃.reg .x19,
      b800028dc_keeps g₂ .x19 (by decide), hp₁.reg .x19, b800028c4_keeps g₁ .x19 (by decide)]; exact x19
  · rw [b8000294c_keeps g₆ .x21 (by decide), hp₅.reg .x21, b80002900_keeps g₄ .x21 (by decide), hp₃.reg .x21,
      b800028dc_keeps g₂ .x21 (by decide), hp₁.reg .x21, b800028c4_keeps g₁ .x21 (by decide)]; exact x21
  · rw [b8000294c_keeps g₆ .x22 (by decide), hp₅.reg .x22, b80002900_keeps g₄ .x22 (by decide), hp₃.reg .x22,
      b800028dc_keeps g₂ .x22 (by decide), hp₁.reg .x22, b800028c4_keeps g₁ .x22 (by decide)]; exact x22
  · rw [b8000294c_keeps g₆ .x23 (by decide)]; exact y23₅
  · rw [b8000294c_keeps g₆ .x27 (by decide)]; exact R₅.x27

end Rv64Verifier.Proofs.Walk
