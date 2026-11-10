import Rv64Verifier.Proofs.Walk.Jp5

/-!
# `walk`: `tables()`, the JUMP `Table` (R8)

From `jumpCols`'s end: the `Flushes` moved to `sp + 2432`, `vec![ZERO; 14]` into `sp + 1728`, the
`Flushes` moved to `sp + 1752`, the tables' buffer loaded: the JUMP `Table` at `sp + 1728` joins
the finished ones, at the first `memcpy` (`jumpTail`). `jumpStage`: from `AtJump` to `AtR9`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

theorem jumpFlushes_eq :
    (((((({} : LayoutMirror.FlushesRust).stateDerived 0 1 npcF nfpF).bytecode 0 11 4 jumpOps).memoryCols
      (LayoutMirror.prodRust 1 2 0) 8 [5]).memoryCols (LayoutMirror.prodRust 1 3 0) 9 [6]).memoryCols
        (LayoutMirror.prodRust 1 4 0) 10 [7]) = LayoutMirror.flushesJumpRust := rfl

set_option maxRecDepth 8192 in
/-- The JUMP `Table` assembled at `sp + 1728`, to the first `memcpy`. -/
theorem jumpTail (hFE : MultilinearContracts.FromElemSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {F : LayoutMirror.FlushesRust} (hpre : WalkPre s) (M : M8 OI s u A k R Q B Bb W (L5 s))
    (fb : FB u (s.getReg .x2 - 928) F W) (r : JR s u) (x20 : u.getReg .x20 = s.getReg .x2 - 512)
    (x8 : u.getReg .x8 = 5) (x9 : u.getReg .x9 = 8) (x24 : u.getReg .x24 = 0xa0000068)
    (hpc : u.pc = 0x80002d30) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x800126e4 ∧
      M8 OI s t A k R Q B Bb (heapNext t) (L5 s ++ [(s.getReg .x2 - 928, ⟨4, List.replicate 14 0, F⟩)]) ∧
      t.getReg .x10 = Bb ∧ t.getReg .x11 = s.getReg .x2 - 1632 ∧ t.getReg .x12 = 72 ∧
      t.getReg .x1 = 0x80002dbc ∧ t.getReg .x8 = 5 ∧ t.getReg .x9 = 8 ∧ t.getReg .x18 = Bb ∧
      t.getReg .x20 = s.getReg .x2 - 512 ∧ JR s t) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp₀ : u.getReg .x2 = s.getReg .x2 - 2656 := M.m.inv.sp
  -- the `Flushes` to `sp + 2432`
  obtain ⟨u₁, p₁, g₁⟩ := Sym.BlockSpec.reaches b80002d30_spec hpc (by
      rv_eval [sp₀, x20]
      and_intros <;> valid_access hval [hb1])
  have k₁ := b80002d30_keeps g₁
  have fr₁ : Rv64Verifier.Layout.DFrame u u₁ fun x ↦ Within x (s.getReg .x2 - 224) 48 := by
    have := MemFrame.dframe (b80002d30_frame g₁ (by rw [x20]; addr_omega [hb1]))
    rwa [x20, show s.getReg .x2 - 512 + 288 = s.getReg .x2 - 224 by rv_eval []] at this
  obtain ⟨M₁, hn₁⟩ := M.slotStep hpre (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) fr₁
    (k₁ .x2 (by decide))
  have hu₀ := M.m.inv.heap.hi
  simp only [heapEnd] at hu₀
  have F₁ := fb.move (o := s.getReg .x2 - 224) fr₁
    (by mem_tac [sp₀, x20] (b80002d30_m_x20_288 g₁)) (by mem_tac [sp₀, x20] (b80002d30_m_x20_296 g₁))
    (by mem_tac [sp₀, x20] (b80002d30_m_x20_304 g₁)) (by mem_tac [sp₀, x20] (b80002d30_m_x20_312 g₁))
    (by mem_tac [sp₀, x20] (b80002d30_m_x20_320 g₁)) (by mem_tac [sp₀, x20] (b80002d30_m_x20_328 g₁))
    (fun x _ h2 hw ↦ by simp only [Within] at hw; simp only [heapNext] at h2 hu₀; addr_omega [hw, h2, hb1, hu₀])
    (by addr_omega [hb1]) M.m.inv.heap hn₁.ge
  -- `vec![ZERO; 14]` into `sp + 1728`
  obtain ⟨t₂, q₂, ⟨pc₂, hp₂, mo₂, M₂, F₂, P', Z₂⟩ | d⟩ := padCall hFE (o := s.getReg .x2 - 928) hpre M₁ F₁
    (inSlot_off hpre (by decide)) (inSlot_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) (l5_off hpre (by decide)) (b80002d30_pc g₁)
    (by rw [b80002d30_x10 g₁]; exact spAdd hpre sp₀ (by decide))
    (by rw [b80002d30_x11 g₁, x24]) (by rw [b80002d30_x12 g₁]; decide)
  swap
  · exact ⟨t₂, p₁.trans q₂, Or.inr d⟩
  rw [b80002d30_x12 g₁] at Z₂
  have Q₂ := p₁.trans q₂
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := M₂.m.inv.sp
  have y20 : t₂.getReg .x20 = s.getReg .x2 - 512 := by rw [hp₂.reg .x20, k₁ .x20 (by decide)]; exact x20
  -- the `Flushes` to `sp + 1752`, the tables' buffer
  obtain ⟨u₃, p₃, g₃⟩ := Sym.BlockSpec.reaches b80002d74_spec
    (by rw [pc₂, returnAddress_eq, b80002d30_x1 g₁]; decide) (by
      rv_eval [sp₂, y20]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | addr_omega [hb1])
  have k₃ := b80002d74_keeps g₃
  have fr₃ : Rv64Verifier.Layout.DFrame t₂ u₃ fun x ↦ Within x (s.getReg .x2 - 904) 48 := by
    have := MemFrame.dframe (b80002d74_frame g₃ (by rw [sp₂]; addr_omega [hb1]))
    rwa [spAdd hpre sp₂ (N := 1752) (M := 904) (by decide)] at this
  obtain ⟨M₃, hn₃⟩ := M₂.slotStep hpre (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) fr₃
    (k₃ .x2 (by decide))
  have hu₂ := M₂.m.inv.heap.hi
  simp only [heapEnd] at hu₂
  have F₃ := F₂.move (o := s.getReg .x2 - 928 + 24) fr₃
    (by mem_tac [sp₂, y20] (b80002d74_m_x2_1752 g₃)) (by mem_tac [sp₂, y20] (b80002d74_m_x2_1760 g₃))
    (by mem_tac [sp₂, y20] (b80002d74_m_x2_1768 g₃)) (by mem_tac [sp₂, y20] (b80002d74_m_x2_1776 g₃))
    (by mem_tac [sp₂, y20] (b80002d74_m_x2_1784 g₃)) (by mem_tac [sp₂, y20] (b80002d74_m_x2_1792 g₃))
    (fun x _ h2 hw ↦ by simp only [Within] at hw; simp only [heapNext] at h2 hu₂; addr_omega [hw, h2, hb1, hu₂])
    (by addr_omega [hb1]) M₂.m.inv.heap hn₃.ge
  have Z₃ := Z₂.frame fr₃ (apart_off hpre (by decide) (by decide) (by decide)) (by addr_omega [hb1])
    (fun x h1 h2 hw ↦ by
      have := Z₂.buf; simp only [Within] at hw; simp only [heapNext] at this hu₂
      addr_omega [hw, h1, h2, hb1, hu₂, this]) hn₃.ge
    (by have := Z₂.buf; omega)
  have T := tableOf (op := 4) Z₃ F₃ (by decide)
  have hW₂ : W ≤ heapNext u := M.bb.2.2.2
  have M₄ := M₃.push (o := s.getReg .x2 - 928) (t := ⟨4, List.replicate 14 0, F⟩)
    (inSlot_off hpre (by decide)) T.1 (fun x hx ↦ by
      have := T.2 x hx; have := hn₁; omega)
  have x18 : u₃.getReg .x18 = Bb := by
    rw [b80002d74_x18 g₃, spAdd hpre sp₂ (N := 200) (M := 2456) (by decide)]; exact M₂.slot
  refine ⟨u₃, Q₂.trans p₃, Or.inl ⟨b80002d74_pc g₃, M₄, ?_, ?_, b80002d74_x12 g₃, b80002d74_x1 g₃, ?_, ?_,
    x18, by rw [k₃ .x20 (by decide)]; exact y20, ((r.keeps k₁).pres hp₂).keeps k₃⟩⟩
  · rw [b80002d74_x10 g₃, spAdd hpre sp₂ (N := 200) (M := 2456) (by decide)]; exact M₂.slot
  · rw [b80002d74_x11 g₃]; exact spAdd hpre sp₂ (by decide)
  · rw [k₃ .x8 (by decide), hp₂.reg .x8, k₁ .x8 (by decide)]; exact x8
  · rw [k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide)]; exact x9

end Rv64Verifier.Proofs.Walk
