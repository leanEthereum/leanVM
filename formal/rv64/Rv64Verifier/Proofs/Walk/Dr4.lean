import Rv64Verifier.Proofs.Walk.Dr3

/-!
# `walk`: `tables()`, DEREF's third stored value (R8)

From `0x800025c4` (the second value at `sp + 1728`, loaded into `s4`, `s5`, `s6`): `col(10, 0)`,
`prod(5, 10, 0)`, `prod(6, 10, 0)` into `sp + 1728 .. 1776`, their sum into `sp + 2240`, to
`0x800026d4` (`deref2`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

/-- A block's frame at `s7 + N` (`s7` = `sp + 2144`) as the frame slot `s - M`. -/
theorem mfr23 {s u v : MachineState} (hpre : WalkPre s) (y23 : u.getReg .x23 = s.getReg .x2 - 512)
    {N M : Word} {n : Nat} (hNM : N.toNat + M.toNat = 512)
    (h : MemFrame u v (u.getReg .x23 + N) n) :
    Rv64Verifier.Layout.DFrame u v (Within · (s.getReg .x2 - M) n) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have := MemFrame.dframe h
  rwa [y23, show s.getReg .x2 - 512 + N = s.getReg .x2 - M by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hNM]] at this

/-- DEREF's third stored value, `v3[2] + f_pc v3[2] + f_fp v3[2]`. -/
abbrev store2 : LayoutMirror.FormRust :=
  LayoutMirror.FormRust.sum [LayoutMirror.colRust 10 0, LayoutMirror.prodRust 5 10 0,
    LayoutMirror.prodRust 6 10 0]

set_option maxRecDepth 8192 in
/-- DEREF's third stored value summed into `sp + 2240`, the second held in `s4`, `s5`, `s6`. -/
theorem deref2 (hC : Rv64Verifier.Layout.ColSpec) (hP : Rv64Verifier.Layout.ProdSpec)
    (hA : Rv64Verifier.Layout.AddScaledSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W lo₂ H : Nat}
    {Fs : List (Word × LayoutMirror.FormRust)} {f : LayoutMirror.FormRust} (hpre : WalkPre s)
    (h : SS OI s u A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 1464) setT.flushes B lo₂ H Fs
      (s.getReg .x2 - 928) f) (r : DRg s u 0xa00000b0) {a b c : Word} (g8 : R3 u .x8 .x9 .x19 a b c)
    (hpc : u.pc = 0x800025c4) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x800026d4 ∧ ∃ H₂, heapNext u ≤ H₂ ∧
      SS OI s t A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 1464) setT.flushes B (heapNext u) H₂
        [(s.getReg .x2 - 880, LayoutMirror.prodRust 6 10 0), (s.getReg .x2 - 904, LayoutMirror.prodRust 5 10 0),
          (s.getReg .x2 - 928, LayoutMirror.colRust 10 0)] (s.getReg .x2 - 416) store2 ∧
      Keep u t (heapNext u) ∧ DRg s t 0xa00000b0 ∧
      R3 t .x20 .x21 .x22 (u.getMem (s.getReg .x2 - 928)) (u.getMem (s.getReg .x2 - 928 + 8))
        (u.getMem (s.getReg .x2 - 928 + 16)) ∧ R3 t .x8 .x9 .x19 a b c) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := h.m.m.inv.sp
  -- the second value into `s4`, `s5`, `s6`; `col(10, 0)` into `sp + 1728`
  obtain ⟨v₀, p₀, g₀⟩ := Sym.BlockSpec.reaches b800025c4_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have m₀ := b800025c4_mem_same g₀
  have hn₀ : heapNext v₀ = heapNext u := by simp only [heapNext, m₀]
  have D₀ : DS OI s v₀ A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 1464) setT.flushes B (heapNext u) [] :=
    ⟨h.m.same hpre m₀ (b800025c4_keeps g₀ .x2 (by decide)), h.fb.same hpre h.fo h.m.m.inv.heap m₀, h.fo,
      SFs.nil _ _ _, hn₀.ge⟩
  have G₀ : R3 v₀ .x20 .x21 .x22 (u.getMem (s.getReg .x2 - 928)) (u.getMem (s.getReg .x2 - 928 + 8))
      (u.getMem (s.getReg .x2 - 928 + 16)) :=
    ⟨by mem_tac [sp] (b800025c4_x20 g₀), by mem_tac [sp] (b800025c4_x21 g₀),
      by mem_tac [sp] (b800025c4_x22 g₀)⟩
  obtain ⟨t₁, q₁, ⟨pc₁, hp₁, D₁, K₁, -, -⟩ | d⟩ := colD hC (o := s.getReg .x2 - 928) hpre D₀
    (inSlot_off hpre (by decide)) (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (fun e he ↦ absurd he List.not_mem_nil) (b800025c4_pc g₀)
    (by rw [b800025c4_x10 g₀]; exact spAdd hpre sp (by decide))
  swap
  · exact ⟨t₁, p₀.trans q₁, Or.inr d⟩
  rw [b800025c4_x11 g₀, b800025c4_x12 g₀] at D₁
  have Q₁ := p₀.trans q₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := D₁.m.m.inv.sp
  have R₁ := (r.keeps (b800025c4_keeps g₀)).pres hp₁
  have G₁ := (G₀.keeps hp₁ (by decide) (by decide) (by decide))
  have F₀ := g8.keeps (b800025c4_keeps g₀) (by decide) (by decide) (by decide)
  have F₁ := F₀.keeps hp₁ (by decide) (by decide) (by decide)
  -- `prod(5, 10, 0)` into `sp + 1752`
  obtain ⟨u₂, p₂, g₂⟩ := Sym.BlockSpec.reaches b800025e4_spec
    (by rw [pc₁, returnAddress_eq, b800025c4_x1 g₀]; decide) trivial
  obtain ⟨E₂, hn₂⟩ := D₁.same hpre (b800025e4_mem_same g₂) (b800025e4_keeps g₂ .x2 (by decide))
  obtain ⟨t₂, q₂, ⟨pc₂, hp₂, D₂, K₂, -, -⟩ | d⟩ := prodD hP (o := s.getReg .x2 - 904) hpre E₂
    (inSlot_off hpre (by decide)) (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (by forms_tac [hb1]) (b800025e4_pc g₂)
    (by rw [b800025e4_x10 g₂]; exact spAdd hpre sp₁ (by decide))
  swap
  · exact ⟨t₂, Q₁.trans (p₂.trans q₂), Or.inr d⟩
  rw [b800025e4_x11 g₂, b800025e4_x12 g₂, b800025e4_x13 g₂] at D₂
  have Q₂ := Q₁.trans (p₂.trans q₂)
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := D₂.m.m.inv.sp
  have R₂ := (R₁.keeps (b800025e4_keeps g₂)).pres hp₂
  have G₂ := ((G₁.keeps (b800025e4_keeps g₂) (by decide) (by decide) (by decide)).keeps hp₂
    (by decide) (by decide) (by decide))
  have F₂ := ((F₁.keeps (b800025e4_keeps g₂) (by decide) (by decide) (by decide)).keeps hp₂
    (by decide) (by decide) (by decide))
  -- `prod(6, 10, 0)` into `sp + 1776`
  obtain ⟨u₃, p₃, g₃⟩ := Sym.BlockSpec.reaches b800025fc_spec
    (by rw [pc₂, returnAddress_eq, b800025e4_x1 g₂]; decide) trivial
  obtain ⟨E₃, hn₃⟩ := D₂.same hpre (b800025fc_mem_same g₃) (b800025fc_keeps g₃ .x2 (by decide))
  obtain ⟨t₃, q₃, ⟨pc₃, hp₃, D₃, K₃, -, -⟩ | d⟩ := prodD hP (o := s.getReg .x2 - 880) hpre E₃
    (inSlot_off hpre (by decide)) (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (by forms_tac [hb1]) (b800025fc_pc g₃)
    (by rw [b800025fc_x10 g₃]; exact spAdd hpre sp₂ (by decide))
  swap
  · exact ⟨t₃, Q₂.trans (p₃.trans q₃), Or.inr d⟩
  rw [b800025fc_x11 g₃, b800025fc_x12 g₃, b800025fc_x13 g₃] at D₃
  have Q₃ := Q₂.trans (p₃.trans q₃)
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := D₃.m.m.inv.sp
  have R₃ := (R₂.keeps (b800025fc_keeps g₃)).pres hp₃
  have G₃ := ((G₂.keeps (b800025fc_keeps g₃) (by decide) (by decide) (by decide)).keeps hp₃
    (by decide) (by decide) (by decide))
  have F₃ := ((F₂.keeps (b800025fc_keeps g₃) (by decide) (by decide) (by decide)).keeps hp₃
    (by decide) (by decide) (by decide))
  have y23 := R₃.x23
  -- the empty sum at `sp + 2240`, the first term
  obtain ⟨v₄, p₄, g₄⟩ := Sym.BlockSpec.reaches b80002614_spec
    (by rw [pc₃, returnAddress_eq, b800025fc_x1 g₃]; decide) (by
      rv_eval [sp₃, y23]
      and_intros <;> valid_access hval [hb1])
  have fr₄ := mfr23 hpre y23 (N := 96) (M := 416) (by decide)
    (b80002614_frame g₄ (by rw [y23]; addr_omega [hb1]))
  obtain ⟨S₄, -, K₄⟩ := SS.start hpre D₃ (acc := s.getReg .x2 - 416) (inSlot_off hpre (by decide))
    (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide)) (by forms_tac [hb1])
    (by slots_tac [hb1, hb3]) fr₄ (by mem_tac [y23] (b80002614_m_x23_96 g₄))
    (by have h' := b80002614_m_x23_104 g₄; rv_eval [y23] at h' ⊢; rw [h', R₃.x25])
    (by mem_tac [y23] (b80002614_m_x23_112 g₄)) (b80002614_keeps g₄ .x2 (by decide))
  obtain ⟨t₄, q₄, ⟨pc₄, hp₄, T₄, K₄', -⟩ | d⟩ := S₄.asc hA hpre (q := s.getReg .x2 - 928)
    (g := LayoutMirror.colRust 10 0) (by simp) ⟨_, _, rfl⟩ (b80002614_pc g₄)
    (by rw [b80002614_x10 g₄]; exact spAdd hpre sp₃ (by decide))
    (by rw [b80002614_x11 g₄]; exact ptrEq fr₄ (by rw [sp₃]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002614_x12 g₄]; exact lenEq fr₄ (by rw [sp₃]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002614_x13 g₄]; exact R₃.x24)
  swap
  · exact ⟨t₄, Q₃.trans (p₄.trans q₄), Or.inr d⟩
  have Q₄ := Q₃.trans (p₄.trans q₄)
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 2656 := T₄.m.m.inv.sp
  have R₄ := (R₃.keeps (b80002614_keeps g₄)).pres hp₄
  have G₄ := ((G₃.keeps (b80002614_keeps g₄) (by decide) (by decide) (by decide)).keeps hp₄
    (by decide) (by decide) (by decide))
  have F₄ := ((F₃.keeps (b80002614_keeps g₄) (by decide) (by decide) (by decide)).keeps hp₄
    (by decide) (by decide) (by decide))
  -- the second term
  obtain ⟨v₅, p₅, g₅⟩ := Sym.BlockSpec.reaches b8000264c_spec
    (by rw [pc₄, returnAddress_eq, b80002614_x1 g₄]; decide) (by
      rv_eval [sp₄, R₄.x23]
      and_intros <;> valid_access hval [hb1])
  have fr₅ := mfr23 hpre R₄.x23 (N := 96) (M := 416) (by decide)
    (b8000264c_frame g₅ (by rw [R₄.x23]; addr_omega [hb1]))
  obtain ⟨S₅, -, K₅⟩ := T₄.blk hpre fr₅ (by mem_tac [R₄.x23] (b8000264c_m_x23_96 g₅))
    (by mem_tac [R₄.x23] (b8000264c_m_x23_104 g₅)) (by mem_tac [R₄.x23] (b8000264c_m_x23_112 g₅))
    (b8000264c_keeps g₅ .x2 (by decide))
  obtain ⟨t₅, q₅, ⟨pc₅, hp₅, T₅, K₅', -⟩ | d⟩ := S₅.asc hA hpre (q := s.getReg .x2 - 904)
    (g := LayoutMirror.prodRust 5 10 0) (by simp) ⟨_, _, rfl⟩ (b8000264c_pc g₅)
    (by rw [b8000264c_x10 g₅]; exact spAdd hpre sp₄ (by decide))
    (by rw [b8000264c_x11 g₅]; exact ptrEq fr₅ (by rw [sp₄]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b8000264c_x12 g₅]; exact lenEq fr₅ (by rw [sp₄]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b8000264c_x13 g₅]; exact R₄.x24)
  swap
  · exact ⟨t₅, Q₄.trans (p₅.trans q₅), Or.inr d⟩
  have Q₅ := Q₄.trans (p₅.trans q₅)
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 2656 := T₅.m.m.inv.sp
  have R₅ := (R₄.keeps (b8000264c_keeps g₅)).pres hp₅
  have G₅ := ((G₄.keeps (b8000264c_keeps g₅) (by decide) (by decide) (by decide)).keeps hp₅
    (by decide) (by decide) (by decide))
  have F₅ := ((F₄.keeps (b8000264c_keeps g₅) (by decide) (by decide) (by decide)).keeps hp₅
    (by decide) (by decide) (by decide))
  -- the third term
  obtain ⟨v₆, p₆, g₆⟩ := Sym.BlockSpec.reaches b80002690_spec
    (by rw [pc₅, returnAddress_eq, b8000264c_x1 g₅]; decide) (by
      rv_eval [sp₅, R₅.x23]
      and_intros <;> valid_access hval [hb1])
  have fr₆ := mfr23 hpre R₅.x23 (N := 96) (M := 416) (by decide)
    (b80002690_frame g₆ (by rw [R₅.x23]; addr_omega [hb1]))
  obtain ⟨S₆, -, K₆⟩ := T₅.blk hpre fr₆ (by mem_tac [R₅.x23] (b80002690_m_x23_96 g₆))
    (by mem_tac [R₅.x23] (b80002690_m_x23_104 g₆)) (by mem_tac [R₅.x23] (b80002690_m_x23_112 g₆))
    (b80002690_keeps g₆ .x2 (by decide))
  obtain ⟨t₆, q₆, ⟨pc₆, hp₆, T₆, K₆', -⟩ | d⟩ := S₆.asc hA hpre (q := s.getReg .x2 - 880)
    (g := LayoutMirror.prodRust 6 10 0) (by simp) ⟨_, _, rfl⟩ (b80002690_pc g₆)
    (by rw [b80002690_x10 g₆]; exact spAdd hpre sp₅ (by decide))
    (by rw [b80002690_x11 g₆]; exact ptrEq fr₆ (by rw [sp₅]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002690_x12 g₆]; exact lenEq fr₆ (by rw [sp₅]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002690_x13 g₆]; exact R₅.x24)
  swap
  · exact ⟨t₆, Q₅.trans (p₆.trans q₆), Or.inr d⟩
  have hu₁ : heapNext u ≤ heapNext t₃ := D₃.hlo₂
  refine ⟨t₆, Q₅.trans (p₆.trans q₆), Or.inl ⟨by rw [pc₆, returnAddress_eq, b80002690_x1 g₆]; decide,
    heapNext t₃, hu₁, T₆, ?_, (R₅.keeps (b80002690_keeps g₆)).pres hp₆,
    (G₅.keeps (b80002690_keeps g₆) (by decide) (by decide) (by decide)).keeps hp₆
      (by decide) (by decide) (by decide),
    (F₅.keeps (b80002690_keeps g₆) (by decide) (by decide) (by decide)).keeps hp₆
      (by decide) (by decide) (by decide)⟩⟩
  have k₀ : Keep u v₀ (heapNext u) := Keep.of_same _ m₀
  exact k₀.trans ((K₁.mono hn₀.ge).trans ((Keep.of_same _ (b800025e4_mem_same g₂)).trans
    ((K₂.mono (by rw [hn₂]; exact D₁.hlo₂)).trans ((Keep.of_same _ (b800025fc_mem_same g₃)).trans
    ((K₃.mono (by rw [hn₃]; exact D₂.hlo₂)).trans ((K₄.mono hu₁).trans ((K₄'.mono hu₁).trans
    ((K₅.mono (le_trans hu₁ T₄.hH)).trans ((K₅'.mono hu₁).trans ((K₆.mono (le_trans hu₁ T₅.hH)).trans
    (K₆'.mono hu₁)))))))))))

end Rv64Verifier.Proofs.Walk
