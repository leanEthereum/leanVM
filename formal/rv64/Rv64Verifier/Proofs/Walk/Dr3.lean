import Rv64Verifier.Proofs.Walk.Dr2

/-!
# `walk`: `tables()`, DEREF's second stored value (R8)

From `0x800024b4` (the first value at `sp + 1728`, loaded into `s0`, `s1`, `s3`): `col(9, 0)`,
`prod(5, 9, 0)`, `prod(6, 9, 0)` into `sp + 2144 .. 2192`, their sum into `sp + 1728`, to
`0x800025c4` (`deref1`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

/-- Three registers holding three words. -/
structure R3 (t : MachineState) (r₁ r₂ r₃ : Reg) (a b c : Word) : Prop where
  h₁ : t.getReg r₁ = a
  h₂ : t.getReg r₂ = b
  h₃ : t.getReg r₃ = c

theorem R3.keeps {u t : MachineState} {r₁ r₂ r₃ : Reg} {a b c : Word} {l : List Reg}
    (h : R3 u r₁ r₂ r₃ a b c) (hk : ∀ r ∈ l, t.getReg r = u.getReg r) (m₁ : r₁ ∈ l) (m₂ : r₂ ∈ l)
    (m₃ : r₃ ∈ l) : R3 t r₁ r₂ r₃ a b c :=
  ⟨by rw [hk _ m₁]; exact h.h₁, by rw [hk _ m₂]; exact h.h₂, by rw [hk _ m₃]; exact h.h₃⟩

/-- DEREF's second stored value, `v3[1] + f_pc v3[1] + f_fp v3[1]`. -/
abbrev store1 : LayoutMirror.FormRust :=
  LayoutMirror.FormRust.sum [LayoutMirror.colRust 9 0, LayoutMirror.prodRust 5 9 0,
    LayoutMirror.prodRust 6 9 0]

set_option maxRecDepth 8192 in
/-- DEREF's second stored value summed into `sp + 1728`, the first held in `s0`, `s1`, `s3`. -/
theorem deref1 (hC : Rv64Verifier.Layout.ColSpec) (hP : Rv64Verifier.Layout.ProdSpec)
    (hA : Rv64Verifier.Layout.AddScaledSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W lo₂ H : Nat}
    {Fs : List (Word × LayoutMirror.FormRust)} {f : LayoutMirror.FormRust} (hpre : WalkPre s)
    (h : SS OI s u A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 1464) setT.flushes B lo₂ H Fs
      (s.getReg .x2 - 928) f) (r : DRg s u 0xa00000b0) (hpc : u.pc = 0x800024b4) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x800025c4 ∧ ∃ H₁, heapNext u ≤ H₁ ∧
      SS OI s t A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 1464) setT.flushes B (heapNext u) H₁
        [(s.getReg .x2 - 464, LayoutMirror.prodRust 6 9 0), (s.getReg .x2 - 488, LayoutMirror.prodRust 5 9 0),
          (s.getReg .x2 - 512, LayoutMirror.colRust 9 0)] (s.getReg .x2 - 928) store1 ∧
      Keep u t (heapNext u) ∧ DRg s t 0xa00000b0 ∧
      R3 t .x8 .x9 .x19 (u.getMem (s.getReg .x2 - 928)) (u.getMem (s.getReg .x2 - 928 + 8))
        (u.getMem (s.getReg .x2 - 928 + 16))) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := h.m.m.inv.sp
  -- the first value into `s0`, `s1`, `s3`; `col(9, 0)` into `sp + 2144`
  obtain ⟨v₀, p₀, g₀⟩ := Sym.BlockSpec.reaches b800024b4_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have m₀ := b800024b4_mem_same g₀
  have hn₀ : heapNext v₀ = heapNext u := by simp only [heapNext, m₀]
  have D₀ : DS OI s v₀ A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 1464) setT.flushes B (heapNext u) [] :=
    ⟨h.m.same hpre m₀ (b800024b4_keeps g₀ .x2 (by decide)), h.fb.same hpre h.fo h.m.m.inv.heap m₀, h.fo,
      SFs.nil _ _ _, hn₀.ge⟩
  have G₀ : R3 v₀ .x8 .x9 .x19 (u.getMem (s.getReg .x2 - 928)) (u.getMem (s.getReg .x2 - 928 + 8))
      (u.getMem (s.getReg .x2 - 928 + 16)) :=
    ⟨by mem_tac [sp] (b800024b4_x8 g₀), by mem_tac [sp] (b800024b4_x9 g₀),
      by mem_tac [sp] (b800024b4_x19 g₀)⟩
  obtain ⟨t₁, q₁, ⟨pc₁, hp₁, D₁, K₁, -, -⟩ | d⟩ := colD hC (o := s.getReg .x2 - 512) hpre D₀
    (inSlot_off hpre (by decide)) (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (fun e he ↦ absurd he List.not_mem_nil) (b800024b4_pc g₀)
    (by rw [b800024b4_x10 g₀]; exact spAdd hpre sp (by decide))
  swap
  · exact ⟨t₁, p₀.trans q₁, Or.inr d⟩
  rw [b800024b4_x11 g₀, b800024b4_x12 g₀] at D₁
  have Q₁ := p₀.trans q₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := D₁.m.m.inv.sp
  have R₁ := (r.keeps (b800024b4_keeps g₀)).pres hp₁
  have G₁ := (G₀.keeps hp₁ (by decide) (by decide) (by decide))
  -- `prod(5, 9, 0)` into `sp + 2168`
  obtain ⟨u₂, p₂, g₂⟩ := Sym.BlockSpec.reaches b800024d8_spec
    (by rw [pc₁, returnAddress_eq, b800024b4_x1 g₀]; decide) trivial
  obtain ⟨E₂, hn₂⟩ := D₁.same hpre (b800024d8_mem_same g₂) (b800024d8_keeps g₂ .x2 (by decide))
  obtain ⟨t₂, q₂, ⟨pc₂, hp₂, D₂, K₂, -, -⟩ | d⟩ := prodD hP (o := s.getReg .x2 - 488) hpre E₂
    (inSlot_off hpre (by decide)) (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (by forms_tac [hb1]) (b800024d8_pc g₂)
    (by rw [b800024d8_x10 g₂]; exact spAdd hpre sp₁ (by decide))
  swap
  · exact ⟨t₂, Q₁.trans (p₂.trans q₂), Or.inr d⟩
  rw [b800024d8_x11 g₂, b800024d8_x12 g₂, b800024d8_x13 g₂] at D₂
  have Q₂ := Q₁.trans (p₂.trans q₂)
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := D₂.m.m.inv.sp
  have R₂ := (R₁.keeps (b800024d8_keeps g₂)).pres hp₂
  have G₂ := ((G₁.keeps (b800024d8_keeps g₂) (by decide) (by decide) (by decide)).keeps hp₂
    (by decide) (by decide) (by decide))
  -- `prod(6, 9, 0)` into `sp + 2192`
  obtain ⟨u₃, p₃, g₃⟩ := Sym.BlockSpec.reaches b800024f4_spec
    (by rw [pc₂, returnAddress_eq, b800024d8_x1 g₂]; decide) trivial
  obtain ⟨E₃, hn₃⟩ := D₂.same hpre (b800024f4_mem_same g₃) (b800024f4_keeps g₃ .x2 (by decide))
  obtain ⟨t₃, q₃, ⟨pc₃, hp₃, D₃, K₃, -, -⟩ | d⟩ := prodD hP (o := s.getReg .x2 - 464) hpre E₃
    (inSlot_off hpre (by decide)) (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (by forms_tac [hb1]) (b800024f4_pc g₃)
    (by rw [b800024f4_x10 g₃]; exact spAdd hpre sp₂ (by decide))
  swap
  · exact ⟨t₃, Q₂.trans (p₃.trans q₃), Or.inr d⟩
  rw [b800024f4_x11 g₃, b800024f4_x12 g₃, b800024f4_x13 g₃] at D₃
  have Q₃ := Q₂.trans (p₃.trans q₃)
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := D₃.m.m.inv.sp
  have R₃ := (R₂.keeps (b800024f4_keeps g₃)).pres hp₃
  have G₃ := ((G₂.keeps (b800024f4_keeps g₃) (by decide) (by decide) (by decide)).keeps hp₃
    (by decide) (by decide) (by decide))
  have y23 := R₃.x23
  -- the empty sum at `sp + 1728`, the first term
  obtain ⟨v₄, p₄, g₄⟩ := Sym.BlockSpec.reaches b80002510_spec
    (by rw [pc₃, returnAddress_eq, b800024f4_x1 g₃]; decide) (by
      rv_eval [sp₃, y23]
      and_intros <;> valid_access hval [hb1])
  have fr₄ := mfr hpre sp₃ (N := 1728) (M := 928) (by decide) (b80002510_frame g₄ (by rw [sp₃]; addr_omega [hb1]))
  obtain ⟨S₄, -, K₄⟩ := SS.start hpre D₃ (acc := s.getReg .x2 - 928) (inSlot_off hpre (by decide))
    (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide)) (by forms_tac [hb1])
    (by slots_tac [hb1, hb3]) fr₄ (by mem_tac [sp₃] (b80002510_m_x2_1728 g₄))
    (by have h' := b80002510_m_x2_1736 g₄; rv_eval [sp₃] at h' ⊢; rw [h', R₃.x25])
    (by mem_tac [sp₃] (b80002510_m_x2_1744 g₄)) (b80002510_keeps g₄ .x2 (by decide))
  obtain ⟨t₄, q₄, ⟨pc₄, hp₄, T₄, K₄', -⟩ | d⟩ := S₄.asc hA hpre (q := s.getReg .x2 - 512)
    (g := LayoutMirror.colRust 9 0) (by simp) ⟨_, _, rfl⟩ (b80002510_pc g₄)
    (by rw [b80002510_x10 g₄]; exact spAdd hpre sp₃ (by decide))
    (by rw [b80002510_x11 g₄]; exact ptrEq fr₄ (by rw [y23]) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002510_x12 g₄]; exact lenEq fr₄ (by rw [y23]) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002510_x13 g₄]; exact R₃.x24)
  swap
  · exact ⟨t₄, Q₃.trans (p₄.trans q₄), Or.inr d⟩
  have Q₄ := Q₃.trans (p₄.trans q₄)
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 2656 := T₄.m.m.inv.sp
  have R₄ := (R₃.keeps (b80002510_keeps g₄)).pres hp₄
  have G₄ := ((G₃.keeps (b80002510_keeps g₄) (by decide) (by decide) (by decide)).keeps hp₄
    (by decide) (by decide) (by decide))
  -- the second term
  obtain ⟨v₅, p₅, g₅⟩ := Sym.BlockSpec.reaches b80002544_spec
    (by rw [pc₄, returnAddress_eq, b80002510_x1 g₄]; decide) (by
      rv_eval [sp₄, R₄.x23]
      and_intros <;> valid_access hval [hb1])
  have fr₅ := mfr hpre sp₄ (N := 1728) (M := 928) (by decide) (b80002544_frame g₅ (by rw [sp₄]; addr_omega [hb1]))
  obtain ⟨S₅, -, K₅⟩ := T₄.blk hpre fr₅ (by mem_tac [sp₄] (b80002544_m_x2_1728 g₅))
    (by mem_tac [sp₄] (b80002544_m_x2_1736 g₅)) (by mem_tac [sp₄] (b80002544_m_x2_1744 g₅))
    (b80002544_keeps g₅ .x2 (by decide))
  obtain ⟨t₅, q₅, ⟨pc₅, hp₅, T₅, K₅', -⟩ | d⟩ := S₅.asc hA hpre (q := s.getReg .x2 - 488)
    (g := LayoutMirror.prodRust 5 9 0) (by simp) ⟨_, _, rfl⟩ (b80002544_pc g₅)
    (by rw [b80002544_x10 g₅]; exact spAdd hpre sp₄ (by decide))
    (by rw [b80002544_x11 g₅]; exact ptrEq fr₅ (by rw [R₄.x23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002544_x12 g₅]; exact lenEq fr₅ (by rw [R₄.x23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002544_x13 g₅]; exact R₄.x24)
  swap
  · exact ⟨t₅, Q₄.trans (p₅.trans q₅), Or.inr d⟩
  have Q₅ := Q₄.trans (p₅.trans q₅)
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 2656 := T₅.m.m.inv.sp
  have R₅ := (R₄.keeps (b80002544_keeps g₅)).pres hp₅
  have G₅ := ((G₄.keeps (b80002544_keeps g₅) (by decide) (by decide) (by decide)).keeps hp₅
    (by decide) (by decide) (by decide))
  -- the third term
  obtain ⟨v₆, p₆, g₆⟩ := Sym.BlockSpec.reaches b80002584_spec
    (by rw [pc₅, returnAddress_eq, b80002544_x1 g₅]; decide) (by
      rv_eval [sp₅, R₅.x23]
      and_intros <;> valid_access hval [hb1])
  have fr₆ := mfr hpre sp₅ (N := 1728) (M := 928) (by decide) (b80002584_frame g₆ (by rw [sp₅]; addr_omega [hb1]))
  obtain ⟨S₆, -, K₆⟩ := T₅.blk hpre fr₆ (by mem_tac [sp₅] (b80002584_m_x2_1728 g₆))
    (by mem_tac [sp₅] (b80002584_m_x2_1736 g₆)) (by mem_tac [sp₅] (b80002584_m_x2_1744 g₆))
    (b80002584_keeps g₆ .x2 (by decide))
  obtain ⟨t₆, q₆, ⟨pc₆, hp₆, T₆, K₆', -⟩ | d⟩ := S₆.asc hA hpre (q := s.getReg .x2 - 464)
    (g := LayoutMirror.prodRust 6 9 0) (by simp) ⟨_, _, rfl⟩ (b80002584_pc g₆)
    (by rw [b80002584_x10 g₆]; exact spAdd hpre sp₅ (by decide))
    (by rw [b80002584_x11 g₆]; exact ptrEq fr₆ (by rw [R₅.x23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002584_x12 g₆]; exact lenEq fr₆ (by rw [R₅.x23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002584_x13 g₆]; exact R₅.x24)
  swap
  · exact ⟨t₆, Q₅.trans (p₆.trans q₆), Or.inr d⟩
  have hu₁ : heapNext u ≤ heapNext t₃ := by
    have := D₃.hlo₂; exact this
  refine ⟨t₆, Q₅.trans (p₆.trans q₆), Or.inl ⟨by rw [pc₆, returnAddress_eq, b80002584_x1 g₆]; decide,
    heapNext t₃, hu₁, T₆, ?_, (R₅.keeps (b80002584_keeps g₆)).pres hp₆,
    (G₅.keeps (b80002584_keeps g₆) (by decide) (by decide) (by decide)).keeps hp₆
      (by decide) (by decide) (by decide)⟩⟩
  have k₀ : Keep u v₀ (heapNext u) := Keep.of_same _ m₀
  have e₁ : heapNext v₀ = heapNext u := hn₀
  exact k₀.trans ((K₁.mono e₁.ge).trans ((Keep.of_same _ (b800024d8_mem_same g₂)).trans
    ((K₂.mono (by rw [hn₂]; exact D₁.hlo₂)).trans ((Keep.of_same _ (b800024f4_mem_same g₃)).trans
    ((K₃.mono (by rw [hn₃]; exact D₂.hlo₂)).trans ((K₄.mono hu₁).trans ((K₄'.mono hu₁).trans
    ((K₅.mono (le_trans hu₁ T₄.hH)).trans ((K₅'.mono hu₁).trans ((K₆.mono (le_trans hu₁ T₅.hH)).trans
    (K₆'.mono hu₁)))))))))))

end Rv64Verifier.Proofs.Walk
