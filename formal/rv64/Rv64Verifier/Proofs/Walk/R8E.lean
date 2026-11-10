import Rv64Verifier.Proofs.Walk.R8D

/-!
# `walk`: `tables()`, SET's operands (R8)

From `setHead`'s end: `col(2, 0)` straight into the operands' buffer `P`, `col(3, 0)`, `col(4, 0)`,
`col(5, 0)` into frame slots, `[sp + 2144] := One`, to `term(One, ZERO)`'s call (`setCols`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

/-- The registers SET keeps: `s0 = 8`, `s8 = &ZERO`, `s9 = P`, `s11 = 6`. -/
structure SetR (u : MachineState) (P : Word) : Prop where
  x8 : u.getReg .x8 = 8
  x24 : u.getReg .x24 = 0xa0000068
  x25 : u.getReg .x25 = P
  x27 : u.getReg .x27 = 6

theorem SetR.keeps {u t : MachineState} {P : Word} {l : List Reg} (h : SetR u P)
    (hk : ∀ r ∈ l, t.getReg r = u.getReg r)
    (hl : ∀ r ∈ ([.x8, .x24, .x25, .x27] : List Reg), r ∈ l := by decide) : SetR t P :=
  ⟨by rw [hk .x8 (hl _ (by decide))]; exact h.x8, by rw [hk .x24 (hl _ (by decide))]; exact h.x24,
    by rw [hk .x25 (hl _ (by decide))]; exact h.x25, by rw [hk .x27 (hl _ (by decide))]; exact h.x27⟩

theorem SetR.pres {u t : MachineState} {P : Word} (h : SetR u P) (hp : Preserves u t) : SetR t P :=
  h.keeps hp

/-- SET's four column operands: `col(5, 0)` at `sp + 2240`, `col(4, 0)` at `sp + 1168`, `col(3, 0)`
at `sp + 2504`, `col(2, 0)` at `P`. -/
abbrev setFs (s : MachineState) (P : Word) : List (Word × LayoutMirror.FormRust) :=
  [(s.getReg .x2 - 416, LayoutMirror.colRust 5 0), (s.getReg .x2 - 1488, LayoutMirror.colRust 4 0),
    (s.getReg .x2 - 152, LayoutMirror.colRust 3 0), (P, LayoutMirror.colRust 2 0)]

set_option maxRecDepth 8192 in
/-- SET's column operands, to `term(One, ZERO)`'s call into `sp + 2432`. -/
theorem setCols (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {F : LayoutMirror.FlushesRust} {lo : Nat} {P : Word} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W (L3 s)) (fb : FB u (s.getReg .x2 - 928) F lo)
    (ob : OpsBuf u (s.getReg .x2 - 928) P) (hlo : W ≤ lo) (hP : lo ≤ P.toNat) (r : SetR u P)
    (x10 : u.getReg .x10 = P) (x11 : u.getReg .x11 = 2) (x12 : u.getReg .x12 = 0)
    (x1 : u.getReg .x1 = 0x80002134) (hpc : u.pc = 0x80004b34) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x800050a8 ∧ M8 OI s t A k R Q B Bb W (L3 s) ∧
      FB t (s.getReg .x2 - 928) F lo ∧ SFs s t (P.toNat + 120) (setFs s P) ∧
      P.toNat + 120 ≤ heapNext t ∧ t.getMem (s.getReg .x2 - 512) = 0 ∧ SetR t P ∧
      t.getReg .x10 = s.getReg .x2 - 224 ∧ t.getReg .x11 = s.getReg .x2 - 512 ∧
      t.getReg .x12 = 0xa0000068 ∧ t.getReg .x23 = s.getReg .x2 - 512 ∧ t.getReg .x26 = 5 ∧
      t.getReg .x1 = 0x800021ac ∧
      ∀ x, flushesDeep t (s.getReg .x2 - 928) x → x.toNat < P.toNat) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨pal, pnx, pdeep⟩ := ob
  have hu := h.m.inv.heap.hi
  simp only [heapEnd] at hu
  have hb := h.bb
  have hq := h.m.bufQ
  have hs := hpre.heap.lo
  simp only [heapStart] at hs
  have hPlo : 0x20000000 ≤ P.toNat := by omega
  have hFo : InSlot s (s.getReg .x2 - 928) 48 := by simp only [InSlot]; addr_omega [hb1, hb3]
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  -- `col(2, 0)` into `P`
  have pre : Rv64Verifier.Layout.ColPre u := {
    heap := h.m.inv.heap
    stack := stk_sub hpre h.m.inv hn (by decide)
    out := by rw [x10]; exact Rv64Verifier.Layout.validMemRange_of pal (Or.inl ⟨by omega, by omega⟩)
    outFree := by rw [x10]; exact ⟨Or.inl (by omega), by addr_omega [pnx, hu]⟩
    outStack := by rw [x10, stackLo_callee h.m.inv]; addr_omega [hb1, hn, pnx, hu]
    rodata := h.m.inv.rodata hpre }
  obtain ⟨t₁, r₁, ⟨pc₁, hp₁, nf₁, fv₁⟩ | d⟩ := hC u hpc pre
  swap
  · exact ⟨t₁, r₁, Or.inr d⟩
  rw [x10] at nf₁ fv₁
  have K₁ := h.newForm hpre fb hFo nf₁ hn (fun a ha ↦ by
      simp only [Within] at ha
      refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))), ?_⟩
      simp only [M8W]
      refine ⟨by omega, ?_, ?_, ?_, fun e he hw ↦ ?_⟩
      · simp only [Within]; addr_omega [ha, hb1, pnx, hu]
      · simp only [Within]; addr_omega [ha, hb1, pnx, hu]
      · simp only [Within]; addr_omega [ha, hb1, pnx, hu]
      · obtain ⟨e1, -, -⟩ := (h.tabs e he).1
        simp only [Within] at hw; addr_omega [ha, hw, hb1, e1, pnx, hu])
    (fun a ha ↦ ⟨by simp only [Within] at ha ⊢; addr_omega [ha, hb1, pnx, hu],
      fun hd ↦ by have := pdeep a hd; simp only [Within] at ha; omega⟩) (hp₁.reg .x2)
  have hN₁ := nf₁.mono
  have S₁ : SFs s t₁ (P.toNat + 120) [(P, LayoutMirror.colRust 2 0)] :=
    (SFs.nil s t₁ _).cons (SF.ofNew nf₁ (by rw [fv₁, x11, x12]; rfl)) pnx (le_refl _)
      (Or.inr (by omega))
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := K₁.1.m.inv.sp
  obtain ⟨u₂, r₂, g₂⟩ := Sym.BlockSpec.reaches b80002134_spec
    (by rw [pc₁, returnAddress_eq, x1]; decide) trivial
  have k₂ := b80002134_keeps g₂
  have m₂ := b80002134_mem_same g₂
  have hn₂ : heapNext u₂ = heapNext t₁ := by simp only [heapNext, m₂]
  have M₂ := K₁.1.same hpre m₂ (k₂ .x2 (by decide))
  have F₂ := K₁.2.1.same hpre hFo K₁.1.m.inv.heap m₂
  have S₂ := S₁.same hpre m₂ K₁.1.m.inv.heap
  have R₂ := (r.pres hp₁).keeps k₂
  -- `col(3, 0)` into `sp + 2504`
  obtain ⟨t₃, r₃, ⟨pc₃, hp₃, M₃, F₃, hN₃, S₃, D₃⟩ | d⟩ := colSlot hC (o := s.getReg .x2 - 152) hpre M₂ F₂ hFo S₂ (by omega)
    (by simp only [InSlot]; addr_omega [hb1, hb3]) (l3_apart hpre (by addr_omega [hb1]))
    (fun a ha hw ↦ by simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
    (fun e he x hx hw ↦ by
      simp only [List.mem_singleton] at he; subst he; simp only [Within] at hx hw
      addr_omega [hx, hw, hb1, pnx, hu])
    (b80002134_pc g₂) (by rw [b80002134_x10 g₂]; exact spAdd hpre sp₁ (N := 2504) (M := 152) (by decide))
  swap
  · exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inr d⟩
  rw [b80002134_x11 g₂, b80002134_x12 g₂] at S₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := M₃.m.inv.sp
  obtain ⟨u₄, r₄, g₄⟩ := Sym.BlockSpec.reaches b8000214c_spec
    (by rw [pc₃, returnAddress_eq, b80002134_x1 g₂]; decide) trivial
  have k₄ := b8000214c_keeps g₄
  have m₄ := b8000214c_mem_same g₄
  have hn₄ : heapNext u₄ = heapNext t₃ := by simp only [heapNext, m₄]
  have M₄ := M₃.same hpre m₄ (k₄ .x2 (by decide))
  have F₄ := F₃.same hpre hFo M₃.m.inv.heap m₄
  have S₄ := S₃.same hpre m₄ M₃.m.inv.heap
  have R₄ := (R₂.pres hp₃).keeps k₄
  -- `col(4, 0)` into `sp + 1168`
  obtain ⟨t₅, r₅, ⟨pc₅, hp₅, M₅, F₅, hN₅, S₅, D₅⟩ | d⟩ := colSlot hC (o := s.getReg .x2 - 1488) hpre M₄ F₄ hFo S₄ (by omega)
    (by simp only [InSlot]; addr_omega [hb1, hb3]) (l3_apart hpre (by addr_omega [hb1]))
    (fun a ha hw ↦ by simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
    (fun e he x hx hw ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp only [Within] at hx hw <;> addr_omega [hx, hw, hb1, pnx, hu])
    (b8000214c_pc g₄) (by rw [b8000214c_x10 g₄]; exact spAdd hpre sp₃ (N := 1168) (M := 1488) (by decide))
  swap
  · exact ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inr d⟩
  rw [b8000214c_x11 g₄, b8000214c_x12 g₄] at S₅
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 2656 := M₅.m.inv.sp
  obtain ⟨u₆, r₆, g₆⟩ := Sym.BlockSpec.reaches b80002160_spec
    (by rw [pc₅, returnAddress_eq, b8000214c_x1 g₄]; decide) trivial
  have k₆ := b80002160_keeps g₆
  have m₆ := b80002160_mem_same g₆
  have hn₆ : heapNext u₆ = heapNext t₅ := by simp only [heapNext, m₆]
  have M₆ := M₅.same hpre m₆ (k₆ .x2 (by decide))
  have F₆ := F₅.same hpre hFo M₅.m.inv.heap m₆
  have S₆ := S₅.same hpre m₆ M₅.m.inv.heap
  have R₆ := (R₄.pres hp₅).keeps k₆
  -- `col(5, 0)` into `sp + 2240`
  obtain ⟨t₇, r₇, ⟨pc₇, hp₇, M₇, F₇, hN₇, S₇, D₇⟩ | d⟩ := colSlot hC (o := s.getReg .x2 - 416) hpre M₆ F₆ hFo S₆ (by omega)
    (by simp only [InSlot]; addr_omega [hb1, hb3]) (l3_apart hpre (by addr_omega [hb1]))
    (fun a ha hw ↦ by simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
    (fun e he x hx hw ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> simp only [Within] at hx hw <;> addr_omega [hx, hw, hb1, pnx, hu])
    (b80002160_pc g₆) (by rw [b80002160_x10 g₆]; exact spAdd hpre sp₅ (N := 2240) (M := 416) (by decide))
  swap
  · exact ⟨t₇, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans (r₆.trans r₇))))), Or.inr d⟩
  rw [b80002160_x11 g₆, b80002160_x12 g₆] at S₇
  have sp₇ : t₇.getReg .x2 = s.getReg .x2 - 2656 := M₇.m.inv.sp
  -- `[sp + 2144] := One`
  obtain ⟨u₈, r₈, g₈⟩ := Sym.BlockSpec.reaches b8000217c_spec
    (by rw [pc₇, returnAddress_eq, b80002160_x1 g₆]; decide) (by
      rv_eval [sp₇]
      valid_access hval [hb1])
  have k₈ := b8000217c_keeps g₈
  have fr₈ : Rv64Verifier.Layout.DFrame t₇ u₈ fun x ↦ Within x (s.getReg .x2 - 512) 24 :=
    Expect.ldframe g₈ (by
      rv_eval [sp₇]
      simp only [Within]
      and_intros <;> addr_omega [hb1])
  obtain ⟨M₈, F₈, S₈, hn₈, D₈⟩ := slotWrite (o := s.getReg .x2 - 512) hpre M₇ F₇ hFo S₇ (by simp only [InSlot]; addr_omega [hb1, hb3])
    (l3_apart hpre (by addr_omega [hb1])) (fun a ha hw ↦ by simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
    (fun e he x hx hw ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> simp only [Within] at hx hw <;> addr_omega [hx, hw, hb1, pnx, hu])
    fr₈ (k₈ .x2 (by decide))
  have R₇ := R₆.pres hp₇
  refine ⟨u₈, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans (r₆.trans (r₇.trans r₈)))))),
    Or.inl ⟨b8000217c_pc g₈, M₈, F₈, S₈, by omega, ?_,
      ⟨by rw [k₈ .x8 (by decide)]; exact R₇.x8, b8000217c_x24 g₈, by rw [k₈ .x25 (by decide)]; exact R₇.x25,
        by rw [k₈ .x27 (by decide)]; exact R₇.x27⟩, ?_, ?_, b8000217c_x12 g₈, ?_, ?_, b8000217c_x1 g₈, ?_⟩⟩
  · rw [← spAdd hpre sp₇ (N := 2144) (M := 512) (by decide)]; exact b8000217c_m_x2_2144 g₈
  · rw [b8000217c_x10 g₈]; exact spAdd hpre sp₇ (N := 2432) (M := 224) (by decide)
  · rw [b8000217c_x11 g₈]; exact spAdd hpre sp₇ (N := 2144) (M := 512) (by decide)
  · rw [b8000217c_x23 g₈]; exact spAdd hpre sp₇ (N := 2144) (M := 512) (by decide)
  · rw [k₈ .x26 (by decide), hp₇.reg .x26, b80002160_x26 g₆]

  · intro x hx
    rw [D₈, D₇, deep_same m₆, D₅, deep_same m₄, D₃, deep_same m₂, K₁.2.2] at hx
    exact pdeep x hx

end Rv64Verifier.Proofs.Walk
