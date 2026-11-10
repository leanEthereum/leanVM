import Rv64Verifier.Proofs.Walk.Jp2

/-!
# `walk`: `tables()`, JUMP's operands (R8)

From `jumpNfp`'s end: `alloc(8, 120)` for the operands `P`, `col(2, 0)` straight into `P`,
`col(3, 0)` into `sp + 1240`, `col(4, 0)` into `sp + 2312`, `[sp + 2432] := One`, to the first
`term(One, ZERO)` call (`jumpHead`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

/-- JUMP's column operands: `col(4, 0)` at `sp + 2312`, `col(3, 0)` at `sp + 1240`, `col(2, 0)` at
`P`. -/
abbrev jumpFs (s : MachineState) (P : Word) : List (Word × LayoutMirror.FormRust) :=
  [(s.getReg .x2 - 344, LayoutMirror.colRust 4 0), (s.getReg .x2 - 1416, LayoutMirror.colRust 3 0),
    (P, LayoutMirror.colRust 2 0)]

set_option maxRecDepth 8192 in
/-- `alloc(8, 120)`, JUMP's column operands, to the first `term(One, ZERO)` call. -/
theorem jumpHead (hAS : AllocSpec) (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {F : LayoutMirror.FlushesRust} (hpre : WalkPre s) (M : M8 OI s u A k R Q B Bb W (L5 s))
    (fb : FB u (s.getReg .x2 - 928) F W) (r : JR s u) (hpc : u.pc = 0x80002b28) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x800050a8 ∧ ∃ P : Word,
      DS OI s t A k R Q B Bb W (L5 s) (s.getReg .x2 - 928) F W (P.toNat + 120) (jumpFs s P) ∧
      P.toNat % 8 = 0 ∧ W ≤ P.toNat ∧ P.toNat + 120 ≤ heapNext t ∧
      (∀ x, flushesDeep t (s.getReg .x2 - 928) x → x.toNat < P.toNat) ∧
      t.getMem (s.getReg .x2 - 224) = 0 ∧ JR s t ∧ t.getReg .x20 = s.getReg .x2 - 512 ∧
      t.getReg .x25 = P ∧ t.getReg .x24 = 0xa0000068 ∧ t.getReg .x10 = s.getReg .x2 - 152 ∧
      t.getReg .x11 = s.getReg .x2 - 224 ∧ t.getReg .x12 = 0xa0000068 ∧ t.getReg .x1 = 0x80002bb0) ∨
      Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hFo : InSlot s (s.getReg .x2 - 928) 48 := inSlot_off hpre (by decide)
  have sp₀ : u.getReg .x2 = s.getReg .x2 - 2656 := M.m.inv.sp
  -- `alloc(8, 120)`
  obtain ⟨u₁, p₁, g₁⟩ := Sym.BlockSpec.reaches b80002b28_spec hpc trivial
  have m₁ := b80002b28_mem_same g₁
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have M₁ := M.same hpre m₁ (b80002b28_keeps g₁ .x2 (by decide))
  have F₁ := fb.same hpre hFo M.m.inv.heap m₁
  have D₁ := deep_same (o := s.getReg .x2 - 928) m₁
  obtain ⟨t₂, q₂, ⟨pc₂, hp₂, post₂⟩ | d⟩ := hAS.call (Reaches.refl u₁) (b80002b28_pc g₁)
    ⟨M₁.m.inv.heap, by rw [b80002b28_x10 g₁]; decide⟩
  swap
  · exact ⟨t₂, p₁.trans q₂, Or.inr d⟩
  have Q₂ := p₁.trans q₂
  have hal := post₂.aligned
  have hab := post₂.above
  have hnx := post₂.next
  rw [b80002b28_x10 g₁] at hal
  rw [b80002b28_x11 g₁] at hnx
  rw [show (8 : Word).toNat = 8 from rfl] at hal
  rw [show (120 : Word).toNat = 120 from rfl] at hnx
  set P := t₂.getReg .x10 with hP
  have fr₂ : Rv64Verifier.Layout.DFrame u₁ t₂ (Within · nextAddr 8) := fun a ha _ ↦
    post₂.mem a fun he ↦ ha a (by simp only [Within]; omega) (by rw [he]; simp only [Within]; omega)
  have hu₁ := M₁.m.inv.heap.hi
  have hW₁ := M₁.bb.2.2.2
  simp only [heapEnd] at hu₁
  have mono₂ : heapNext u₁ ≤ heapNext t₂ := by rw [hnx]; omega
  have M₂ := M₁.step hpre fr₂ (fun x hx ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))
    (fun x hx ↦ by
      simp only [M8W]
      refine ⟨?_, ?_, ?_, ?_, fun e he hw ↦ ?_⟩
      all_goals first
        | (simp only [Within, nextAddr] at hx ⊢; addr_omega [hx, hb1, hW₁, hu₁])
        | (obtain ⟨e1, -, -⟩ := (M₁.tabs e he).1; simp only [Within, nextAddr] at hx hw; addr_omega [hx, hw, e1, hb1]))
    post₂.heap mono₂ (hp₂.reg .x2)
  have F₂ := F₁.frame fr₂ (fun x hx hw ↦ by simp only [Within, nextAddr] at hx hw; addr_omega [hx, hw, hb1])
    (fun x _ h2 hw ↦ by simp only [Within, nextAddr] at hw; addr_omega [hw, h2, hu₁]) (by addr_omega [hb1])
    M₁.m.inv.heap mono₂
  have pdeep₂ : ∀ x, flushesDeep t₂ (s.getReg .x2 - 928) x → x.toNat < P.toNat := fun x hx ↦ by
    rw [F₂.2] at hx; have := (F₁.ok.deep_below hx).2; omega
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := M₂.m.inv.sp
  have hP0 : P ≠ 0 := fun he ↦ by
    have := congrArg BitVec.toNat he; rw [show (0 : Word).toNat = 0 from rfl] at this
    have := M₁.m.inv.heap.lo; simp only [heapStart] at this; omega
  obtain ⟨u₃, p₃, g₃⟩ := Sym.BlockSpec.reaches b80002b38_spec
    (by rw [pc₂, returnAddress_eq, b80002b28_x1 g₁]; decide) trivial
  obtain ⟨u₄, p₄, g₄⟩ := Sym.BlockSpec.reaches b80002b48_spec (b80002b38_pc_taken g₃ hP0) trivial
  have m₄ (a : Word) : u₄.getMem a = t₂.getMem a := (b80002b48_mem_same g₄ a).trans (b80002b38_mem_same g₃ a)
  have sp₄ : u₄.getReg .x2 = t₂.getReg .x2 := (b80002b48_keeps g₄ .x2 (by decide)).trans
    (b80002b38_keeps g₃ .x2 (by decide))
  have hn₄ : heapNext u₄ = heapNext t₂ := by simp only [heapNext, m₄]
  have M₄ := M₂.same hpre m₄ sp₄
  have F₄ := F₂.1.same hpre hFo M₂.m.inv.heap m₄
  have pdeep₄ : ∀ x, flushesDeep u₄ (s.getReg .x2 - 928) x → x.toNat < P.toNat := fun x hx ↦ by
    rw [deep_same m₄] at hx; exact pdeep₂ x hx
  have x10₄ : u₄.getReg .x10 = P := by
    rw [b80002b48_keeps g₄ .x10 (by decide), b80002b38_keeps g₃ .x10 (by decide)]
  have x25₄ : u₄.getReg .x25 = P := by rw [b80002b48_x25 g₄, b80002b38_keeps g₃ .x10 (by decide)]
  have x20₄ : u₄.getReg .x20 = s.getReg .x2 - 512 := by
    rw [b80002b48_keeps g₄ .x20 (by decide), b80002b38_x20 g₃]; exact spAdd hpre sp₂ (by decide)
  have r₄ := ((r.keeps (b80002b28_keeps g₁)).pres hp₂).keeps (b80002b38_keeps g₃) |>.keeps (b80002b48_keeps g₄)
  have Q₄ := Q₂.trans (p₃.trans p₄)
  have hu := M₄.m.inv.heap.hi
  simp only [heapEnd] at hu
  have hq := M₄.m.bufQ
  have hb := M₄.bb
  have hs := hpre.heap.lo
  simp only [heapStart] at hs
  have pnx : P.toNat + 120 ≤ heapNext u₄ := by rw [hn₄, hnx]
  have hWP : W ≤ P.toNat := by omega
  have hPlo : 0x20000000 ≤ P.toNat := by have := M₁.m.inv.heap.lo; simp only [heapStart] at this; omega
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  -- `col(2, 0)` into `P`
  have pre : Rv64Verifier.Layout.ColPre u₄ := {
    heap := M₄.m.inv.heap
    stack := stk_sub hpre M₄.m.inv hn (by decide)
    out := by rw [x10₄]; exact Rv64Verifier.Layout.validMemRange_of hal (Or.inl ⟨by omega, by omega⟩)
    outFree := by rw [x10₄]; exact ⟨Or.inl (by omega), by addr_omega [pnx, hu]⟩
    outStack := by rw [x10₄, stackLo_callee M₄.m.inv]; addr_omega [hb1, hn, pnx, hu]
    rodata := M₄.m.inv.rodata hpre }
  obtain ⟨t₅, q₅, ⟨pc₅, hp₅, nf₅, fv₅⟩ | d⟩ := hC u₄ (b80002b48_pc g₄) pre
  swap
  · exact ⟨t₅, Q₄.trans q₅, Or.inr d⟩
  rw [x10₄] at nf₅ fv₅
  have K₅ := M₄.newForm hpre F₄ hFo nf₅ hn (fun a ha ↦ by
      simp only [Within] at ha
      refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))), ?_⟩
      simp only [M8W]
      refine ⟨by omega, ?_, ?_, ?_, fun e he hw ↦ ?_⟩
      · simp only [Within]; addr_omega [ha, hb1, pnx, hu]
      · simp only [Within]; addr_omega [ha, hb1, pnx, hu]
      · simp only [Within]; addr_omega [ha, hb1, pnx, hu]
      · obtain ⟨e1, -, -⟩ := (M₄.tabs e he).1
        simp only [Within] at hw; addr_omega [ha, hw, hb1, e1, pnx, hu])
    (fun a ha ↦ ⟨by simp only [Within] at ha ⊢; addr_omega [ha, hb1, pnx, hu],
      fun hd ↦ by have := pdeep₄ a hd; simp only [Within] at ha; omega⟩) (hp₅.reg .x2)
  have S₅ : SFs s t₅ (P.toNat + 120) [(P, LayoutMirror.colRust 2 0)] :=
    (SFs.nil s t₅ _).cons (SF.ofNew nf₅ (by rw [fv₅, b80002b48_x11 g₄, b80002b48_x12 g₄]; rfl))
      (by rw [pnx.antisymm (by omega)]) (le_refl _) (Or.inr (by have := nf₅.mono; omega))
  have D₅ : DS OI s t₅ A k R Q B Bb W (L5 s) (s.getReg .x2 - 928) F W (P.toNat + 120)
      [(P, LayoutMirror.colRust 2 0)] := ⟨K₅.1, K₅.2.1, hFo, S₅, by have := nf₅.mono; omega⟩
  have pdeep₅ : ∀ x, flushesDeep t₅ (s.getReg .x2 - 928) x → x.toNat < P.toNat := fun x hx ↦
    pdeep₄ x (by rw [← K₅.2.2]; exact hx)
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 2656 := K₅.1.m.inv.sp
  have r₅ := r₄.pres hp₅
  have hu₅ := K₅.1.m.inv.heap.hi
  simp only [heapEnd] at hu₅
  have pn₅ : P.toNat + 120 ≤ heapNext t₅ := by have := nf₅.mono; omega
  -- `col(3, 0)` into `sp + 1240`
  obtain ⟨u₆, p₆, g₆⟩ := Sym.BlockSpec.reaches b80002b5c_spec
    (by rw [pc₅, returnAddress_eq, b80002b48_x1 g₄]; decide) trivial
  obtain ⟨E₆, -⟩ := D₅.same hpre (b80002b5c_mem_same g₆) (b80002b5c_keeps g₆ .x2 (by decide))
  obtain ⟨t₇, q₇, ⟨pc₇, hp₇, D₇, -, mo₇, dd₇⟩ | d⟩ := colD hC (o := s.getReg .x2 - 1416) hpre E₆
    (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (by forms_tac [hb1, hPlo, hu₅, pn₅]) (b80002b5c_pc g₆)
    (by rw [b80002b5c_x10 g₆]; exact spAdd hpre sp₅ (by decide))
  swap
  · exact ⟨t₇, Q₄.trans (q₅.trans (p₆.trans q₇)), Or.inr d⟩
  rw [b80002b5c_x11 g₆, b80002b5c_x12 g₆] at D₇
  have Q₇ := Q₄.trans (q₅.trans (p₆.trans q₇))
  have sp₇ : t₇.getReg .x2 = s.getReg .x2 - 2656 := D₇.m.m.inv.sp
  have r₇ := (r₅.keeps (b80002b5c_keeps g₆)).pres hp₇
  have hu₇ := D₇.m.m.inv.heap.hi
  simp only [heapEnd] at hu₇
  have pn₇ : P.toNat + 120 ≤ heapNext t₇ := by
    have : heapNext u₆ = heapNext t₅ := by simp only [heapNext, b80002b5c_mem_same g₆]
    omega
  -- `col(4, 0)` into `sp + 2312`
  obtain ⟨u₈, p₈, g₈⟩ := Sym.BlockSpec.reaches b80002b70_spec
    (by rw [pc₇, returnAddress_eq, b80002b5c_x1 g₆]; decide) trivial
  obtain ⟨E₈, -⟩ := D₇.same hpre (b80002b70_mem_same g₈) (b80002b70_keeps g₈ .x2 (by decide))
  obtain ⟨t₉, q₉, ⟨pc₉, hp₉, D₉, -, mo₉, dd₉⟩ | d⟩ := colD hC (o := s.getReg .x2 - 344) hpre E₈
    (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (by forms_tac [hb1, hPlo, hu₇, pn₇]) (b80002b70_pc g₈)
    (by rw [b80002b70_x10 g₈]; exact spAdd hpre sp₇ (by decide))
  swap
  · exact ⟨t₉, Q₇.trans (p₈.trans q₉), Or.inr d⟩
  rw [b80002b70_x11 g₈, b80002b70_x12 g₈] at D₉
  have Q₉ := Q₇.trans (p₈.trans q₉)
  have sp₉ : t₉.getReg .x2 = s.getReg .x2 - 2656 := D₉.m.m.inv.sp
  have r₉ := (r₇.keeps (b80002b70_keeps g₈)).pres hp₉
  have hu₉ := D₉.m.m.inv.heap.hi
  simp only [heapEnd] at hu₉
  have pn₉ : P.toNat + 120 ≤ heapNext t₉ := by
    have : heapNext u₈ = heapNext t₇ := by simp only [heapNext, b80002b70_mem_same g₈]
    omega
  have x20₉ : t₉.getReg .x20 = s.getReg .x2 - 512 := by
    rw [hp₉.reg .x20, b80002b70_keeps g₈ .x20 (by decide), hp₇.reg .x20,
      b80002b5c_keeps g₆ .x20 (by decide), hp₅.reg .x20]; exact x20₄
  -- `[sp + 2432] := One`
  obtain ⟨u₁₀, p₁₀, g₁₀⟩ := Sym.BlockSpec.reaches b80002b88_spec
    (by rw [pc₉, returnAddress_eq, b80002b70_x1 g₈]; decide) (by
      rv_eval [sp₉, x20₉]
      valid_access hval [hb1])
  have fr₁₀ : Rv64Verifier.Layout.DFrame t₉ u₁₀ fun x ↦ Within x (s.getReg .x2 - 224) 8 := by
    have := MemFrame.dframe (b80002b88_frame g₁₀ (by rw [x20₉]; addr_omega [hb1]))
    rwa [x20₉, show s.getReg .x2 - 512 + 288 = s.getReg .x2 - 224 by rv_eval []] at this
  obtain ⟨D₁₀, hn₁₀, dd₁₀, -⟩ := D₉.blk hpre (inSlot_off hpre (by decide)) (l5_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) _ (fun _ h ↦ h)
    (by forms_tac [hb1, hPlo, hu₉, pn₉]) fr₁₀ (b80002b88_keeps g₁₀ .x2 (by decide))
  refine ⟨u₁₀, Q₉.trans p₁₀, Or.inl ⟨b80002b88_pc g₁₀, P, D₁₀, hal, hWP, by omega, fun x hx ↦ ?_, ?_,
    r₉.keeps (b80002b88_keeps g₁₀), by rw [b80002b88_keeps g₁₀ .x20 (by decide)]; exact x20₉, ?_,
    b80002b88_x24 g₁₀, ?_, ?_, b80002b88_x12 g₁₀, b80002b88_x1 g₁₀⟩⟩
  · rw [dd₁₀, dd₉, deep_same (b80002b70_mem_same g₈), dd₇, deep_same (b80002b5c_mem_same g₆)] at hx
    exact pdeep₅ x hx
  · have := b80002b88_m_x20_288 g₁₀; rw [x20₉] at this; rv_eval [] at this ⊢; exact this
  · rw [b80002b88_keeps g₁₀ .x25 (by decide), hp₉.reg .x25, b80002b70_keeps g₈ .x25 (by decide),
      hp₇.reg .x25, b80002b5c_keeps g₆ .x25 (by decide), hp₅.reg .x25]; exact x25₄
  · rw [b80002b88_x10 g₁₀]; exact spAdd hpre sp₉ (by decide)
  · rw [b80002b88_x11 g₁₀]; exact spAdd hpre sp₉ (by decide)

end Rv64Verifier.Proofs.Walk
