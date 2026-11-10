import Rv64Verifier.Proofs.Walk.Jp3

/-!
# `walk`: `tables()`, JUMP's `bytecode` (R8)

From `jumpHead`'s end: `term(One, ZERO)` into `sp + 2504` and into `sp + 2240`, the five operands
copied into `P` and the `Vec` {5, `P`, 5} at `sp + 2240` (`jumpTerms`); `bytecode(11, OP_JUMP,
operands)` on the `Flushes` at `sp + 1728` (`jumpBc`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf FormVecOk formVecOf)

/-- JUMP's operands. -/
abbrev jumpOps : List LayoutMirror.FormRust :=
  [LayoutMirror.colRust 2 0, LayoutMirror.colRust 3 0, LayoutMirror.colRust 4 0,
    LayoutMirror.constantRust 0, LayoutMirror.constantRust 0]

set_option maxRecDepth 8192 in
/-- The two `term(One, ZERO)` calls, the operands copied into `P`, the `Vec` at `sp + 2240`, to
`bytecode`'s call. -/
theorem jumpTerms (hT : Rv64Verifier.Layout.TermSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {F : LayoutMirror.FlushesRust} {P : Word} (hpre : WalkPre s)
    (h : DS OI s u A k R Q B Bb W (L5 s) (s.getReg .x2 - 928) F W (P.toNat + 120) (jumpFs s P))
    (pal : P.toNat % 8 = 0) (hWP : W ≤ P.toNat) (pnx : P.toNat + 120 ≤ heapNext u)
    (pdeep : ∀ x, flushesDeep u (s.getReg .x2 - 928) x → x.toNat < P.toNat)
    (m0 : u.getMem (s.getReg .x2 - 224) = 0) (r : JR s u) (x20 : u.getReg .x20 = s.getReg .x2 - 512)
    (x25 : u.getReg .x25 = P) (x24 : u.getReg .x24 = 0xa0000068)
    (x10 : u.getReg .x10 = s.getReg .x2 - 152) (x11 : u.getReg .x11 = s.getReg .x2 - 224)
    (x12 : u.getReg .x12 = 0xa0000068) (x1 : u.getReg .x1 = 0x80002bb0) (hpc : u.pc = 0x800050a8) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b94 ∧ M8 OI s t A k R Q B Bb W (L5 s) ∧
      FB t (s.getReg .x2 - 928) F W ∧ FormVecOk t (s.getReg .x2 - 416) ∧
      formVecOf t (s.getReg .x2 - 416) = jumpOps ∧ vecPtr t (s.getReg .x2 - 416) = P ∧
      vecLen t (s.getReg .x2 - 416) = 5 ∧ P.toNat + 120 ≤ heapNext t ∧
      (∀ x, flushesDeep t (s.getReg .x2 - 928) x → x.toNat < P.toNat) ∧ JR s t ∧
      t.getReg .x20 = s.getReg .x2 - 512 ∧ t.getReg .x8 = 5 ∧ t.getReg .x24 = 0xa0000068 ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = 11 ∧ t.getReg .x12 = 4 ∧
      t.getReg .x13 = s.getReg .x2 - 416 ∧ t.getReg .x1 = 0x80002c5c) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hu := h.m.m.inv.heap.hi
  simp only [heapEnd] at hu
  have hb := h.m.bb
  have hs := hpre.heap.lo
  simp only [heapStart] at hs
  have hq := h.m.m.bufQ
  have hPlo : 0x20000000 ≤ P.toNat := by omega
  have hFo : InSlot s (s.getReg .x2 - 928) 48 := inSlot_off hpre (by decide)
  -- `term(One, ZERO)` into `sp + 2504`
  obtain ⟨t₁, q₁, ⟨pc₁, hp₁, D₁, -, mo₁, dd₁⟩ | d⟩ := termD hT (o := s.getReg .x2 - 152)
    (m := s.getReg .x2 - 224) hpre h (inSlot_off hpre (by decide)) (l5_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) (by forms_tac [hb1, hPlo, hu, pnx]) hpc x10 x11
    (inSlot_off hpre (by decide)) m0 x12
  swap
  · exact ⟨t₁, q₁, Or.inr d⟩
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := D₁.m.m.inv.sp
  have r₁ := r.pres hp₁
  have y20₁ : t₁.getReg .x20 = s.getReg .x2 - 512 := by rw [hp₁.reg .x20]; exact x20
  have hu₁ := D₁.m.m.inv.heap.hi
  simp only [heapEnd] at hu₁
  have pn₁ : P.toNat + 120 ≤ heapNext t₁ := by omega
  -- `[sp + 2432] := One`, `term(One, ZERO)` into `sp + 2240`
  obtain ⟨u₂, p₂, g₂⟩ := Sym.BlockSpec.reaches b80002bb0_spec
    (by rw [pc₁, returnAddress_eq, x1]; decide) (by
      rv_eval [sp₁, y20₁]
      valid_access hval [hb1])
  have fr₂ : Rv64Verifier.Layout.DFrame t₁ u₂ fun x ↦ Within x (s.getReg .x2 - 224) 8 :=
    Expect.ldframe g₂ (by
      rv_eval [sp₁, y20₁]
      simp only [Within]
      and_intros <;> addr_omega [hb1])
  obtain ⟨D₂, hn₂, dd₂, -⟩ := D₁.blk hpre (inSlot_off hpre (by decide)) (l5_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) _ (fun _ h ↦ h)
    (by forms_tac [hb1, hPlo, hu₁, pn₁]) fr₂ (b80002bb0_keeps g₂ .x2 (by decide))
  have x24₁ : t₁.getReg .x24 = 0xa0000068 := by rw [hp₁.reg .x24]; exact x24
  obtain ⟨t₃, q₃, ⟨pc₃, hp₃, D₃, -, mo₃, dd₃⟩ | d⟩ := termD hT (o := s.getReg .x2 - 416)
    (m := s.getReg .x2 - 224) hpre D₂ (inSlot_off hpre (by decide)) (l5_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) (by forms_tac [hb1, hPlo, hu₁, pn₁]) (b80002bb0_pc g₂)
    (by rw [b80002bb0_x10 g₂]; exact spAdd hpre sp₁ (by decide))
    (by rw [b80002bb0_x11 g₂]; exact spAdd hpre sp₁ (by decide)) (inSlot_off hpre (by decide))
    (by have := b80002bb0_m_x20_288 g₂; rw [y20₁] at this; rv_eval [] at this ⊢; exact this)
    (by rw [b80002bb0_x12 g₂, x24₁])
  swap
  · exact ⟨t₃, q₁.trans (p₂.trans q₃), Or.inr d⟩
  have Q₃ := q₁.trans (p₂.trans q₃)
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := D₃.m.m.inv.sp
  have r₃ := (r₁.keeps (b80002bb0_keeps g₂)).pres hp₃
  have y20 : t₃.getReg .x20 = s.getReg .x2 - 512 := by
    rw [hp₃.reg .x20, b80002bb0_keeps g₂ .x20 (by decide)]; exact y20₁
  have y25 : t₃.getReg .x25 = P := by
    rw [hp₃.reg .x25, b80002bb0_keeps g₂ .x25 (by decide), hp₁.reg .x25]; exact x25
  have y24 : t₃.getReg .x24 = 0xa0000068 := by
    rw [hp₃.reg .x24, b80002bb0_keeps g₂ .x24 (by decide)]; exact x24₁
  have M₁ := D₃.m
  have F₁ := D₃.fb
  have S₁ := D₃.sl
  have D₁' : ∀ x, flushesDeep t₃ (s.getReg .x2 - 928) x → x.toNat < P.toNat := fun x hx ↦ by
    rw [dd₃, dd₂, dd₁] at hx; exact pdeep x hx
  have hu₃ := M₁.m.inv.heap.hi
  simp only [heapEnd] at hu₃
  have pn₃ : P.toNat + 120 ≤ heapNext t₃ := by omega
  have hmP : Mapped P 120 := Or.inl ⟨by omega, by omega⟩
  -- the operands into `P`, the `Vec` at `sp + 2240`
  obtain ⟨u₄, p₄, g₄⟩ := Sym.BlockSpec.reaches b80002bd0_spec
    (by rw [pc₃, returnAddress_eq, b80002bb0_x1 g₂]; decide) (by
      rv_eval [sp₃, y20, y25]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [pal, hPlo, hu₃, pn₃]) (by addr_omega [pal, hPlo, hu₃, pn₃])
            (by addr_omega [pal, hPlo, hu₃, pn₃])
        | addr_omega [hb1, hPlo, hu₃, pn₃])
  have k₄ := b80002bd0_keeps g₄
  have fr₄ : Rv64Verifier.Layout.DFrame t₃ u₄ fun x ↦ Within x (s.getReg .x2 - 416) 24 ∨
      Within x (P + 24) 96 :=
    Expect.ldframe g₄ (by
      rv_eval [sp₃, y20, y25]
      simp only [Within]
      and_intros
      all_goals first
        | exact Or.inl (by addr_omega [hb1])
        | exact Or.inr (by addr_omega [hPlo, hu₃, pn₃]))
  have nw : ∀ x, x.toNat < P.toNat ∨ P.toNat + 120 ≤ x.toNat → x.toNat < heapNext t₃ →
      ¬ (Within x (s.getReg .x2 - 416) 24 ∨ Within x (P + 24) 96) := fun x h1 h2 hw ↦ by
    simp only [Within] at hw
    rcases hw with hw | hw <;> rcases h1 with h1 | h1 <;> addr_omega [hw, h1, h2, hb1, hPlo, hu₃, pn₃]
  have hn₄ : heapNext u₄ = heapNext t₃ := by
    simp only [heapNext]; rw [fr₄ _ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, hPlo, hu₃, pn₃])
      (by decide)]
  have hv₄ : HeapOk u₄ := ⟨hn₄ ▸ M₁.m.inv.heap.lo, hn₄ ▸ M₁.m.inv.heap.hi⟩
  have hW₄ := slotOk hpre M₁ (o := s.getReg .x2 - 416) (n := 24)
    (inSlot_off hpre (by decide)) (l5_off hpre (by decide))
  have hP₄ := heapOk hpre M₁ (o := P + 24) (n := 96) (by addr_omega [hWP, hPlo, hu₃, pn₃])
    (by addr_omega [hPlo, hu₃, pn₃])
  have M₄ := M₁.step hpre fr₄ (fun a ha ↦ ?_) (fun a ha ↦ ?_) hv₄ hn₄.ge (k₄ .x2 (by decide))
  rotate_left
  · rcases ha with ha | ha
    · exact ((hW₄ a ha).1).mono hn₄.ge
    · exact ((hP₄ a ha).1).mono hn₄.ge
  · rcases ha with ha | ha
    · exact (hW₄ a ha).2
    · exact (hP₄ a ha).2
  have F₄ := F₁.frame' fr₄ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, hPlo, hu₃, pn₃])
    (fun x hx ↦ nw x (Or.inl (D₁' x hx)) (F₁.ok.deep_below hx).2)
    (by addr_omega [hb1]) M₁.m.inv.heap hn₄.ge
  have sf (o : Word) (f : LayoutMirror.FormRust)
      (he : (o, f) ∈ (s.getReg .x2 - 416, LayoutMirror.constantRust 0) ::
        (s.getReg .x2 - 152, LayoutMirror.constantRust 0) :: jumpFs s P) :
      SF t₃ o f (P.toNat + 120) (heapNext t₃) := S₁.sf _ he
  have hbb : ∀ x, P.toNat + 120 ≤ x.toNat → x.toNat < heapNext t₃ →
      ¬ (Within x (s.getReg .x2 - 416) 24 ∨ Within x (P + 24) 96) := fun x h1 h2 ↦ nw x (Or.inr h1) h2
  have c0 := (sf P (LayoutMirror.colRust 2 0) (by simp)).frame fr₄ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, hPlo, hu₃, pn₃])
    hbb (by omega) M₁.m.inv.heap hn₄.ge
  have c1 := (sf (s.getReg .x2 - 1416) (LayoutMirror.colRust 3 0) (by simp)).move (o := P + 24) fr₄
    (by mem_tac [sp₃, y20, y25] (b80002bd0_m_x25_24 g₄))
    (by mem_tac [sp₃, y20, y25] (b80002bd0_m_x25_32 g₄))
    (by mem_tac [sp₃, y20, y25] (b80002bd0_m_x25_40 g₄)) hbb M₁.m.inv.heap hn₄.ge
  have c2 := (sf (s.getReg .x2 - 344) (LayoutMirror.colRust 4 0) (by simp)).move (o := P + 48) fr₄
    (by mem_tac [sp₃, y20, y25] (b80002bd0_m_x25_48 g₄))
    (by mem_tac [sp₃, y20, y25] (b80002bd0_m_x25_56 g₄))
    (by mem_tac [sp₃, y20, y25] (b80002bd0_m_x25_64 g₄)) hbb M₁.m.inv.heap hn₄.ge
  have c3 := (sf (s.getReg .x2 - 152) (LayoutMirror.constantRust 0) (by simp)).move (o := P + 72) fr₄
    (by mem_tac [sp₃, y20, y25] (b80002bd0_m_x25_72 g₄))
    (by mem_tac [sp₃, y20, y25] (b80002bd0_m_x25_80 g₄))
    (by mem_tac [sp₃, y20, y25] (b80002bd0_m_x25_88 g₄)) hbb M₁.m.inv.heap hn₄.ge
  have c4 := (sf (s.getReg .x2 - 416) (LayoutMirror.constantRust 0) (by simp)).move (o := P + 96) fr₄
    (by mem_tac [sp₃, y20, y25] (b80002bd0_m_x25_96 g₄))
    (by mem_tac [sp₃, y20, y25] (b80002bd0_m_x25_104 g₄))
    (by mem_tac [sp₃, y20, y25] (b80002bd0_m_x25_112 g₄)) hbb M₁.m.inv.heap hn₄.ge
  have vc : vecCap u₄ (s.getReg .x2 - 416) = 5 := by
    have := b80002bd0_m_x20_96 g₄; simp only [vecCap]; rv_eval [y20] at this ⊢; exact this
  have vp : vecPtr u₄ (s.getReg .x2 - 416) = P := by
    have := b80002bd0_m_x20_104 g₄; simp only [vecPtr]; rv_eval [y20, y25] at this ⊢; exact this
  have vl : vecLen u₄ (s.getReg .x2 - 416) = 5 := by
    have := b80002bd0_m_x20_112 g₄; simp only [vecLen]; rv_eval [y20] at this ⊢; exact this
  have pn₄ : P.toNat + 120 ≤ heapNext u₄ := by omega
  have V := vec5 vc vp vl pal hPlo (le_refl _) pn₄ c0 c1 c2 c3 c4
  refine ⟨u₄, Q₃.trans p₄, Or.inl ⟨b80002bd0_pc g₄, M₄, F₄.1, V.1, V.2, vp, vl, pn₄,
    fun x hx ↦ D₁' x (by rw [← F₄.2]; exact hx), r₃.keeps k₄, by rw [k₄ .x20 (by decide)]; exact y20,
    b80002bd0_x8 g₄, by rw [k₄ .x24 (by decide)]; exact y24, ?_, b80002bd0_x11 g₄, b80002bd0_x12 g₄, ?_,
    b80002bd0_x1 g₄⟩⟩
  · rw [b80002bd0_x10 g₄]; exact spAdd hpre sp₃ (by decide)
  · rw [b80002bd0_x13 g₄]; exact spAdd hpre sp₃ (by decide)

set_option maxRecDepth 8192 in
/-- `bytecode(11, OP_JUMP, operands)` on the `Flushes` at `sp + 1728`. -/
theorem jumpBc (hBC : Rv64Verifier.Layout.BytecodeSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {F : LayoutMirror.FlushesRust} {P : Word} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W (L5 s)) (fb : FB u (s.getReg .x2 - 928) F W)
    (hv : FormVecOk u (s.getReg .x2 - 416))
    (hvv : formVecOf u (s.getReg .x2 - 416) = jumpOps) (vp : vecPtr u (s.getReg .x2 - 416) = P)
    (vl : vecLen u (s.getReg .x2 - 416) = 5) (pnx : P.toNat + 120 ≤ heapNext u)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = 11) (x12 : u.getReg .x12 = 4)
    (x13 : u.getReg .x13 = s.getReg .x2 - 416) (hpc : u.pc = 0x80004b94) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      M8 OI s t A k R Q B Bb W (L5 s) ∧ FB t (s.getReg .x2 - 928) (F.bytecode 0 11 4 jumpOps) W ∧
      heapNext u ≤ heapNext t) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hn : Rv64Verifier.Layout.bytecodeStack ≤ 8736 := by decide
  have hFo : InSlot s (s.getReg .x2 - 928) (8 * 6) := inSlot_off hpre (by decide)
  obtain ⟨v1, v2, v3⟩ := slotW hpre h.m.inv hFo hn
  obtain ⟨w1, w2, w3⟩ := slotPre hpre h.m.inv (o := s.getReg .x2 - 416) (inSlot_off hpre (by decide)) hn
  have hu := h.m.inv.heap.hi
  simp only [heapEnd] at hu
  have e5 : (5 : Word).toNat = 5 := rfl
  have pre : Rv64Verifier.Layout.BytecodePre u := {
    heap := h.m.inv.heap
    stack := stk_sub hpre h.m.inv hn (by decide)
    self := by rw [x10]; exact v1
    ok := by rw [x10]; exact fb.ok
    selfFree := by rw [x10]; exact v2
    selfStack := by rw [x10]; exact v3
    rodata := h.m.inv.rodata hpre
    ops := by rw [x13]; exact w1
    opsOk := by rw [x13]; exact hv
    opsFree := by rw [x13]; exact w2
    opsStack := by rw [x13]; exact w3
    opsBuf := by rw [x13, vp, vl, e5]; exact ⟨Or.inl (by omega), by addr_omega [pnx, hu]⟩
    opsBufStack := by rw [x13, vp, vl, e5, stackLo_callee h.m.inv]; addr_omega [hb1, hn, pnx, hu] }
  obtain ⟨t, hr, ⟨hpct, hp, ⟨g, gv⟩⟩ | hd⟩ := hBC u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  rw [x10] at g gv
  rw [x11, x12, x13, hvv, fb.val] at gv
  obtain ⟨M, Fb⟩ := h.grow hpre fb (le_refl _) h.bb.2.2.2 hFo (l5_off hpre (by decide)) g hn (hp.reg .x2)
  rw [gv] at Fb
  exact ⟨t, hr, Or.inl ⟨hpct, hp, M, Fb, g.mono⟩⟩

end Rv64Verifier.Proofs.Walk
