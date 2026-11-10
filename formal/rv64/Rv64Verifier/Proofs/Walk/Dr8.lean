import Rv64Verifier.Proofs.Walk.Dr7

/-!
# `walk`: `tables()`, DEREF's operands and `bytecode` (R8)

From `0x8000275c`: `col(3, 0)`, `col(4, 0)`, `col(5, 0)`, `col(6, 0)` into frame slots, the block at
`0x800027bc` copying them into `P + 24 ..` with the `Vec` {5, `P`, 5} at `sp + 2408`, then
`bytecode(DEREF_CNT_BC, OP_DEREF, operands)` (`derefHead2`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf FormVecOk formVecOf)

/-- DEREF's operands. -/
abbrev derefOps : List LayoutMirror.FormRust :=
  [LayoutMirror.colRust 2 0, LayoutMirror.colRust 3 0, LayoutMirror.colRust 4 0,
    LayoutMirror.colRust 5 0, LayoutMirror.colRust 6 0]

set_option maxRecDepth 8192 in
/-- DEREF's operands into `P`, then `bytecode`. -/
theorem derefHead2 (hC : Rv64Verifier.Layout.ColSpec) (hBC : Rv64Verifier.Layout.BytecodeSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W lo₂ H : Nat}
    {F : LayoutMirror.FlushesRust} {P : Word} (hpre : WalkPre s) (hal : P.toNat % 8 = 0)
    (hHP : H ≤ P.toNat) (hWH : W ≤ H)
    (h : DS OI s u A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 344) F H (P.toNat + 120)
      [(P, LayoutMirror.colRust 2 0)])
    (pdeep : ∀ x, flushesDeep u (s.getReg .x2 - 344) x → x.toNat < P.toNat)
    (hS : SFh s u lo₂ H (storeFs s)) (r : DRg s u P) (hpc : u.pc = 0x8000275c) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80002848 ∧
      M8 OI s t A k R Q B Bb W (L4 s setT) ∧
      FB t (s.getReg .x2 - 344) (F.bytecode 0 14 3 derefOps) H ∧ SFh s t lo₂ H (storeFs s) ∧
      H ≤ heapNext t ∧ DRg s t P ∧ t.getReg .x21 = 6 ∧
      ∀ r ∈ ([.x19, .x22] : List Reg), t.getReg r = u.getReg r) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I := h.m.m.inv
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  have hu := I.heap.hi
  simp only [heapEnd] at hu
  have pnx : P.toNat + 120 ≤ heapNext u := h.hlo₂
  have hPe : P.toNat + 120 ≤ 0x78000000 := by simp only [heapNext] at pnx hu; omega
  have hHu : H ≤ heapNext u := by omega
  -- `col(3, 0)` into `sp + 2360`
  obtain ⟨u₁, p₁, g₁⟩ := Sym.BlockSpec.reaches b8000275c_spec hpc trivial
  have m₁ := b8000275c_mem_same g₁
  obtain ⟨E₁, hn₁⟩ := h.same hpre m₁ (b8000275c_keeps g₁ .x2 (by decide))
  have H₁ := hS.next hpre I (Rv64Verifier.Layout.DFrame.of_same m₁ _) hHu hn₁.ge
  obtain ⟨t₁, q₁, ⟨pc₁, hp₁, D₁, H₁', mo₁, dd₁⟩ | d⟩ := colE hC (o := s.getReg .x2 - 296) hpre E₁ H₁
    (by rw [hn₁]; exact hHu) (inSlot_off hpre (by decide)) (l4_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) (by forms_tac [hb1, hPe]) (by forms_tac [hb1])
    (b8000275c_pc g₁) (by rw [b8000275c_x10 g₁]; exact spAdd hpre sp (by decide))
  swap
  · exact ⟨t₁, p₁.trans q₁, Or.inr d⟩
  rw [b8000275c_x11 g₁, b8000275c_x12 g₁] at D₁
  have Q₁ := p₁.trans q₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := D₁.m.m.inv.sp
  have R₁ := (r.keeps (b8000275c_keeps g₁)).pres hp₁
  -- `col(4, 0)` into `sp + 2384`
  obtain ⟨u₂, p₂, g₂⟩ := Sym.BlockSpec.reaches b80002774_spec
    (by rw [pc₁, returnAddress_eq, b8000275c_x1 g₁]; decide) trivial
  have m₂ := b80002774_mem_same g₂
  obtain ⟨E₂, hn₂⟩ := D₁.same hpre m₂ (b80002774_keeps g₂ .x2 (by decide))
  have H₂ := H₁'.next hpre D₁.m.m.inv (Rv64Verifier.Layout.DFrame.of_same m₂ _)
    (by rw [hn₁] at mo₁; omega) hn₂.ge
  obtain ⟨t₂, q₂, ⟨pc₂, hp₂, D₂, H₂', mo₂, dd₂⟩ | d⟩ := colE hC (o := s.getReg .x2 - 272) hpre E₂ H₂
    (by rw [hn₂]; rw [hn₁] at mo₁; omega) (inSlot_off hpre (by decide)) (l4_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) (by forms_tac [hb1, hPe]) (by forms_tac [hb1])
    (b80002774_pc g₂) (by rw [b80002774_x10 g₂]; exact spAdd hpre sp₁ (by decide))
  swap
  · exact ⟨t₂, Q₁.trans (p₂.trans q₂), Or.inr d⟩
  rw [b80002774_x11 g₂, b80002774_x12 g₂] at D₂
  have Q₂ := Q₁.trans (p₂.trans q₂)
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := D₂.m.m.inv.sp
  have R₂ := (R₁.keeps (b80002774_keeps g₂)).pres hp₂
  -- `col(5, 0)` into `sp + 2408`
  obtain ⟨u₃, p₃, g₃⟩ := Sym.BlockSpec.reaches b8000278c_spec
    (by rw [pc₂, returnAddress_eq, b80002774_x1 g₂]; decide) trivial
  have m₃ := b8000278c_mem_same g₃
  obtain ⟨E₃, hn₃⟩ := D₂.same hpre m₃ (b8000278c_keeps g₃ .x2 (by decide))
  have H₃ := H₂'.next hpre D₂.m.m.inv (Rv64Verifier.Layout.DFrame.of_same m₃ _)
    (by rw [hn₂] at mo₂; rw [hn₁] at mo₁; omega) hn₃.ge
  obtain ⟨t₃, q₃, ⟨pc₃, hp₃, D₃, H₃', mo₃, dd₃⟩ | d⟩ := colE hC (o := s.getReg .x2 - 248) hpre E₃ H₃
    (by rw [hn₃]; rw [hn₂] at mo₂; rw [hn₁] at mo₁; omega) (inSlot_off hpre (by decide))
    (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (by forms_tac [hb1, hPe]) (by forms_tac [hb1])
    (b8000278c_pc g₃) (by rw [b8000278c_x10 g₃]; exact spAdd hpre sp₂ (by decide))
  swap
  · exact ⟨t₃, Q₂.trans (p₃.trans q₃), Or.inr d⟩
  rw [b8000278c_x11 g₃, b8000278c_x12 g₃] at D₃
  have Q₃ := Q₂.trans (p₃.trans q₃)
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := D₃.m.m.inv.sp
  have R₃ := (R₂.keeps (b8000278c_keeps g₃)).pres hp₃
  -- `col(6, 0)` into `sp + 1240`
  obtain ⟨u₄, p₄, g₄⟩ := Sym.BlockSpec.reaches b800027a4_spec
    (by rw [pc₃, returnAddress_eq, b8000278c_x1 g₃]; decide) trivial
  have m₄ := b800027a4_mem_same g₄
  obtain ⟨E₄, hn₄⟩ := D₃.same hpre m₄ (b800027a4_keeps g₄ .x2 (by decide))
  have H₄ := H₃'.next hpre D₃.m.m.inv (Rv64Verifier.Layout.DFrame.of_same m₄ _)
    (by rw [hn₃] at mo₃; rw [hn₂] at mo₂; rw [hn₁] at mo₁; omega) hn₄.ge
  obtain ⟨t₄, q₄, ⟨pc₄, hp₄, D₄, H₄', mo₄, dd₄⟩ | d⟩ := colE hC (o := s.getReg .x2 - 1416) hpre E₄ H₄
    (by rw [hn₄]; rw [hn₃] at mo₃; rw [hn₂] at mo₂; rw [hn₁] at mo₁; omega) (inSlot_off hpre (by decide))
    (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (by forms_tac [hb1, hPe]) (by forms_tac [hb1])
    (b800027a4_pc g₄) (by rw [b800027a4_x10 g₄]; exact spAdd hpre sp₃ (by decide))
  swap
  · exact ⟨t₄, Q₃.trans (p₄.trans q₄), Or.inr d⟩
  rw [b800027a4_x11 g₄, b800027a4_x12 g₄] at D₄
  have Q₄ := Q₃.trans (p₄.trans q₄)
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 2656 := D₄.m.m.inv.sp
  have R₄ := (R₃.keeps (b800027a4_keeps g₄)).pres hp₄
  have x21₄ : t₄.getReg .x21 = 6 := by rw [hp₄.reg .x21, b800027a4_x21 g₄]
  have y23 := R₄.x23
  have y24 := R₄.x24
  have y26 := R₄.x26
  have hHt : H ≤ heapNext t₄ := by
    rw [hn₄] at mo₄; rw [hn₃] at mo₃; rw [hn₂] at mo₂; rw [hn₁] at mo₁; omega
  have pn₄ : P.toNat + 120 ≤ heapNext t₄ := D₄.hlo₂
  have hu₄ := D₄.m.m.inv.heap.hi
  simp only [heapEnd] at hu₄
  have hPh : 0x20000000 ≤ P.toNat := by
    have := D₄.m.m.inv.heap.lo; have := h.m.bb; have := h.m.m.bufQ; have := hpre.heap.lo
    simp only [heapStart] at *; omega
  have hmP : Mapped P 120 := Or.inl ⟨by omega, by omega⟩
  have pdeep₄ : ∀ x, flushesDeep t₄ (s.getReg .x2 - 344) x → x.toNat < P.toNat := fun x hx ↦
    pdeep x (by rw [← deep_same m₁, ← dd₁, ← deep_same m₂, ← dd₂, ← deep_same m₃, ← dd₃,
      ← deep_same m₄, ← dd₄]; exact hx)
  -- the operands into `P`, the `Vec` at `sp + 2408`
  obtain ⟨v, p₅, g₅⟩ := Sym.BlockSpec.reaches b800027bc_spec
    (by rw [pc₄, returnAddress_eq, b800027a4_x1 g₄]; decide) (by
      rv_eval [sp₄, y23, y24]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [hal, hPh, hPe]) (by addr_omega [hal, hPh, hPe])
            (by addr_omega [hal, hPh, hPe])
        | addr_omega [hb1, hPh, hPe])
  have k₅ := b800027bc_keeps g₅
  have fr₅ : Rv64Verifier.Layout.DFrame t₄ v fun x ↦ Within x (s.getReg .x2 - 248) 24 ∨
      Within x (P + 24) 96 :=
    Expect.ldframe g₅ (by
      rv_eval [sp₄, y23, y24]
      simp only [Within]
      and_intros
      all_goals first
        | exact Or.inl (by addr_omega [hb1])
        | exact Or.inr (by addr_omega [hPh, hPe]))
  have nw : ∀ x, x.toNat < P.toNat ∨ P.toNat + 120 ≤ x.toNat → x.toNat < heapNext t₄ →
      ¬ (Within x (s.getReg .x2 - 248) 24 ∨ Within x (P + 24) 96) := fun x h1 h2 hw ↦ by
    simp only [heapNext] at h2 hu₄
    simp only [Within] at hw
    rcases hw with hw | hw <;> rcases h1 with h1 | h1 <;> addr_omega [hw, h1, h2, hb1, hPh, hPe, hu₄]
  have hn₅ : heapNext v = heapNext t₄ := by
    simp only [heapNext]; rw [fr₅ _ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, hPh, hPe])
      (by decide)]
  have hv₅ : HeapOk v := ⟨hn₅ ▸ D₄.m.m.inv.heap.lo, hn₅ ▸ D₄.m.m.inv.heap.hi⟩
  have hW₅ := slotOk hpre D₄.m (o := s.getReg .x2 - 248) (n := 24) (inSlot_off hpre (by decide))
    (l4_off hpre (by decide))
  have hP₅ := heapOk hpre D₄.m (o := P + 24) (n := 96) (by addr_omega [hWH, hHP, hPh, hPe])
    (by addr_omega [hPh, hPe, pn₄])
  have M₅ := D₄.m.step hpre fr₅ (fun a ha ↦ ?_) (fun a ha ↦ ?_) hv₅ hn₅.ge (k₅ .x2 (by decide))
  rotate_left
  · rcases ha with ha | ha
    · exact ((hW₅ a ha).1).mono hn₅.ge
    · exact ((hP₅ a ha).1).mono hn₅.ge
  · rcases ha with ha | ha
    · exact (hW₅ a ha).2
    · exact (hP₅ a ha).2
  have F₅ := D₄.fb.frame' fr₅ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, hPh, hPe])
    (fun x hx ↦ nw x (Or.inl (pdeep₄ x hx)) (D₄.fb.ok.deep_below hx).2)
    (by addr_omega [hb1]) D₄.m.m.inv.heap hn₅.ge
  have H₅ := H₄'.frame' (o := s.getReg .x2 - 248) (n := 0) (lo' := P.toNat + 24) (hi' := P.toNat + 120)
    hpre D₄.m.m.inv (fr₅.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (Or.inl ha)
      · exact Or.inr (by simp only [Within] at ha; addr_omega [ha, hPh, hPe])) (by decide)
    (inSlot_off hpre (by decide)) (by forms_tac [hb1]) (Or.inl (by omega)) hHt (by rw [hn₅]; exact pn₄)
    hv₅ hn₅.ge
  have sf (o : Word) (f : LayoutMirror.FormRust)
      (he : (o, f) ∈ [(s.getReg .x2 - 1416, LayoutMirror.colRust 6 0),
        (s.getReg .x2 - 248, LayoutMirror.colRust 5 0), (s.getReg .x2 - 272, LayoutMirror.colRust 4 0),
        (s.getReg .x2 - 296, LayoutMirror.colRust 3 0), (P, LayoutMirror.colRust 2 0)]) :
      SF t₄ o f (P.toNat + 120) (heapNext t₄) := D₄.sl.sf _ he
  have hb : ∀ x, P.toNat + 120 ≤ x.toNat → x.toNat < heapNext t₄ →
      ¬ (Within x (s.getReg .x2 - 248) 24 ∨ Within x (P + 24) 96) := fun x h1 h2 ↦ nw x (Or.inr h1) h2
  have c0 := (sf P (LayoutMirror.colRust 2 0) (by simp)).frame fr₅ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, hPh, hPe])
    hb (by omega) D₄.m.m.inv.heap hn₅.ge
  have c1 := (sf (s.getReg .x2 - 296) (LayoutMirror.colRust 3 0) (by simp)).move (o := P + 24) fr₅
    (by mem_tac [sp₄, y23, y24] (b800027bc_m_x24_24 g₅)) (by mem_tac [sp₄, y23, y24] (b800027bc_m_x24_32 g₅))
    (by mem_tac [sp₄, y23, y24] (b800027bc_m_x24_40 g₅)) hb D₄.m.m.inv.heap hn₅.ge
  have c2 := (sf (s.getReg .x2 - 272) (LayoutMirror.colRust 4 0) (by simp)).move (o := P + 48) fr₅
    (by mem_tac [sp₄, y23, y24] (b800027bc_m_x24_48 g₅)) (by mem_tac [sp₄, y23, y24] (b800027bc_m_x24_56 g₅))
    (by mem_tac [sp₄, y23, y24] (b800027bc_m_x24_64 g₅)) hb D₄.m.m.inv.heap hn₅.ge
  have c3 := (sf (s.getReg .x2 - 248) (LayoutMirror.colRust 5 0) (by simp)).move (o := P + 72) fr₅
    (by mem_tac [sp₄, y23, y24] (b800027bc_m_x24_72 g₅)) (by mem_tac [sp₄, y23, y24] (b800027bc_m_x24_80 g₅))
    (by mem_tac [sp₄, y23, y24] (b800027bc_m_x24_88 g₅)) hb D₄.m.m.inv.heap hn₅.ge
  have c4 := (sf (s.getReg .x2 - 1416) (LayoutMirror.colRust 6 0) (by simp)).move (o := P + 96) fr₅
    (by mem_tac [sp₄, y23, y24] (b800027bc_m_x24_96 g₅)) (by mem_tac [sp₄, y23, y24] (b800027bc_m_x24_104 g₅))
    (by mem_tac [sp₄, y23, y24] (b800027bc_m_x24_112 g₅)) hb D₄.m.m.inv.heap hn₅.ge
  have vc : vecCap v (s.getReg .x2 - 248) = 5 := by
    have := b800027bc_m_x23_264 g₅; simp only [vecCap]; rv_eval [y23, y26] at this ⊢; exact this
  have vp : vecPtr v (s.getReg .x2 - 248) = P := by
    have := b800027bc_m_x23_272 g₅; simp only [vecPtr]; rv_eval [y23, y24] at this ⊢; exact this
  have vl : vecLen v (s.getReg .x2 - 248) = 5 := by
    have := b800027bc_m_x23_280 g₅; simp only [vecLen]; rv_eval [y23, y26] at this ⊢; exact this
  have pn₅ : P.toNat + 120 ≤ heapNext v := by omega
  have V := vec5 vc vp vl hal hPh (le_refl _) pn₅ c0 c1 c2 c3 c4
  -- `bytecode(DEREF_CNT_BC, OP_DEREF, operands)`
  have sp₅ : v.getReg .x2 = s.getReg .x2 - 2656 := M₅.m.inv.sp
  have hnB : Rv64Verifier.Layout.bytecodeStack ≤ 8736 := by decide
  have hFo : InSlot s (s.getReg .x2 - 344) (8 * 6) := inSlot_off hpre (by decide)
  obtain ⟨v1, v2, v3⟩ := slotW hpre M₅.m.inv hFo hnB
  obtain ⟨w1, w2, w3⟩ := slotPre hpre M₅.m.inv (o := s.getReg .x2 - 248) (inSlot_off hpre (by decide)) hnB
  have hu₅ := M₅.m.inv.heap.hi
  simp only [heapEnd] at hu₅
  have e5 : (5 : Word).toNat = 5 := rfl
  have x10₅ : v.getReg .x10 = s.getReg .x2 - 344 := by rw [b800027bc_x10 g₅]; exact spAdd hpre sp₄ (by decide)
  have x13₅ : v.getReg .x13 = s.getReg .x2 - 248 := by rw [b800027bc_x13 g₅]; exact spAdd hpre sp₄ (by decide)
  have pre : Rv64Verifier.Layout.BytecodePre v := {
    heap := M₅.m.inv.heap
    stack := stk_sub hpre M₅.m.inv hnB (by decide)
    self := by rw [x10₅]; exact v1
    ok := by rw [x10₅]; exact F₅.1.ok
    selfFree := by rw [x10₅]; exact v2
    selfStack := by rw [x10₅]; exact v3
    rodata := M₅.m.inv.rodata hpre
    ops := by rw [x13₅]; exact w1
    opsOk := by rw [x13₅]; exact V.1
    opsFree := by rw [x13₅]; exact w2
    opsStack := by rw [x13₅]; exact w3
    opsBuf := by rw [x13₅, vp, vl, e5]; exact ⟨Or.inl (by omega), by addr_omega [pn₅, hu₅]⟩
    opsBufStack := by rw [x13₅, vp, vl, e5, stackLo_callee M₅.m.inv]; addr_omega [hb1, hnB, pn₅, hu₅] }
  obtain ⟨t₆, q₆, ⟨pc₆, hp₆, ⟨g₆, gv₆⟩⟩ | d⟩ := hBC v (b800027bc_pc g₅) pre
  swap
  · exact ⟨t₆, Q₄.trans (p₅.trans q₆), Or.inr d⟩
  rw [x10₅] at g₆ gv₆
  rw [b800027bc_x11 g₅, b800027bc_x12 g₅, x13₅, V.2, F₅.1.val] at gv₆
  have hHv : H ≤ heapNext v := by omega
  obtain ⟨M₆, F₆⟩ := M₅.grow hpre F₅.1 hWH hHv h.fo (l4_off hpre (by decide)) g₆ hnB (hp₆.reg .x2)
  rw [gv₆] at F₆
  have H₆ := H₅.grow hpre M₅.m.inv g₆ F₅.1 (le_refl _) h.fo (by forms_tac [hb1]) hnB hHv
  refine ⟨t₆, Q₄.trans (p₅.trans q₆), Or.inl ⟨by rw [pc₆, returnAddress_eq, b800027bc_x1 g₅]; decide,
    M₆, F₆, H₆, le_trans hHv g₆.mono, (R₄.keeps k₅).pres hp₆,
    by rw [hp₆.reg .x21, k₅ .x21 (by decide)]; exact x21₄, ?_⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hp₆.reg .x19, k₅ .x19 (by decide), hp₄.reg .x19, b800027a4_keeps g₄ .x19 (by decide),
      hp₃.reg .x19, b8000278c_keeps g₃ .x19 (by decide), hp₂.reg .x19, b80002774_keeps g₂ .x19 (by decide),
      hp₁.reg .x19, b8000275c_keeps g₁ .x19 (by decide)]
  · rw [hp₆.reg .x22, k₅ .x22 (by decide), hp₄.reg .x22, b800027a4_keeps g₄ .x22 (by decide),
      hp₃.reg .x22, b8000278c_keeps g₃ .x22 (by decide), hp₂.reg .x22, b80002774_keeps g₂ .x22 (by decide),
      hp₁.reg .x22, b8000275c_keeps g₁ .x22 (by decide)]

end Rv64Verifier.Proofs.Walk
