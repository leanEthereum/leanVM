import Rv64Verifier.Proofs.Walk.R8F

/-!
# `walk`: `tables()`, SET's tail (R8)

`bytecode` on the operands (`setBc`); `prod(fp, o)`, `memory_cols(.., SET_CNT, k)` (the columns in
`.rodata`), the `Flushes` moved to `sp + 2144`, `vec![ZERO; 8]` into `sp + 1168`, the `Flushes` moved
to `sp + 1192`: the SET `Table` at `sp + 1168` joins the finished ones, to DEREF's first `col`
(`setTail`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf FormVecOk formVecOf)

set_option maxRecDepth 8192 in
/-- `bytecode(SET_CNT_BC, OP_SET, operands)` on the `Flushes` at `sp + 1728`. -/
theorem setBc (hBC : Rv64Verifier.Layout.BytecodeSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {F : LayoutMirror.FlushesRust} {lo : Nat} {P : Word} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W (L3 s)) (fb : FB u (s.getReg .x2 - 928) F lo) (hlo : W ≤ lo)
    (hlo' : lo ≤ heapNext u) (hv : FormVecOk u (s.getReg .x2 - 224))
    (hvv : formVecOf u (s.getReg .x2 - 224) = setOps) (vp : vecPtr u (s.getReg .x2 - 224) = P)
    (vl : vecLen u (s.getReg .x2 - 224) = 5) (pnx : P.toNat + 120 ≤ heapNext u)
    (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = 7) (x12 : u.getReg .x12 = 2)
    (x13 : u.getReg .x13 = s.getReg .x2 - 224) (hpc : u.pc = 0x80004b94) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      M8 OI s t A k R Q B Bb W (L3 s) ∧ FB t (s.getReg .x2 - 928) (F.bytecode 0 7 2 setOps) lo ∧
      heapNext u ≤ heapNext t) ∨
      Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hn : Rv64Verifier.Layout.bytecodeStack ≤ 8736 := by decide
  have hFo : InSlot s (s.getReg .x2 - 928) (8 * 6) := by simp only [InSlot]; addr_omega [hb1, hb3]
  obtain ⟨v1, v2, v3⟩ := slotW hpre h.m.inv hFo hn
  obtain ⟨w1, w2, w3⟩ := slotPre hpre h.m.inv (o := s.getReg .x2 - 224)
    (by simp only [InSlot]; addr_omega [hb1, hb3]) hn
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
  obtain ⟨M, Fb⟩ := h.grow hpre fb hlo hlo' hFo (l3_apart hpre (by addr_omega [hb1])) g hn (hp.reg .x2)
  rw [gv] at Fb
  exact ⟨t, hr, Or.inl ⟨hpct, hp, M, Fb, g.mono⟩⟩

/-- A block that writes only the frame slot `o`, apart from the finished tables, keeps `M8` and
`NEXT`. -/
theorem M8.slotStep {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o : Word} {n : Nat} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W L) (ho : InSlot s o n)
    (hL : ∀ e ∈ L, ∀ a, Within a o n → ¬ Within a e.1 72)
    (fr : Rv64Verifier.Layout.DFrame u v fun x ↦ Within x o n) (sp : v.getReg .x2 = u.getReg .x2) :
    M8 OI s v A k R Q B Bb W L ∧ heapNext v = heapNext u := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, o3⟩ := ho
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]
    rw [fr nextAddr (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1, o1, o2])
      (by decide)]
  have hW := slotOk hpre h ⟨o1, o2, o3⟩ hL
  exact ⟨h.step hpre fr (fun a ha ↦ (hW a ha).1.mono hn.ge) (fun a ha ↦ (hW a ha).2)
    ⟨hn ▸ h.m.inv.heap.lo, hn ▸ h.m.inv.heap.hi⟩ hn.ge sp, hn⟩

theorem cols_set {u : MachineState} (h : RodataOk u) :
    Rv64Verifier.Layout.colsAt u 0xa0000ee8 3 = [3, 4, 5] := by
  have h0 : u.getMem 0xa0000ee8 = 3 := h.word
  have h1 : u.getMem 0xa0000ef0 = 4 := h.word
  have h2 : u.getMem 0xa0000ef8 = 5 := h.word
  show [(u.getMem (0xa0000ee8 + BitVec.ofNat 64 (8 * 0))).toNat,
    (u.getMem (0xa0000ee8 + BitVec.ofNat 64 (8 * 1))).toNat,
    (u.getMem (0xa0000ee8 + BitVec.ofNat 64 (8 * 2))).toNat] = _
  rw [show (0xa0000ee8 : Word) + BitVec.ofNat 64 (8 * 0) = 0xa0000ee8 by decide,
    show (0xa0000ee8 : Word) + BitVec.ofNat 64 (8 * 1) = 0xa0000ef0 by decide,
    show (0xa0000ee8 : Word) + BitVec.ofNat 64 (8 * 2) = 0xa0000ef8 by decide, h0, h1, h2]
  rfl

/-- The finished tables and SET's. -/
abbrev L4 (s : MachineState) (t : LayoutMirror.TableRust) : List (Word × LayoutMirror.TableRust) :=
  L3 s ++ [(s.getReg .x2 - 1488, t)]

set_option maxRecDepth 8192 in
/-- From `bytecode`'s return: `prod(fp, o)` into `sp + 2144`, `memory_cols`, the `Flushes` moved to
`sp + 2144`, `vec![ZERO; 8]` into `sp + 1168`, the `Flushes` moved to `sp + 1192`, to DEREF's first
`col` into `sp + 2432`. -/
theorem setTail (hP : Rv64Verifier.Layout.ProdSpec) (hK : Rv64Verifier.Layout.MemoryColsSpec)
    (hFE : MultilinearContracts.FromElemSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {F : LayoutMirror.FlushesRust} {lo : Nat} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W (L3 s)) (fb : FB u (s.getReg .x2 - 928) F lo) (hlo : W ≤ lo)
    (hlo' : lo ≤ heapNext u) (r8 : R8 u) (y23 : u.getReg .x23 = s.getReg .x2 - 512)
    (hpc : u.pc = 0x80002238) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ M8 OI s t A k R Q B Bb (heapNext t)
      (L4 s ⟨2, List.replicate 8 0, F.memoryCols (LayoutMirror.prodRust 1 2 0) 6 [3, 4, 5]⟩) ∧
      R8 t ∧ t.getReg .x25 = 8 ∧ t.getReg .x10 = s.getReg .x2 - 224 ∧ t.getReg .x11 = 8 ∧
      t.getReg .x12 = 0 ∧ t.getReg .x1 = 0x80002308 ∧
      ∀ r ∈ ([.x18, .x23, .x26, .x27] : List Reg), t.getReg r = u.getReg r) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hFo : InSlot s (s.getReg .x2 - 928) 48 := by simp only [InSlot]; addr_omega [hb1, hb3]
  have sp₀ : u.getReg .x2 = s.getReg .x2 - 2656 := h.m.inv.sp
  -- `prod(fp, o)` into `sp + 2144`
  obtain ⟨u₁, r₁, g₁⟩ := Sym.BlockSpec.reaches b80002238_spec hpc trivial
  have k₁ := b80002238_keeps g₁
  have m₁ := b80002238_mem_same g₁
  have M₁ := h.same hpre m₁ (k₁ .x2 (by decide))
  have F₁ := fb.same hpre hFo h.m.inv.heap m₁
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  obtain ⟨t₂, r₂, ⟨pc₂, hp₂, M₂, F₂, hN₂, S₂, -⟩ | d⟩ := prodSlot hP (o := s.getReg .x2 - 512) hpre M₁ F₁
    hFo (SFs.nil s u₁ (heapNext u₁)) (le_refl _) (by simp only [InSlot]; addr_omega [hb1, hb3])
    (l3_apart hpre (by addr_omega [hb1])) (fun a ha hw ↦ by simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
    (fun e he ↦ absurd he List.not_mem_nil) (b80002238_pc g₁)
    (by rw [b80002238_x10 g₁]; exact spAdd hpre sp₀ (N := 2144) (M := 512) (by decide))
  swap
  · exact ⟨t₂, r₁.trans r₂, Or.inr d⟩
  rw [b80002238_x11 g₁, b80002238_x12 g₁, b80002238_x13 g₁] at S₂
  have sf := S₂.sf _ (List.mem_singleton_self _)
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := M₂.m.inv.sp
  -- `memory_cols(fp * o, SET_CNT, k)`
  obtain ⟨u₃, r₃, g₃⟩ := Sym.BlockSpec.reaches b80002254_spec
    (by rw [pc₂, returnAddress_eq, b80002238_x1 g₁]; decide) trivial
  have k₃ := b80002254_keeps g₃
  have m₃ := b80002254_mem_same g₃
  have hn₃ : heapNext u₃ = heapNext t₂ := by simp only [heapNext, m₃]
  have M₃ := M₂.same hpre m₃ (k₃ .x2 (by decide))
  have F₃ := F₂.same hpre hFo M₂.m.inv.heap m₃
  have sf₃ : SF u₃ (s.getReg .x2 - 512) (LayoutMirror.prodRust 1 2 0) (heapNext u₁) (heapNext u₃) := by
    exact (S₂.same hpre m₃ M₂.m.inv.heap).sf _ (List.mem_singleton_self _)
  have hnK : Rv64Verifier.Layout.memoryColsStack ≤ 8736 := by decide
  have hFo6 : InSlot s (s.getReg .x2 - 928) (8 * 6) := hFo
  obtain ⟨v1, v2, v3⟩ := slotW hpre M₃.m.inv hFo6 hnK
  obtain ⟨w1, w2, w3⟩ := slotPre hpre M₃.m.inv (o := s.getReg .x2 - 512)
    (by simp only [InSlot]; addr_omega [hb1, hb3]) hnK
  have x10₃ : u₃.getReg .x10 = s.getReg .x2 - 928 := by
    rw [b80002254_x10 g₃]; exact spAdd hpre sp₂ (N := 1728) (M := 928) (by decide)
  have x11₃ : u₃.getReg .x11 = s.getReg .x2 - 512 := by
    rw [b80002254_x11 g₃]; exact spAdd hpre sp₂ (N := 2144) (M := 512) (by decide)
  have pre : Rv64Verifier.Layout.MemoryColsPre u₃ := {
    heap := M₃.m.inv.heap
    stack := stk_sub hpre M₃.m.inv hnK (by decide)
    self := by rw [x10₃]; exact v1
    ok := by rw [x10₃]; exact F₃.ok
    selfFree := by rw [x10₃]; exact v2
    selfStack := by rw [x10₃]; exact v3
    rodata := M₃.m.inv.rodata hpre
    address := by rw [x11₃]; exact w1
    addressOk := by rw [x11₃]; exact sf₃.ok
    addressFree := by rw [x11₃]; exact w2
    addressStack := by rw [x11₃]; exact w3
    len := by rw [b80002254_x14 g₃]; decide
    columns := by
      rw [b80002254_x13 g₃, b80002254_x14 g₃]
      exact Rv64Verifier.Layout.validMemRange_of (by decide) (Or.inr ⟨by decide, by decide⟩)
    columnsFree := by
      rw [b80002254_x13 g₃, b80002254_x14 g₃]; exact ⟨Or.inr (by simp only [heapEnd]; decide), by addr_omega []⟩
    columnsStack := by
      rw [b80002254_x13 g₃, b80002254_x14 g₃, stackLo_callee M₃.m.inv]; addr_omega [hb1, hnK] }
  obtain ⟨t₄, r₄, ⟨pc₄, hp₄, ⟨g₄, gv₄⟩⟩ | d⟩ := hK u₃ (b80002254_pc g₃) pre
  swap
  · exact ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inr d⟩
  rw [x10₃] at g₄ gv₄
  rw [x11₃, b80002254_x12 g₃, b80002254_x13 g₃, b80002254_x14 g₃, F₃.val, sf₃.val,
    show (3 : Word).toNat = 3 from rfl, cols_set (M₃.m.inv.rodata hpre)] at gv₄
  obtain ⟨M₄, F₄⟩ := M₃.grow hpre F₃ hlo (by omega) hFo (l3_apart hpre (by addr_omega [hb1])) g₄ hnK
    (hp₄.reg .x2)
  rw [gv₄] at F₄
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 2656 := M₄.m.inv.sp
  have y23₄ : t₄.getReg .x23 = s.getReg .x2 - 512 := by
    rw [hp₄.reg .x23, k₃ .x23 (by decide), hp₂.reg .x23, k₁ .x23 (by decide)]; exact y23
  -- the `Flushes` to `sp + 2144`
  obtain ⟨u₅, r₅, g₅⟩ := Sym.BlockSpec.reaches b80002278_spec
    (by rw [pc₄, returnAddress_eq, b80002254_x1 g₃]; decide) (by
      rv_eval [sp₄, y23₄]
      and_intros <;> valid_access hval [hb1])
  have k₅ := b80002278_keeps g₅
  have fr₅ : Rv64Verifier.Layout.DFrame t₄ u₅ fun x ↦ Within x (s.getReg .x2 - 512) 48 :=
    Expect.ldframe g₅ (by
      rv_eval [sp₄, y23₄]
      simp only [Within]
      and_intros <;> addr_omega [hb1])
  obtain ⟨M₅, hn₅⟩ := M₄.slotStep hpre (by simp only [InSlot]; addr_omega [hb1, hb3])
    (l3_apart hpre (by addr_omega [hb1])) fr₅ (k₅ .x2 (by decide))
  have hu₄ := M₄.m.inv.heap.hi
  simp only [heapEnd] at hu₄
  have F₅ := F₄.move (o := s.getReg .x2 - 512) fr₅
    (by have := b80002278_m_x23_0 g₅; rv_eval [sp₄, y23₄] at this ⊢; exact this)
    (by have := b80002278_m_x23_8 g₅; rv_eval [sp₄, y23₄] at this ⊢; exact this)
    (by have := b80002278_m_x23_16 g₅; rv_eval [sp₄, y23₄] at this ⊢; exact this)
    (by have := b80002278_m_x23_24 g₅; rv_eval [sp₄, y23₄] at this ⊢; exact this)
    (by have := b80002278_m_x23_32 g₅; rv_eval [sp₄, y23₄] at this ⊢; exact this)
    (by have := b80002278_m_x23_40 g₅; rv_eval [sp₄, y23₄] at this ⊢; exact this)
    (fun x _ h2 hw ↦ by simp only [Within] at hw; addr_omega [hw, h2, hb1, hu₄])
    (by addr_omega [hb1]) M₄.m.inv.heap hn₅.ge
  have sp₅ : u₅.getReg .x2 = s.getReg .x2 - 2656 := M₅.m.inv.sp
  have x24₅ : u₅.getReg .x24 = 0xa0000068 := by
    rw [k₅ .x24 (by decide), hp₄.reg .x24, k₃ .x24 (by decide), hp₂.reg .x24, k₁ .x24 (by decide)]
    exact r8.x24
  -- `vec![ZERO; 8]` into `sp + 1168`
  obtain ⟨t₆, r₆, ⟨pc₆, hp₆, mo₆, M₆, F₆, P', Z₆⟩ | d⟩ := padCall hFE (o := s.getReg .x2 - 1488) hpre M₅ F₅
    (by simp only [InSlot]; addr_omega [hb1, hb3]) (by simp only [InSlot]; addr_omega [hb1, hb3])
    (fun a ha hw ↦ by simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
    (l3_apart hpre (by addr_omega [hb1])) (b80002278_pc g₅)
    (by rw [b80002278_x10 g₅]; exact spAdd hpre sp₄ (N := 1168) (M := 1488) (by decide))
    (by rw [b80002278_x11 g₅]; rw [k₅ .x24 (by decide)] at x24₅; exact x24₅)
    (by rw [b80002278_x12 g₅]; decide)
  swap
  · exact ⟨t₆, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans r₆)))), Or.inr d⟩
  rw [b80002278_x12 g₅] at Z₆
  have sp₆ : t₆.getReg .x2 = s.getReg .x2 - 2656 := M₆.m.inv.sp
  have y23₆ : t₆.getReg .x23 = s.getReg .x2 - 512 := by
    rw [hp₆.reg .x23, k₅ .x23 (by decide)]; exact y23₄
  -- the `Flushes` to `sp + 1192`
  obtain ⟨u₇, r₇, g₇⟩ := Sym.BlockSpec.reaches b800022c0_spec
    (by rw [pc₆, returnAddress_eq, b80002278_x1 g₅]; decide) (by
      rv_eval [sp₆, y23₆]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | addr_omega [hb1])
  have k₇ := b800022c0_keeps g₇
  have fr₇ : Rv64Verifier.Layout.DFrame t₆ u₇ fun x ↦ Within x (s.getReg .x2 - 1464) 48 :=
    Expect.ldframe g₇ (by
      rv_eval [sp₆, y23₆]
      simp only [Within]
      and_intros <;> addr_omega [hb1])
  obtain ⟨M₇, hn₇⟩ := M₆.slotStep hpre (by simp only [InSlot]; addr_omega [hb1, hb3])
    (l3_apart hpre (by addr_omega [hb1])) fr₇ (k₇ .x2 (by decide))
  have hu₆ := M₆.m.inv.heap.hi
  simp only [heapEnd] at hu₆
  have F₇ := F₆.move (o := s.getReg .x2 - 1488 + 24) fr₇
    (by have := b800022c0_m_x2_1192 g₇; rv_eval [sp₆, y23₆] at this ⊢; exact this)
    (by have := b800022c0_m_x2_1200 g₇; rv_eval [sp₆, y23₆] at this ⊢; exact this)
    (by have := b800022c0_m_x2_1208 g₇; rv_eval [sp₆, y23₆] at this ⊢; exact this)
    (by have := b800022c0_m_x2_1216 g₇; rv_eval [sp₆, y23₆] at this ⊢; exact this)
    (by have := b800022c0_m_x2_1224 g₇; rv_eval [sp₆, y23₆] at this ⊢; exact this)
    (by have := b800022c0_m_x2_1232 g₇; rv_eval [sp₆, y23₆] at this ⊢; exact this)
    (fun x _ h2 hw ↦ by simp only [Within] at hw; addr_omega [hw, h2, hb1, hu₆])
    (by addr_omega [hb1]) M₆.m.inv.heap hn₇.ge
  have Z₇ := Z₆.frame fr₇ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
    (by addr_omega [hb1]) (fun x h1 h2 hw ↦ by
      have := Z₆.buf; simp only [Within] at hw; addr_omega [hw, h1, h2, hb1, hu₆, this]) hn₇.ge
    (by have := Z₆.buf; omega)
  have T := tableOf (op := 2) Z₇ F₇ (by decide)
  have hW₅ : W ≤ heapNext u₅ := M₅.bb.2.2.2
  have M₈ := M₇.push (o := s.getReg .x2 - 1488) (t := ⟨2, List.replicate 8 0,
      F.memoryCols (LayoutMirror.prodRust 1 2 0) 6 [3, 4, 5]⟩) (by simp only [InSlot]; addr_omega [hb1, hb3])
    T.1 (fun x hx ↦ by have := T.2 x hx; omega)
  refine ⟨u₇, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans (r₆.trans r₇))))),
    Or.inl ⟨b800022c0_pc g₇, M₈, ⟨?_, ?_⟩, ?_, ?_, b800022c0_x11 g₇, b800022c0_x12 g₇, b800022c0_x1 g₇, ?_⟩⟩
  · rw [k₇ .x8 (by decide), hp₆.reg .x8, k₅ .x8 (by decide), hp₄.reg .x8, k₃ .x8 (by decide),
      hp₂.reg .x8, k₁ .x8 (by decide)]; exact r8.x8
  · rw [k₇ .x24 (by decide), hp₆.reg .x24]; exact x24₅
  · rw [k₇ .x25 (by decide), hp₆.reg .x25, b80002278_x25 g₅]
  · rw [b800022c0_x10 g₇]; exact spAdd hpre sp₆ (N := 2432) (M := 224) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [k₇ .x18 (by decide), hp₆.reg .x18, k₅ .x18 (by decide), hp₄.reg .x18, k₃ .x18 (by decide),
        hp₂.reg .x18, k₁ .x18 (by decide)]
    · rw [k₇ .x23 (by decide), hp₆.reg .x23, k₅ .x23 (by decide), hp₄.reg .x23, k₃ .x23 (by decide),
        hp₂.reg .x23, k₁ .x23 (by decide)]
    · rw [k₇ .x26 (by decide), hp₆.reg .x26, k₅ .x26 (by decide), hp₄.reg .x26, k₃ .x26 (by decide),
        hp₂.reg .x26, k₁ .x26 (by decide)]
    · rw [k₇ .x27 (by decide), hp₆.reg .x27, k₅ .x27 (by decide), hp₄.reg .x27, k₃ .x27 (by decide),
        hp₂.reg .x27, k₁ .x27 (by decide)]

end Rv64Verifier.Proofs.Walk
