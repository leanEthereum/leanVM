import Rv64Verifier.Proofs.Walk.Dr8

/-!
# `walk`: `tables()`, DEREF's pointer and target flushes (R8)

From `bytecode`'s return (`0x80002848`): `prod(fp, o1)`, `memory_cols(.., DEREF_CNT_PTR, &[ptr])`,
`prod(ptr, o2)`, `memory(.., DEREF_CNT_TARGET, store)`, to `0x800028c4` (`derefMem`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf FormVecOk formVecOf)

theorem storesAt {s u : MachineState} {lo hi : Nat} (h : SFh s u lo hi (storeFs s)) (hpre : WalkPre s) :
    Rv64Verifier.Layout.FormsOk u (s.getReg .x2 - 416) 3 ∧
      Rv64Verifier.Layout.formsAt u (s.getReg .x2 - 416) 3 = [store0, store1, store2] := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have q0 : s.getReg .x2 - 416 + BitVec.ofNat 64 (24 * 0) = s.getReg .x2 - 416 := by simp
  have q1 : s.getReg .x2 - 416 + BitVec.ofNat 64 (24 * 1) = s.getReg .x2 - 392 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have q2 : s.getReg .x2 - 416 + BitVec.ofNat 64 (24 * 2) = s.getReg .x2 - 368 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have s0 := h.sf (s.getReg .x2 - 416, store0) (by simp)
  have s1 := h.sf (s.getReg .x2 - 392, store1) (by simp)
  have s2 := h.sf (s.getReg .x2 - 368, store2) (by simp)
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · interval_cases i
    · rw [q0]; exact s0.ok
    · rw [q1]; exact s1.ok
    · rw [q2]; exact s2.ok
  · have r3 : List.range 3 = [0, 1, 2] := rfl
    simp only [Rv64Verifier.Layout.formsAt, r3, List.map_cons, List.map_nil]
    rw [q0, q1, q2, s0.val, s1.val, s2.val]

set_option maxRecDepth 8192 in
/-- `prod(fp, o1)`, `memory_cols(.., 11, &[ptr])`, `prod(ptr, o2)`, `memory(.., 12, store)`. -/
theorem derefMem (hP : Rv64Verifier.Layout.ProdSpec) (hK : Rv64Verifier.Layout.MemoryColsSpec)
    (hM : Rv64Verifier.Layout.MemorySpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W lo₂ H : Nat}
    {F : LayoutMirror.FlushesRust} {P : Word} (hpre : WalkPre s) (hWH : W ≤ H)
    (h : M8 OI s u A k R Q B Bb W (L4 s setT)) (fb : FB u (s.getReg .x2 - 344) F H)
    (hS : SFh s u lo₂ H (storeFs s)) (hH : H ≤ heapNext u) (r : DRg s u P) (hpc : u.pc = 0x80002848) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x800028c4 ∧ M8 OI s t A k R Q B Bb W (L4 s setT) ∧
      FB t (s.getReg .x2 - 344) ((F.memoryCols (LayoutMirror.prodRust 1 2 0) 11 [7]).memory
        (LayoutMirror.prodRust 7 3 0) 12 [store0, store1, store2]) H ∧ H ≤ heapNext t ∧ DRg s t P ∧
      t.getReg .x19 = 1 ∧ ∀ r ∈ ([.x21, .x22] : List Reg), t.getReg r = u.getReg r) ∨
      Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I := h.m.inv
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  have hFo : InSlot s (s.getReg .x2 - 344) 48 := inSlot_off hpre (by decide)
  -- `prod(fp, o1)` into `sp + 1240`
  obtain ⟨u₁, p₁, g₁⟩ := Sym.BlockSpec.reaches b80002848_spec hpc trivial
  have m₁ := b80002848_mem_same g₁
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have D₀ : DS OI s u₁ A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 344) F H (heapNext u₁) [] :=
    ⟨h.same hpre m₁ (b80002848_keeps g₁ .x2 (by decide)), fb.same hpre hFo I.heap m₁, hFo,
      SFs.nil _ _ _, le_refl _⟩
  have H₀ := hS.next hpre I (Rv64Verifier.Layout.DFrame.of_same m₁ _) hH hn₁.ge
  obtain ⟨t₁, q₁, ⟨pc₁, hp₁, D₁, H₁, mo₁, -⟩ | d⟩ := prodE hP (o := s.getReg .x2 - 1416) hpre D₀ H₀
    (by rw [hn₁]; exact hH) (inSlot_off hpre (by decide)) (l4_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) (fun e he ↦ absurd he List.not_mem_nil)
    (by forms_tac [hb1]) (b80002848_pc g₁) (by rw [b80002848_x10 g₁]; exact spAdd hpre sp (by decide))
  swap
  · exact ⟨t₁, p₁.trans q₁, Or.inr d⟩
  rw [b80002848_x11 g₁, b80002848_x12 g₁, b80002848_x13 g₁] at D₁
  have Q₁ := p₁.trans q₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := D₁.m.m.inv.sp
  have R₁ := (r.keeps (b80002848_keeps g₁)).pres hp₁
  have x19₁ : t₁.getReg .x19 = 1 := by rw [hp₁.reg .x19, b80002848_x19 g₁]
  have hH₁ : H ≤ heapNext t₁ := by rw [hn₁] at mo₁; omega
  -- `[sp + 2384] := ptr`, `memory_cols(fp * o1, 11, &[ptr])`
  obtain ⟨u₂, p₂, g₂⟩ := Sym.BlockSpec.reaches b80002864_spec
    (by rw [pc₁, returnAddress_eq, b80002848_x1 g₁]; decide) (by
      rv_eval [sp₁, R₁.x23]
      valid_access hval [hb1])
  have fr₂ := mfr23 hpre R₁.x23 (N := 240) (M := 272) (n := 8) (by decide)
    (b80002864_frame g₂ (by rw [R₁.x23]; addr_omega [hb1]))
  have hs₂ : InSlot s (s.getReg .x2 - 272) 8 := inSlot_off hpre (by decide)
  obtain ⟨D₂, hn₂, dd₂, -⟩ := D₁.blk hpre hs₂ (l4_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) _ (fun _ h ↦ h) (by forms_tac [hb1]) fr₂
    (b80002864_keeps g₂ .x2 (by decide))
  have H₂ := H₁.slot' hpre fr₂ hs₂ (by forms_tac [hb1]) D₁.m.m.inv.heap hH₁ hn₂.ge
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 2656 := D₂.m.m.inv.sp
  have hnK : Rv64Verifier.Layout.memoryColsStack ≤ 8736 := by decide
  have hFo6 : InSlot s (s.getReg .x2 - 344) (8 * 6) := hFo
  obtain ⟨v1, v2, v3⟩ := slotW hpre D₂.m.m.inv hFo6 hnK
  have sa₂ := D₂.sl.sf _ (List.mem_singleton_self _)
  obtain ⟨w1, w2, w3⟩ := slotPre hpre D₂.m.m.inv (o := s.getReg .x2 - 1416) (inSlot_off hpre (by decide)) hnK
  obtain ⟨c1, c2, c3⟩ := slotW (n := 1) hpre D₂.m.m.inv (o := s.getReg .x2 - 272) hs₂ hnK
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - 344 := by rw [b80002864_x10 g₂]; exact spAdd hpre sp₁ (by decide)
  have x11₂ : u₂.getReg .x11 = s.getReg .x2 - 1416 := by
    rw [b80002864_x11 g₂]; exact spAdd hpre sp₁ (by decide)
  have x13₂ : u₂.getReg .x13 = s.getReg .x2 - 272 := by rw [b80002864_x13 g₂]; exact spAdd hpre sp₁ (by decide)
  have e1 : (u₂.getReg .x14).toNat = 1 := by rw [b80002864_x14 g₂]; rfl
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
    len := by rw [e1]; decide
    columns := by rw [x13₂, e1]; exact c1
    columnsFree := by rw [x13₂, e1]; exact c2
    columnsStack := by rw [x13₂, e1]; exact c3 }
  obtain ⟨t₃, q₃, ⟨pc₃, hp₃, ⟨g₃, gv₃⟩⟩ | d⟩ := hK u₂ (b80002864_pc g₂) pre
  swap
  · exact ⟨t₃, Q₁.trans (p₂.trans q₃), Or.inr d⟩
  have col7 : Rv64Verifier.Layout.colsAt u₂ (s.getReg .x2 - 272) 1 = [7] := by
    show [(u₂.getMem (s.getReg .x2 - 272 + BitVec.ofNat 64 (8 * 0))).toNat] = [7]
    rw [show s.getReg .x2 - 272 + BitVec.ofNat 64 (8 * 0) = s.getReg .x2 - 272 by simp]
    have h' := b80002864_m_x23_240 g₂
    rv_eval [R₁.x23] at h'
    rw [h', R₁.x18]; rfl
  rw [x10₂] at g₃ gv₃
  rw [x11₂, b80002864_x12 g₂, x13₂, e1, D₂.fb.val, sa₂.val, col7] at gv₃
  have hHu₂ : H ≤ heapNext u₂ := by rw [hn₂]; exact hH₁
  obtain ⟨M₃, F₃⟩ := D₂.m.grow hpre D₂.fb hWH hHu₂ hFo (l4_off hpre (by decide)) g₃ hnK (hp₃.reg .x2)
  rw [gv₃] at F₃
  have H₃ := H₂.grow hpre D₂.m.m.inv g₃ D₂.fb (le_refl _) hFo (by forms_tac [hb1]) hnK hHu₂
  have Q₃ := Q₁.trans (p₂.trans q₃)
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := M₃.m.inv.sp
  have R₃ := (R₁.keeps (b80002864_keeps g₂)).pres hp₃
  have hH₃ : H ≤ heapNext t₃ := le_trans hHu₂ g₃.mono
  -- `prod(ptr, o2)` into `sp + 1240`
  obtain ⟨u₄, p₄, g₄⟩ := Sym.BlockSpec.reaches b8000288c_spec
    (by rw [pc₃, returnAddress_eq, b80002864_x1 g₂]; decide) trivial
  have m₄ := b8000288c_mem_same g₄
  have hn₄ : heapNext u₄ = heapNext t₃ := by simp only [heapNext, m₄]
  have D₄ : DS OI s u₄ A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 344)
      (F.memoryCols (LayoutMirror.prodRust 1 2 0) 11 [7]) H (heapNext u₄) [] :=
    ⟨M₃.same hpre m₄ (b8000288c_keeps g₄ .x2 (by decide)), F₃.same hpre hFo M₃.m.inv.heap m₄, hFo,
      SFs.nil _ _ _, le_refl _⟩
  have H₄ := H₃.next hpre M₃.m.inv (Rv64Verifier.Layout.DFrame.of_same m₄ _) hH₃ hn₄.ge
  obtain ⟨t₅, q₅, ⟨pc₅, hp₅, D₅, H₅, mo₅, -⟩ | d⟩ := prodE hP (o := s.getReg .x2 - 1416) hpre D₄ H₄
    (by rw [hn₄]; exact hH₃) (inSlot_off hpre (by decide)) (l4_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) (fun e he ↦ absurd he List.not_mem_nil)
    (by forms_tac [hb1]) (b8000288c_pc g₄) (by rw [b8000288c_x10 g₄]; exact spAdd hpre sp₃ (by decide))
  swap
  · exact ⟨t₅, Q₃.trans (p₄.trans q₅), Or.inr d⟩
  rw [b8000288c_x11 g₄, b8000288c_x12 g₄, b8000288c_x13 g₄] at D₅
  have Q₅ := Q₃.trans (p₄.trans q₅)
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 2656 := D₅.m.m.inv.sp
  have R₅ := (R₃.keeps (b8000288c_keeps g₄)).pres hp₅
  have hH₅ : H ≤ heapNext t₅ := by rw [hn₄] at mo₅; omega
  -- `memory(ptr * o2, 12, store)`
  obtain ⟨u₆, p₆, g₆⟩ := Sym.BlockSpec.reaches b800028a4_spec
    (by rw [pc₅, returnAddress_eq, b8000288c_x1 g₄]; decide) trivial
  have m₆ := b800028a4_mem_same g₆
  obtain ⟨D₆, hn₆⟩ := D₅.same hpre m₆ (b800028a4_keeps g₆ .x2 (by decide))
  have H₆ := H₅.next hpre D₅.m.m.inv (Rv64Verifier.Layout.DFrame.of_same m₆ _) hH₅ hn₆.ge
  have hnM : Rv64Verifier.Layout.memoryStack ≤ 8736 := by decide
  obtain ⟨y1, y2, y3⟩ := slotW hpre D₆.m.m.inv hFo6 hnM
  have sa₆ := D₆.sl.sf _ (List.mem_singleton_self _)
  obtain ⟨z1, z2, z3⟩ := slotPre hpre D₆.m.m.inv (o := s.getReg .x2 - 1416) (inSlot_off hpre (by decide)) hnM
  obtain ⟨d1, d2, d3⟩ := slotW (n := 9) hpre D₆.m.m.inv (o := s.getReg .x2 - 416) (inSlot_off hpre (by decide))
    hnM
  have SA := storesAt H₆ hpre
  have x10₆ : u₆.getReg .x10 = s.getReg .x2 - 344 := by rw [b800028a4_x10 g₆]; exact spAdd hpre sp₅ (by decide)
  have x11₆ : u₆.getReg .x11 = s.getReg .x2 - 1416 := by
    rw [b800028a4_x11 g₆]; exact spAdd hpre sp₅ (by decide)
  have x13₆ : u₆.getReg .x13 = s.getReg .x2 - 416 := by rw [b800028a4_x13 g₆]; exact spAdd hpre sp₅ (by decide)
  have preM : Rv64Verifier.Layout.MemoryPre u₆ := {
    heap := D₆.m.m.inv.heap
    stack := stk_sub hpre D₆.m.m.inv hnM (by decide)
    self := by rw [x10₆]; exact y1
    ok := by rw [x10₆]; exact D₆.fb.ok
    selfFree := by rw [x10₆]; exact y2
    selfStack := by rw [x10₆]; exact y3
    rodata := D₆.m.m.inv.rodata hpre
    address := by rw [x11₆]; exact z1
    addressOk := by rw [x11₆]; exact sa₆.ok
    addressFree := by rw [x11₆]; exact z2
    addressStack := by rw [x11₆]; exact z3
    values := by rw [x13₆]; exact d1
    valuesOk := by rw [x13₆]; exact SA.1
    valuesFree := by rw [x13₆]; exact d2
    valuesStack := by rw [x13₆]; exact d3 }
  obtain ⟨t₇, q₇, ⟨pc₇, hp₇, ⟨g₇, gv₇⟩⟩ | d⟩ := hM u₆ (b800028a4_pc g₆) preM
  swap
  · exact ⟨t₇, Q₅.trans (p₆.trans q₇), Or.inr d⟩
  rw [x10₆] at g₇ gv₇
  rw [x11₆, b800028a4_x12 g₆, x13₆, D₆.fb.val, sa₆.val, SA.2] at gv₇
  have hHu₆ : H ≤ heapNext u₆ := by rw [hn₆]; exact hH₅
  obtain ⟨M₇, F₇⟩ := D₆.m.grow hpre D₆.fb hWH hHu₆ hFo (l4_off hpre (by decide)) g₇ hnM (hp₇.reg .x2)
  rw [gv₇] at F₇
  refine ⟨t₇, Q₅.trans (p₆.trans q₇), Or.inl ⟨by rw [pc₇, returnAddress_eq, b800028a4_x1 g₆]; decide,
    M₇, F₇, le_trans hHu₆ g₇.mono, (R₅.keeps (b800028a4_keeps g₆)).pres hp₇, ?_, ?_⟩⟩
  · rw [hp₇.reg .x19, b800028a4_keeps g₆ .x19 (by decide), hp₅.reg .x19, b8000288c_keeps g₄ .x19 (by decide),
      hp₃.reg .x19, b80002864_keeps g₂ .x19 (by decide)]; exact x19₁
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hp₇.reg .x21, b800028a4_keeps g₆ .x21 (by decide), hp₅.reg .x21, b8000288c_keeps g₄ .x21 (by decide),
        hp₃.reg .x21, b80002864_keeps g₂ .x21 (by decide), hp₁.reg .x21, b80002848_keeps g₁ .x21 (by decide)]
    · rw [hp₇.reg .x22, b800028a4_keeps g₆ .x22 (by decide), hp₅.reg .x22, b8000288c_keeps g₄ .x22 (by decide),
        hp₃.reg .x22, b80002864_keeps g₂ .x22 (by decide), hp₁.reg .x22, b80002848_keeps g₁ .x22 (by decide)]

end Rv64Verifier.Proofs.Walk
