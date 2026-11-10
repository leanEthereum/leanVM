import Rv64Verifier.Proofs.Walk.R8A

/-!
# `walk`: `tables()`, XOR and MUL (R8, first part)

From `0x80002024`: `flushes_arith(XOR, false)` into `sp + 1728`, `vec![ZERO; 15]` into `sp + 1024`,
the `Flushes` moved to `sp + 1048` (the XOR `Table`, `xorStage`); the same for MUL at `sp + 1096`,
then an empty `Flushes` at `sp + 1728` for SET (`mulStage`), to `state_step`'s call.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep)

/-- A doubleword a block copied within the frame. -/
theorem hdr {s u v : MachineState} (hpre : WalkPre s) (sp : u.getReg .x2 = s.getReg .x2 - 2656)
    {N N' M M' : Word} (hN : N.toNat + M.toNat = 2656) (hN' : N'.toNat + M'.toNat = 2656)
    (h : v.getMem (u.getReg .x2 + N) = u.getMem (u.getReg .x2 + N')) {a a' : Word}
    (ha : a = s.getReg .x2 - M) (ha' : a' = s.getReg .x2 - M') : v.getMem a = u.getMem a' := by
  subst ha ha'; rw [← spAdd hpre sp hN, ← spAdd hpre sp hN']; exact h

/-- A table made of a zero padding row at `o` and a `Flushes` at `o + 24`. -/
theorem tableOf {u : MachineState} {o P : Word} {n lo₁ lo₂ op : Nat} {F : LayoutMirror.FlushesRust}
    (z : ZVec u o n P lo₁) (f : FB u (o + 24) F lo₂) (hn : n < 2 ^ 32) :
    TableAt u o ⟨op, List.replicate n 0, F⟩ ∧ ∀ x, tableDeep u o x → min lo₁ lo₂ ≤ x.toNat := by
  have hl := z.len
  have hb := z.buf
  have hn' : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨⟨z.vec, ?_, f.ok, f.val⟩, fun x hx ↦ ?_⟩
  · simp only [vecEs, z.ptr, hl, hn']
    apply List.ext_getElem (by simp [eListAt_length])
    intro i h1 _
    rw [eListAt_length] at h1
    rw [eListAt_getElem, z.zero i h1, List.getElem_replicate]
  · rcases hx with hx | hx
    · simp only [Within, z.ptr] at hx; omega
    · have := f.deep x hx; omega

/-- The XOR and MUL `Table`s. -/
def xorT : LayoutMirror.TableRust := ⟨0, List.replicate 15 0, LayoutMirror.flushesArithRust 0 false⟩
def mulT : LayoutMirror.TableRust := ⟨1, List.replicate 15 0, LayoutMirror.flushesArithRust 1 true⟩

theorem tablesRust_zero : LayoutMirror.tablesRust[0]? = some xorT := rfl
theorem tablesRust_one : LayoutMirror.tablesRust[1]? = some mulT := rfl

/-- The registers `tables()` keeps past the KECCAK table: `s0 = 8`, `s8 = &ZERO`. -/
structure R8 (u : MachineState) : Prop where
  x8 : u.getReg .x8 = 8
  x24 : u.getReg .x24 = 0xa0000068

set_option maxRecDepth 8192 in
/-- XOR: `flushes_arith(0, false)`, `vec![ZERO; 15]` into `sp + 1024`, the `Flushes` to `sp + 1048`,
then the call of `flushes_arith(1, true)`. -/
theorem xorStage (hFA : Rv64Verifier.Layout.FlushesArithSpec) (hFE : MultilinearContracts.FromElemSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W [(s.getReg .x2 - 1704, kTable)]) (x8 : u.getReg .x8 = 8)
    (hpc : u.pc = 0x80002024) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x8000547c ∧ M8 OI s t A k R Q B Bb (heapNext t)
      [(s.getReg .x2 - 1704, kTable), (s.getReg .x2 - 1632, xorT)] ∧ R8 t ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = 1 ∧ t.getReg .x12 = 1 ∧
      t.getReg .x1 = 0x80002098) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨u₁, r₁, g₁⟩ := Sym.BlockSpec.reaches b80002024_spec hpc trivial
  have k₁ := b80002024_keeps g₁
  have m₁ := b80002024_mem_same g₁
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have M₁ := h.step hpre (Rv64Verifier.Layout.DFrame.of_same m₁ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (fun _ h ↦ h.elim) ⟨hn₁ ▸ h.m.inv.heap.lo, hn₁ ▸ h.m.inv.heap.hi⟩ hn₁.ge (k₁ .x2 (by decide))
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := M₁.m.inv.sp
  obtain ⟨t₁, r₂, ⟨pc₂, hp₂, mo₂, M₂, F₂⟩ | d⟩ := arithCall hFA (L := [(s.getReg .x2 - 1704, kTable)]) hpre M₁ (fun e he a ha hw ↦ by
      simp only [List.mem_singleton] at he; subst he; simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
    (b80002024_pc g₁) (by rw [b80002024_x10 g₁]; exact spAdd hpre h.m.inv.sp (N := 1728) (M := 928) (by decide))
  swap
  · exact ⟨t₁, r₁.trans r₂, Or.inr d⟩
  rw [b80002024_x11 g₁, b80002024_x12 g₁] at F₂
  have sp₂ : t₁.getReg .x2 = s.getReg .x2 - 2656 := M₂.m.inv.sp
  obtain ⟨u₃, r₃, g₃⟩ := Sym.BlockSpec.reaches b80002038_spec
    (by rw [pc₂, returnAddress_eq, b80002024_x1 g₁]; decide) trivial
  have k₃ := b80002038_keeps g₃
  have m₃ := b80002038_mem_same g₃
  have hn₃ : heapNext u₃ = heapNext t₁ := by simp only [heapNext, m₃]
  have fr₃ := Rv64Verifier.Layout.DFrame.of_same m₃ (fun _ ↦ False)
  have M₃ := M₂.step hpre fr₃ (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) ⟨hn₃ ▸ M₂.m.inv.heap.lo,
    hn₃ ▸ M₂.m.inv.heap.hi⟩ hn₃.ge (k₃ .x2 (by decide))
  have F₃ := (F₂.frame fr₃ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) M₂.m.inv.heap hn₃.ge).1
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 2656 := M₃.m.inv.sp
  obtain ⟨t₂, r₄, ⟨pc₄, hp₄, mo₄, M₄, F₄, P, Z₄⟩ | d⟩ := padCall hFE (o := s.getReg .x2 - 1632) (L := [(s.getReg .x2 - 1704, kTable)]) hpre M₃ F₃
    (by simp only [InSlot]; addr_omega [hb1, hb3]) (by simp only [InSlot]; addr_omega [hb1, hb3])
    (fun a ha hw ↦ by simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
    (fun e he a ha hw ↦ by
      simp only [List.mem_singleton] at he; subst he; simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
    (b80002038_pc g₃) (by rw [b80002038_x10 g₃]; exact spAdd hpre sp₂ (N := 1024) (M := 1632) (by decide))
    (b80002038_x11 g₃) (by rw [b80002038_x12 g₃]; decide)
  swap
  · exact ⟨t₂, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inr d⟩
  rw [b80002038_x12 g₃] at Z₄
  have sp₄ : t₂.getReg .x2 = s.getReg .x2 - 2656 := M₄.m.inv.sp
  obtain ⟨u₅, r₅, g₅⟩ := Sym.BlockSpec.reaches b80002054_spec
    (by rw [pc₄, returnAddress_eq, b80002038_x1 g₃]; decide) (by
      rv_eval [sp₄]
      and_intros <;> valid_access hval [hb1])
  have k₅ := b80002054_keeps g₅
  have fr₅ : Rv64Verifier.Layout.DFrame t₂ u₅ fun x ↦ Within x (s.getReg .x2 - 1608) 48 :=
    Expect.ldframe g₅ (by
      rv_eval [sp₄]
      simp only [Within]
      and_intros <;> addr_omega [hb1])
  have hn₅ : heapNext u₅ = heapNext t₂ := by
    simp only [heapNext]; rw [fr₅ _ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
      (by decide)]
  have hu₄ := M₄.m.inv.heap.hi
  simp only [heapEnd] at hu₄
  have M₅ := M₄.step hpre fr₅ (fun x hx ↦ Or.inl (by simp only [Within] at hx ⊢; addr_omega [hx, hb1]))
    (fun x hx ↦ by
      simp only [M8W, Within] at hx ⊢
      refine ⟨by have := M₄.bb; addr_omega [hx, hb1, hu₄, this], ?_, ?_, ?_, ?_⟩
      · addr_omega [hx, hb1]
      · addr_omega [hx, hb1]
      · addr_omega [hx, hb1]
      · intro e he; simp only [List.mem_singleton] at he; subst he; addr_omega [hx, hb1])
    ⟨hn₅ ▸ M₄.m.inv.heap.lo, hn₅ ▸ M₄.m.inv.heap.hi⟩ hn₅.ge (k₅ .x2 (by decide))
  have e24 : s.getReg .x2 - 1632 + 24 = s.getReg .x2 - 1608 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have nd : ∀ x, heapNext u₁ ≤ x.toNat → x.toNat < heapNext t₂ → ¬ Within x (s.getReg .x2 - 1608) 48 :=
    fun x _ h2 hw ↦ by simp only [Within] at hw; addr_omega [hw, h2, hb1, hu₄]
  have F₅ : FB u₅ (s.getReg .x2 - 1632 + 24) (LayoutMirror.flushesArithRust 0 false) (heapNext u₁) := by
    rw [e24]
    refine F₄.move fr₅ (hdr hpre sp₄ (N := 1048) (N' := 1728) (M := 1608) (M' := 928) (by decide) (by decide)
        (b80002054_m_x2_1048 g₅) rfl rfl)
      (hdr hpre sp₄ (N := 1056) (N' := 1736) (M := 1600) (M' := 920) (by decide) (by decide)
        (b80002054_m_x2_1056 g₅) (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]) (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))
      (hdr hpre sp₄ (N := 1064) (N' := 1744) (M := 1592) (M' := 912) (by decide) (by decide)
        (b80002054_m_x2_1064 g₅) (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]) (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))
      (hdr hpre sp₄ (N := 1072) (N' := 1752) (M := 1584) (M' := 904) (by decide) (by decide)
        (b80002054_m_x2_1072 g₅) (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]) (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))
      (hdr hpre sp₄ (N := 1080) (N' := 1760) (M := 1576) (M' := 896) (by decide) (by decide)
        (b80002054_m_x2_1080 g₅) (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
        (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))
      (hdr hpre sp₄ (N := 1088) (N' := 1768) (M := 1568) (M' := 888) (by decide) (by decide)
        (b80002054_m_x2_1088 g₅) (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
        (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))
      nd (by addr_omega [hb1]) M₄.m.inv.heap hn₅.ge
  have Z₅ := Z₄.frame fr₅ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
    (by addr_omega [hb1]) (fun x h1 h2 hw ↦ by
      have := Z₄.buf; simp only [Within] at hw; addr_omega [hw, h1, h2, hb1, hu₄, this]) hn₅.ge
    (by have := Z₄.buf; omega)
  have T := tableOf (op := 0) Z₅ F₅ (by norm_num)
  have hW₁ : W ≤ heapNext u₁ := M₁.bb.2.2.2
  have hu₁₃ : heapNext u₁ ≤ heapNext u₃ := by rw [hn₃]; exact mo₂
  have M₆ := M₅.push (o := s.getReg .x2 - 1632) (t := xorT) (by simp only [InSlot]; addr_omega [hb1, hb3])
    T.1 (fun x hx ↦ by have := T.2 x hx; omega)
  refine ⟨u₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inl ⟨b80002054_pc g₅, M₆,
    ⟨?_, ?_⟩, ?_, b80002054_x11 g₅, b80002054_x12 g₅, b80002054_x1 g₅⟩⟩
  · rw [k₅ .x8 (by decide), hp₄.reg .x8, k₃ .x8 (by decide), hp₂.reg .x8, k₁ .x8 (by decide), x8]
  · rw [k₅ .x24 (by decide), hp₄.reg .x24, b80002038_x24 g₃]
  · rw [b80002054_x10 g₅]; exact spAdd hpre sp₄ (N := 1728) (M := 928) (by decide)

/-- The empty `Flushes` at `o`: `{0, 8, 0}` twice. -/
def EmptyAt (u : MachineState) (o : Word) : Prop :=
  u.getMem o = 0 ∧ u.getMem (o + 8) = 8 ∧ u.getMem (o + 16) = 0 ∧ u.getMem (o + 24) = 0 ∧
    u.getMem (o + 24 + 8) = 8 ∧ u.getMem (o + 24 + 16) = 0

set_option maxRecDepth 8192 in
/-- MUL: `flushes_arith(1, true)`, `vec![ZERO; 15]` into `sp + 1096`, the `Flushes` to `sp + 1120`,
an empty `Flushes` at `sp + 1728`, then the call of `state_step` on it. -/
theorem mulStage (hFA : Rv64Verifier.Layout.FlushesArithSpec) (hFE : MultilinearContracts.FromElemSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W [(s.getReg .x2 - 1704, kTable), (s.getReg .x2 - 1632, xorT)])
    (r : R8 u) (x10 : u.getReg .x10 = s.getReg .x2 - 928) (x11 : u.getReg .x11 = 1)
    (x12 : u.getReg .x12 = 1) (x1 : u.getReg .x1 = 0x80002098) (hpc : u.pc = 0x8000547c) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004a90 ∧ M8 OI s t A k R Q B Bb (heapNext t)
      [(s.getReg .x2 - 1704, kTable), (s.getReg .x2 - 1632, xorT), (s.getReg .x2 - 1560, mulT)] ∧
      R8 t ∧ EmptyAt t (s.getReg .x2 - 928) ∧ t.getReg .x10 = s.getReg .x2 - 928 ∧
      t.getReg .x1 = 0x80002100) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hL₀ : ∀ e ∈ [(s.getReg .x2 - 1704, kTable), (s.getReg .x2 - 1632, xorT)],
      ∀ (o : Word) (n : Nat), (s.getReg .x2 - 1560).toNat ≤ o.toNat →
        ∀ a, Within a o n → ¬ Within a e.1 72 := fun e he o n ho a ha hw ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp only [Within] at ha hw <;> addr_omega [ha, hw, hb1, ho]
  obtain ⟨t₁, r₂, ⟨pc₂, hp₂, mo₂, M₂, F₂⟩ | d⟩ := arithCall hFA hpre h
    (fun e he a ha ↦ hL₀ e he _ 48 (by addr_omega [hb1]) a ha) hpc x10
  swap
  · exact ⟨t₁, r₂, Or.inr d⟩
  rw [x11, x12] at F₂
  have sp₂ : t₁.getReg .x2 = s.getReg .x2 - 2656 := M₂.m.inv.sp
  obtain ⟨u₃, r₃, g₃⟩ := Sym.BlockSpec.reaches b80002098_spec
    (by rw [pc₂, returnAddress_eq, x1]; decide) trivial
  have k₃ := b80002098_keeps g₃
  have m₃ := b80002098_mem_same g₃
  have hn₃ : heapNext u₃ = heapNext t₁ := by simp only [heapNext, m₃]
  have fr₃ := Rv64Verifier.Layout.DFrame.of_same m₃ (fun _ ↦ False)
  have M₃ := M₂.step hpre fr₃ (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) ⟨hn₃ ▸ M₂.m.inv.heap.lo,
    hn₃ ▸ M₂.m.inv.heap.hi⟩ hn₃.ge (k₃ .x2 (by decide))
  have F₃ := (F₂.frame fr₃ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) M₂.m.inv.heap hn₃.ge).1
  obtain ⟨t₂, r₄, ⟨pc₄, hp₄, mo₄, M₄, F₄, P, Z₄⟩ | d⟩ := padCall hFE (o := s.getReg .x2 - 1560) hpre M₃ F₃
    (by simp only [InSlot]; addr_omega [hb1, hb3]) (by simp only [InSlot]; addr_omega [hb1, hb3])
    (fun a ha hw ↦ by simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
    (fun e he a ha ↦ hL₀ e he _ 24 (by addr_omega [hb1]) a ha)
    (b80002098_pc g₃) (by rw [b80002098_x10 g₃]; exact spAdd hpre sp₂ (N := 1096) (M := 1560) (by decide))
    (by rw [b80002098_x11 g₃, hp₂.reg .x24]; exact r.x24) (by rw [b80002098_x12 g₃]; decide)
  swap
  · exact ⟨t₂, r₂.trans (r₃.trans r₄), Or.inr d⟩
  rw [b80002098_x12 g₃] at Z₄
  have sp₄ : t₂.getReg .x2 = s.getReg .x2 - 2656 := M₄.m.inv.sp
  obtain ⟨u₅, r₅, g₅⟩ := Sym.BlockSpec.reaches b800020ac_spec
    (by rw [pc₄, returnAddress_eq, b80002098_x1 g₃]; decide) (by
      rv_eval [sp₄]
      and_intros <;> valid_access hval [hb1])
  have k₅ := b800020ac_keeps g₅
  have fr₅ : Rv64Verifier.Layout.DFrame t₂ u₅ fun x ↦ Within x (s.getReg .x2 - 1536) 48 ∨
      Within x (s.getReg .x2 - 928) 48 :=
    Expect.ldframe g₅ (by
      rv_eval [sp₄]
      simp only [Within]
      and_intros
      all_goals first
        | exact Or.inl (by addr_omega [hb1])
        | exact Or.inr (by addr_omega [hb1]))
  have hn₅ : heapNext u₅ = heapNext t₂ := by
    simp only [heapNext]; rw [fr₅ _ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1]) (by decide)]
  have hu₄ := M₄.m.inv.heap.hi
  simp only [heapEnd] at hu₄
  have M₅ := M₄.step hpre fr₅ (fun x hx ↦ Or.inl (by
      simp only [Within] at hx ⊢; rcases hx with hx | hx <;> addr_omega [hx, hb1]))
    (fun x hx ↦ by
      have hb := M₄.bb
      simp only [M8W]
      refine ⟨by simp only [Within] at hx; rcases hx with hx | hx <;> addr_omega [hx, hb1, hu₄, hb], ?_, ?_, ?_,
        fun e he ↦ ?_⟩
      · simp only [Within] at hx ⊢; rcases hx with hx | hx <;> addr_omega [hx, hb1]
      · simp only [Within] at hx ⊢; rcases hx with hx | hx <;> addr_omega [hx, hb1]
      · simp only [Within] at hx ⊢; rcases hx with hx | hx <;> addr_omega [hx, hb1]
      · rcases hx with hx | hx
        · exact hL₀ e he _ 48 (by addr_omega [hb1]) x hx
        · exact hL₀ e he _ 48 (by addr_omega [hb1]) x hx)
    ⟨hn₅ ▸ M₄.m.inv.heap.lo, hn₅ ▸ M₄.m.inv.heap.hi⟩ hn₅.ge (k₅ .x2 (by decide))
  have e24 : s.getReg .x2 - 1560 + 24 = s.getReg .x2 - 1536 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have nd : ∀ x, heapNext u ≤ x.toNat → x.toNat < heapNext t₂ → ¬ (Within x (s.getReg .x2 - 1536) 48 ∨
      Within x (s.getReg .x2 - 928) 48) :=
    fun x _ h2 hw ↦ by simp only [Within] at hw; rcases hw with hw | hw <;> addr_omega [hw, h2, hb1, hu₄]
  have F₅ : FB u₅ (s.getReg .x2 - 1560 + 24) (LayoutMirror.flushesArithRust 1 true) (heapNext u) := by
    rw [e24]
    refine F₄.move fr₅ (hdr hpre sp₄ (N := 1120) (N' := 1728) (M := 1536) (M' := 928) (by decide) (by decide)
        (b800020ac_m_x2_1120 g₅) rfl rfl)
      (hdr hpre sp₄ (N := 1128) (N' := 1736) (M := 1528) (M' := 920) (by decide) (by decide)
        (b800020ac_m_x2_1128 g₅) (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
        (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))
      (hdr hpre sp₄ (N := 1136) (N' := 1744) (M := 1520) (M' := 912) (by decide) (by decide)
        (b800020ac_m_x2_1136 g₅) (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
        (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))
      (hdr hpre sp₄ (N := 1144) (N' := 1752) (M := 1512) (M' := 904) (by decide) (by decide)
        (b800020ac_m_x2_1144 g₅) (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
        (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))
      (hdr hpre sp₄ (N := 1152) (N' := 1760) (M := 1504) (M' := 896) (by decide) (by decide)
        (b800020ac_m_x2_1152 g₅) (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
        (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))
      (hdr hpre sp₄ (N := 1160) (N' := 1768) (M := 1496) (M' := 888) (by decide) (by decide)
        (b800020ac_m_x2_1160 g₅) (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
        (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))
      nd (by addr_omega [hb1]) M₄.m.inv.heap hn₅.ge
  have Z₅ := Z₄.frame fr₅ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1])
    (by addr_omega [hb1]) (fun x h1 h2 hw ↦ by
      have := Z₄.buf; simp only [Within] at hw; rcases hw with hw | hw <;> addr_omega [hw, h1, h2, hb1, hu₄, this])
    hn₅.ge (by have := Z₄.buf; omega)
  have T := tableOf (op := 1) Z₅ F₅ (by norm_num)
  have hW : W ≤ heapNext u := h.bb.2.2.2
  have hu₁₃ : heapNext u ≤ heapNext u₃ := by rw [hn₃]; exact mo₂
  have M₆ := M₅.push (o := s.getReg .x2 - 1560) (t := mulT) (by simp only [InSlot]; addr_omega [hb1, hb3])
    T.1 (fun x hx ↦ by have := T.2 x hx; omega)
  have x8₅ : u₅.getReg .x8 = 8 := by
    rw [k₅ .x8 (by decide), hp₄.reg .x8, k₃ .x8 (by decide), hp₂.reg .x8]; exact r.x8
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t₂.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp₄ hNM
  have a8 : s.getReg .x2 - 928 + 8 = t₂.getReg .x2 + 1736 := by
    rw [e 1736 920 (by decide)]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a16 : s.getReg .x2 - 928 + 16 = t₂.getReg .x2 + 1744 := by
    rw [e 1744 912 (by decide)]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a24 : s.getReg .x2 - 928 + 24 = t₂.getReg .x2 + 1752 := by
    rw [e 1752 904 (by decide)]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a24_8 : s.getReg .x2 - 928 + 24 + 8 = t₂.getReg .x2 + 1760 := by
    rw [e 1760 896 (by decide)]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a24_16 : s.getReg .x2 - 928 + 24 + 16 = t₂.getReg .x2 + 1768 := by
    rw [e 1768 888 (by decide)]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  refine ⟨u₅, r₂.trans (r₃.trans (r₄.trans r₅)), Or.inl ⟨b800020ac_pc g₅, M₆,
    ⟨x8₅, by rw [k₅ .x24 (by decide), hp₄.reg .x24, k₃ .x24 (by decide), hp₂.reg .x24]; exact r.x24⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, b800020ac_x1 g₅⟩⟩
  · rw [← e 1728 928 (by decide), b800020ac_m_x2_1728 g₅]
  · rw [a8, b800020ac_m_x2_1736 g₅, ← k₅ .x8 (by decide), x8₅]
  · rw [a16, b800020ac_m_x2_1744 g₅]
  · rw [a24, b800020ac_m_x2_1752 g₅]
  · rw [a24_8, b800020ac_m_x2_1760 g₅, ← k₅ .x8 (by decide), x8₅]
  · rw [a24_16, b800020ac_m_x2_1768 g₅]
  · rw [b800020ac_x10 g₅]; exact e 1728 928 (by decide)

end Rv64Verifier.Proofs.Walk
