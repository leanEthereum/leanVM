import Rv64Verifier.Proofs.Walk.Jp0

/-!
# `walk`: `tables()`, JUMP's next `pc` (R8)

From `AtJump`: `prod(13, 6, 0)` into `sp + 2240`, `prod(13, 0, 1)` into `sp + 2432`, their sum, moved
to `sp + 2504`, plus `col(0, 1)` (`jumpNpc`, to `0x80002a3c`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

theorem JE.cwx {s u t : MachineState} {o : Word} {n lo' hi' : Nat} (hpre : WalkPre s) (I : Inv s u)
    (h : JE s u)
    (fr : Rv64Verifier.Layout.DFrame u t fun a ↦ CW u t o n a ∨ (lo' ≤ a.toNat ∧ a.toNat < hi'))
    (hn : n ≤ 8736) (hoo : ∀ x, Within x (s.getReg .x2 - 928) 48 → ¬ Within x o 24) (hv : HeapOk t)
    (hhi' : hi' ≤ heapNext t) (mono : heapNext u ≤ heapNext t) : JE s t :=
  h.frame hpre fr (slot_not_cwx hpre I (inSlot_off hpre (by decide)) hn hoo hv hhi') I.heap mono

theorem JE.cw {s u t : MachineState} {o : Word} {n : Nat} (hpre : WalkPre s) (I : Inv s u)
    (h : JE s u) (fr : Rv64Verifier.Layout.DFrame u t (CW u t o n)) (hn : n ≤ 8736)
    (hoo : ∀ x, Within x (s.getReg .x2 - 928) 48 → ¬ Within x o 24) (hv : HeapOk t)
    (mono : heapNext u ≤ heapNext t) : JE s t :=
  h.cwx hpre I (lo' := 0) (hi' := 0) (fr.mono fun _ ha ↦ Or.inl ha) hn hoo hv (Nat.zero_le _) mono

theorem SF.cw {s u t : MachineState} {o o' : Word} {n lo hi : Nat}
    {f : LayoutMirror.FormRust} (hpre : WalkPre s) (I : Inv s u) (hf : SF u o f lo hi)
    (ho : InSlot s o 24) (hhi : hi ≤ heapNext u)
    (fr : Rv64Verifier.Layout.DFrame u t (CW u t o' n))
    (hn : n ≤ 8736) (ho' : InSlot s o' 24) (hoo : ∀ x, Within x o 24 → ¬ Within x o' 24)
    (hv : HeapOk t) (mono : heapNext u ≤ heapNext t) : SF t o f lo hi :=
  hf.cwx hpre I ho hhi (lo' := 0) (hi' := 0) (fr.mono fun _ ha ↦ Or.inl ha) hn ho' hoo
    (Or.inr (Nat.zero_le _)) (Nat.zero_le _) hv mono

/-- A form in a frame slot kept across a block writing only another frame slot. -/
theorem SF.blk {s u v : MachineState} {o o' : Word} {n lo hi : Nat} {f : LayoutMirror.FormRust}
    (hpre : WalkPre s) (hf : SF u o f lo hi) (ho : InSlot s o 24) (ho' : InSlot s o' n)
    (hhi : hi ≤ heapNext u) (hheap : HeapOk u)
    (fr : Rv64Verifier.Layout.DFrame u v fun x ↦ Within x o' n)
    (hoo : ∀ x, Within x o 24 → ¬ Within x o' n) (mono : heapNext u ≤ heapNext v) : SF v o f lo hi := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨e1, e2, -⟩ := ho
  obtain ⟨o1, o2, -⟩ := ho'
  have hu := hheap.hi
  simp only [heapEnd, heapNext] at hu hhi
  exact hf.frame fr hoo (fun x _ hx hw ↦ by simp only [Within] at hw; addr_omega [hw, hx, hb1, o1, hhi, hu])
    (by addr_omega [hb1, e2]) hheap mono

/-- JUMP's next `pc`, `b·dest + b·g·pc + g·pc`. -/
abbrev npcF : LayoutMirror.FormRust :=
  ((LayoutMirror.prodRust 13 6 0).add (LayoutMirror.prodRust 13 0 1)).add (LayoutMirror.colRust 0 1)

set_option maxRecDepth 8192 in
/-- JUMP's next `pc` at `sp + 2504`, to `0x80002a3c`. -/
theorem jumpNpc (hP : Rv64Verifier.Layout.ProdSpec) (hC : Rv64Verifier.Layout.ColSpec)
    (hA : Rv64Verifier.Layout.AddScaledSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} (hpre : WalkPre s)
    (h : AtJump OI s u A k R Q B Bb) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80002a3c ∧
      M8 OI s t A k R Q B Bb (heapNext u) (L5 s) ∧ JE s t ∧
      SF t (s.getReg .x2 - 152) npcF (heapNext u) (heapNext t) ∧ JR s t ∧
      t.getReg .x24 = 0xa00000b0) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I₀ := h.m.m.inv
  have J₀ := JE.of_empty h.empty
  have r₀ : JR s u := ⟨h.x19, h.x21, h.x22, h.x23, h.x27⟩
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  have hnA : Rv64Verifier.Layout.addScaledStack ≤ 8736 := by decide
  -- `prod(13, 6, 0)` into `sp + 2240`
  obtain ⟨t₁, q₁, ⟨pc₁, hp₁, M₁, A₁, fr₁, hv₁, mo₁⟩ | d⟩ := prodF hP (o := s.getReg .x2 - 416) hpre h.m
    (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) h.pc h.x10
  swap
  · exact ⟨t₁, q₁, Or.inr d⟩
  rw [h.x11, h.x12, h.x13] at A₁
  have J₁ := J₀.cw hpre I₀ fr₁ hn (apart_off hpre (by decide) (by decide) (by decide)) hv₁ mo₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := M₁.m.inv.sp
  have r₁ := r₀.pres hp₁
  -- `prod(13, 0, 1)` into `sp + 2432`
  obtain ⟨u₂, p₂, g₂⟩ := Sym.BlockSpec.reaches b800029b0_spec
    (by rw [pc₁, returnAddress_eq, h.x1]; decide) trivial
  have m₂ := b800029b0_mem_same g₂
  have hn₂ : heapNext u₂ = heapNext t₁ := by simp only [heapNext, m₂]
  have M₂ := M₁.same hpre m₂ (b800029b0_keeps g₂ .x2 (by decide))
  have fr₂ := Rv64Verifier.Layout.DFrame.of_same m₂ (fun _ ↦ False)
  have A₂ := A₁.frame fr₂ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hv₁ hn₂.ge
  have J₂ := J₁.frame hpre fr₂ (fun _ _ h ↦ h) hv₁ hn₂.ge
  have r₂ := r₁.keeps (b800029b0_keeps g₂)
  obtain ⟨t₃, q₃, ⟨pc₃, hp₃, M₃, B₃, fr₃, hv₃, mo₃⟩ | d⟩ := prodF hP (o := s.getReg .x2 - 224) hpre M₂
    (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) (b800029b0_pc g₂)
    (by rw [b800029b0_x10 g₂]; exact spAdd hpre sp₁ (by decide))
  swap
  · exact ⟨t₃, q₁.trans (p₂.trans q₃), Or.inr d⟩
  rw [b800029b0_x11 g₂, b800029b0_x12 g₂, b800029b0_x13 g₂] at B₃
  have Q₃ := q₁.trans (p₂.trans q₃)
  have I₂ := M₂.m.inv
  have A₃ := A₂.cw hpre I₂ (inSlot_off hpre (by decide)) hn₂.ge fr₃ hn (inSlot_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) hv₃ mo₃
  have J₃ := J₂.cw hpre I₂ fr₃ hn (apart_off hpre (by decide) (by decide) (by decide)) hv₃ mo₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := M₃.m.inv.sp
  have r₃ := r₂.pres hp₃
  -- `add_scaled` into `sp + 2240`
  obtain ⟨u₄, p₄, g₄⟩ := Sym.BlockSpec.reaches b800029cc_spec
    (by rw [pc₃, returnAddress_eq, b800029b0_x1 g₂]; decide) (by
      rv_eval [sp₃, r₃.x23]
      and_intros <;> valid_access hval [hb1])
  have m₄ := b800029cc_mem_same g₄
  have hn₄ : heapNext u₄ = heapNext t₃ := by simp only [heapNext, m₄]
  have M₄ := M₃.same hpre m₄ (b800029cc_keeps g₄ .x2 (by decide))
  have fr₄ := Rv64Verifier.Layout.DFrame.of_same m₄ (fun _ ↦ False)
  have A₄ := A₃.frame fr₄ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hv₃ hn₄.ge
  have B₄ := B₃.frame fr₄ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hv₃ hn₄.ge
  have J₄ := J₃.frame hpre fr₄ (fun _ _ h ↦ h) hv₃ hn₄.ge
  have r₄ := r₃.keeps (b800029cc_keeps g₄)
  obtain ⟨t₅, q₅, ⟨pc₅, hp₅, M₅, A₅, mo₅, fr₅⟩ | d⟩ := ascM8d hA hpre M₄ (b800029cc_pc g₄)
    (by rw [b800029cc_x10 g₄]; exact spAdd hpre sp₃ (by decide)) (inSlot_off hpre (by decide))
    (l5_off hpre (by decide)) A₄ B₄ (len_term (by rw [B₄.val]; rfl)) (Or.inr (by rw [hn₂]))
    (by omega) (by omega) (le_refl _)
    (by rw [b800029cc_x11 g₄, vecPtr, m₄, r₃.x23]; rv_eval [])
    (by rw [b800029cc_x12 g₄, vecLen, m₄, r₃.x23]; rv_eval []) (b800029cc_x13 g₄)
  swap
  · exact ⟨t₅, Q₃.trans (p₄.trans q₅), Or.inr d⟩
  have Q₅ := Q₃.trans (p₄.trans q₅)
  have I₄ := M₄.m.inv
  have hv₅ := M₅.m.inv.heap
  have J₅ := J₄.cwx hpre I₄ fr₅ hnA (apart_off hpre (by decide) (by decide) (by decide)) hv₅
    (by omega) mo₅
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 2656 := M₅.m.inv.sp
  have r₅ := r₄.pres hp₅
  have x24₅ : t₅.getReg .x24 = 0xa00000b0 := by rw [hp₅.reg .x24]; exact b800029cc_x24 g₄
  -- the sum moved to `sp + 2504`, `col(0, 1)` into `sp + 2432`
  obtain ⟨u₆, p₆, g₆⟩ := Sym.BlockSpec.reaches b800029f0_spec
    (by rw [pc₅, returnAddress_eq, b800029cc_x1 g₄]; decide) (by
      rv_eval [sp₅, r₅.x23]
      and_intros <;> valid_access hval [hb1])
  have fr₆ : Rv64Verifier.Layout.DFrame t₅ u₆ fun x ↦ Within x (s.getReg .x2 - 152) 24 :=
    Expect.ldframe g₆ (by
      rv_eval [sp₅, r₅.x23]
      simp only [Within]
      and_intros <;> addr_omega [hb1])
  obtain ⟨M₆, hn₆⟩ := M₅.slotStep hpre (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) fr₆
    (b800029f0_keeps g₆ .x2 (by decide))
  have hu₅ := hv₅.hi
  simp only [heapEnd] at hu₅
  have A₆ := A₅.move fr₆ (by mem_tac [r₅.x23] (b800029f0_m_x23_360 g₆))
    (by mem_tac [r₅.x23] (b800029f0_m_x23_368 g₆)) (by mem_tac [r₅.x23] (b800029f0_m_x23_376 g₆))
    (fun x _ hx hw ↦ by simp only [Within] at hw; simp only [heapNext] at hx hu₅; addr_omega [hw, hx, hb1, hu₅])
    hv₅ hn₆.ge
  have J₆ := J₅.frame hpre fr₆ (apart_off hpre (by decide) (by decide) (by decide)) hv₅ hn₆.ge
  have r₆ := r₅.keeps (b800029f0_keeps g₆)
  have x24₆ : u₆.getReg .x24 = 0xa00000b0 := by rw [b800029f0_keeps g₆ .x24 (by decide)]; exact x24₅
  obtain ⟨t₇, q₇, ⟨pc₇, hp₇, M₇, C₇, fr₇, hv₇, mo₇⟩ | d⟩ := colF hC (o := s.getReg .x2 - 224) hpre M₆
    (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) (b800029f0_pc g₆)
    (by rw [b800029f0_x10 g₆]; exact spAdd hpre sp₅ (by decide))
  swap
  · exact ⟨t₇, Q₅.trans (p₆.trans q₇), Or.inr d⟩
  rw [b800029f0_x11 g₆, b800029f0_x12 g₆] at C₇
  have Q₇ := Q₅.trans (p₆.trans q₇)
  have I₆ := M₆.m.inv
  have A₇ := A₆.cw hpre I₆ (inSlot_off hpre (by decide)) hn₆.ge fr₇ hn (inSlot_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) hv₇ mo₇
  have J₇ := J₆.cw hpre I₆ fr₇ hn (apart_off hpre (by decide) (by decide) (by decide)) hv₇ mo₇
  have sp₇ : t₇.getReg .x2 = s.getReg .x2 - 2656 := M₇.m.inv.sp
  have r₇ := r₆.pres hp₇
  have x24₇ : t₇.getReg .x24 = 0xa00000b0 := by rw [hp₇.reg .x24]; exact x24₆
  -- `add_scaled` into `sp + 2504`
  obtain ⟨u₈, p₈, g₈⟩ := Sym.BlockSpec.reaches b80002a20_spec
    (by rw [pc₇, returnAddress_eq, b800029f0_x1 g₆]; decide) (by
      rv_eval [sp₇, r₇.x23]
      and_intros <;> valid_access hval [hb1])
  have m₈ := b80002a20_mem_same g₈
  have hn₈ : heapNext u₈ = heapNext t₇ := by simp only [heapNext, m₈]
  have M₈ := M₇.same hpre m₈ (b80002a20_keeps g₈ .x2 (by decide))
  have fr₈ := Rv64Verifier.Layout.DFrame.of_same m₈ (fun _ ↦ False)
  have A₈ := A₇.frame fr₈ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hv₇ hn₈.ge
  have C₈ := C₇.frame fr₈ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hv₇ hn₈.ge
  have J₈ := J₇.frame hpre fr₈ (fun _ _ h ↦ h) hv₇ hn₈.ge
  have r₈ := r₇.keeps (b80002a20_keeps g₈)
  obtain ⟨t₉, q₉, ⟨pc₉, hp₉, M₉, A₉, mo₉, fr₉⟩ | d⟩ := ascM8d hA hpre M₈ (b80002a20_pc g₈)
    (by rw [b80002a20_x10 g₈]; exact spAdd hpre sp₇ (by decide)) (inSlot_off hpre (by decide))
    (l5_off hpre (by decide)) A₈ C₈ (len_term (by rw [C₈.val]; rfl)) (Or.inr (by rw [hn₆]))
    (by omega) (by omega) (le_refl _)
    (by rw [b80002a20_x11 g₈, vecPtr, m₈, r₇.x23]; rv_eval [])
    (by rw [b80002a20_x12 g₈, vecLen, m₈, r₇.x23]; rv_eval []) (by rw [b80002a20_x13 g₈, x24₇])
  swap
  · exact ⟨t₉, Q₇.trans (p₈.trans q₉), Or.inr d⟩
  have I₈ := M₈.m.inv
  have hv₉ := M₉.m.inv.heap
  refine ⟨t₉, Q₇.trans (p₈.trans q₉), Or.inl ⟨by rw [pc₉, returnAddress_eq, b80002a20_x1 g₈]; decide,
    M₉, J₈.cwx hpre I₈ fr₉ hnA (apart_off hpre (by decide) (by decide) (by decide)) hv₉ (by omega) mo₉,
    A₉, r₈.pres hp₉, ?_⟩⟩
  rw [hp₉.reg .x24, b80002a20_keeps g₈ .x24 (by decide)]; exact x24₇

end Rv64Verifier.Proofs.Walk
