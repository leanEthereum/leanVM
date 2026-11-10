import Rv64Verifier.Proofs.Walk.Jp1

/-!
# `walk`: `tables()`, JUMP's next `fp` and `state_derived` (R8)

From `jumpNpc`'s end: the next `pc` moved to `sp + 2312`; `prod(13, 7, 0)` into `sp + 2240`,
`prod(13, 1, 0)` into `sp + 2432`, their sum moved to `sp + 2504`, plus `col(1, 0)`, moved back to
`sp + 2240`; `state_derived(0, 1, npc, nfp)` on the empty `Flushes` at `sp + 1728` (`jumpNfp`, to
`0x80002b28`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

/-- JUMP's next `fp`, `b·frame + b·fp + fp`. -/
abbrev nfpF : LayoutMirror.FormRust :=
  ((LayoutMirror.prodRust 13 7 0).add (LayoutMirror.prodRust 13 1 0)).add (LayoutMirror.colRust 1 0)

set_option maxRecDepth 8192 in
/-- JUMP's next `fp`, then `state_derived`, to `0x80002b28`. -/
theorem jumpNfp (hP : Rv64Verifier.Layout.ProdSpec) (hC : Rv64Verifier.Layout.ColSpec)
    (hA : Rv64Verifier.Layout.AddScaledSpec) (hSD : Rv64Verifier.Layout.StateDerivedSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat} (hpre : WalkPre s)
    (M : M8 OI s u A k R Q B Bb W (L5 s)) (J : JE s u)
    (N : SF u (s.getReg .x2 - 152) npcF W (heapNext u)) (r : JR s u)
    (x24 : u.getReg .x24 = 0xa00000b0) (hpc : u.pc = 0x80002a3c) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80002b28 ∧
      M8 OI s t A k R Q B Bb W (L5 s) ∧
      FB t (s.getReg .x2 - 928) (({} : LayoutMirror.FlushesRust).stateDerived 0 1 npcF nfpF) W ∧
      JR s t) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  have hnA : Rv64Verifier.Layout.addScaledStack ≤ 8736 := by decide
  have I₀ := M.m.inv
  have sp₀ : u.getReg .x2 = s.getReg .x2 - 2656 := I₀.sp
  have hv₀ := I₀.heap
  have hu₀ := hv₀.hi
  simp only [heapEnd] at hu₀
  have hW₀ : W ≤ heapNext u := M.bb.2.2.2
  -- the next `pc` moved to `sp + 2312`; `prod(13, 7, 0)` into `sp + 2240`
  obtain ⟨v₁, p₁, g₁⟩ := Sym.BlockSpec.reaches b80002a3c_spec hpc (by
      rv_eval [sp₀, r.x23]
      and_intros <;> valid_access hval [hb1])
  have fr₁ : Rv64Verifier.Layout.DFrame u v₁ fun x ↦ Within x (s.getReg .x2 - 344) 24 :=
    Expect.ldframe g₁ (by
      rv_eval [sp₀, r.x23]
      simp only [Within]
      and_intros <;> addr_omega [hb1])
  obtain ⟨M₁, hn₁⟩ := M.slotStep hpre (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) fr₁
    (b80002a3c_keeps g₁ .x2 (by decide))
  have N₁ := N.move fr₁ (by mem_tac [r.x23] (b80002a3c_m_x23_168 g₁))
    (by mem_tac [r.x23] (b80002a3c_m_x23_176 g₁)) (by mem_tac [r.x23] (b80002a3c_m_x23_184 g₁))
    (fun x _ hx hw ↦ by simp only [Within] at hw; simp only [heapNext] at hx hu₀; addr_omega [hw, hx, hb1, hu₀])
    hv₀ hn₁.ge
  have J₁ := J.frame hpre fr₁ (apart_off hpre (by decide) (by decide) (by decide)) hv₀ hn₁.ge
  have r₁ := r.keeps (b80002a3c_keeps g₁)
  have x24₁ : v₁.getReg .x24 = 0xa00000b0 := by rw [b80002a3c_keeps g₁ .x24 (by decide)]; exact x24
  have I₁ := M₁.m.inv
  obtain ⟨t₂, q₂, ⟨pc₂, hp₂, M₂, C₂, fr₂, hv₂, mo₂⟩ | d⟩ := prodF hP (o := s.getReg .x2 - 416) hpre M₁
    (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) (b80002a3c_pc g₁)
    (by rw [b80002a3c_x10 g₁]; exact spAdd hpre sp₀ (by decide))
  swap
  · exact ⟨t₂, p₁.trans q₂, Or.inr d⟩
  rw [b80002a3c_x11 g₁, b80002a3c_x12 g₁, b80002a3c_x13 g₁] at C₂
  have Q₂ := p₁.trans q₂
  have N₂ := N₁.cw hpre I₁ (inSlot_off hpre (by decide)) hn₁.ge fr₂ hn (inSlot_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) hv₂ mo₂
  have J₂ := J₁.cw hpre I₁ fr₂ hn (apart_off hpre (by decide) (by decide) (by decide)) hv₂ mo₂
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := M₂.m.inv.sp
  have r₂ := r₁.pres hp₂
  have x24₂ : t₂.getReg .x24 = 0xa00000b0 := by rw [hp₂.reg .x24]; exact x24₁
  -- `prod(13, 1, 0)` into `sp + 2432`
  obtain ⟨u₃, p₃, g₃⟩ := Sym.BlockSpec.reaches b80002a70_spec
    (by rw [pc₂, returnAddress_eq, b80002a3c_x1 g₁]; decide) trivial
  have m₃ := b80002a70_mem_same g₃
  have hn₃ : heapNext u₃ = heapNext t₂ := by simp only [heapNext, m₃]
  have M₃ := M₂.same hpre m₃ (b80002a70_keeps g₃ .x2 (by decide))
  have fr₃ := Rv64Verifier.Layout.DFrame.of_same m₃ (fun _ ↦ False)
  have N₃ := N₂.frame fr₃ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hv₂ hn₃.ge
  have C₃ := C₂.frame fr₃ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hv₂ hn₃.ge
  have J₃ := J₂.frame hpre fr₃ (fun _ _ h ↦ h) hv₂ hn₃.ge
  have r₃ := r₂.keeps (b80002a70_keeps g₃)
  have x24₃ : u₃.getReg .x24 = 0xa00000b0 := by rw [b80002a70_keeps g₃ .x24 (by decide)]; exact x24₂
  have I₃ := M₃.m.inv
  obtain ⟨t₄, q₄, ⟨pc₄, hp₄, M₄, D₄, fr₄, hv₄, mo₄⟩ | d⟩ := prodF hP (o := s.getReg .x2 - 224) hpre M₃
    (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) (b80002a70_pc g₃)
    (by rw [b80002a70_x10 g₃]; exact spAdd hpre sp₂ (by decide))
  swap
  · exact ⟨t₄, Q₂.trans (p₃.trans q₄), Or.inr d⟩
  rw [b80002a70_x11 g₃, b80002a70_x12 g₃, b80002a70_x13 g₃] at D₄
  have Q₄ := Q₂.trans (p₃.trans q₄)
  have N₄ := N₃.cw hpre I₃ (inSlot_off hpre (by decide)) (by omega) fr₄ hn (inSlot_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) hv₄ mo₄
  have C₄ := C₃.cw hpre I₃ (inSlot_off hpre (by decide)) hn₃.ge fr₄ hn (inSlot_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) hv₄ mo₄
  have J₄ := J₃.cw hpre I₃ fr₄ hn (apart_off hpre (by decide) (by decide) (by decide)) hv₄ mo₄
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 2656 := M₄.m.inv.sp
  have r₄ := r₃.pres hp₄
  have x24₄ : t₄.getReg .x24 = 0xa00000b0 := by rw [hp₄.reg .x24]; exact x24₃
  -- `add_scaled` into `sp + 2240`
  obtain ⟨u₅, p₅, g₅⟩ := Sym.BlockSpec.reaches b80002a8c_spec
    (by rw [pc₄, returnAddress_eq, b80002a70_x1 g₃]; decide) (by
      rv_eval [sp₄, r₄.x23]
      and_intros <;> valid_access hval [hb1])
  have m₅ := b80002a8c_mem_same g₅
  have hn₅ : heapNext u₅ = heapNext t₄ := by simp only [heapNext, m₅]
  have M₅ := M₄.same hpre m₅ (b80002a8c_keeps g₅ .x2 (by decide))
  have fr₅ := Rv64Verifier.Layout.DFrame.of_same m₅ (fun _ ↦ False)
  have N₅ := N₄.frame fr₅ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hv₄ hn₅.ge
  have C₅ := C₄.frame fr₅ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hv₄ hn₅.ge
  have D₅ := D₄.frame fr₅ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hv₄ hn₅.ge
  have J₅ := J₄.frame hpre fr₅ (fun _ _ h ↦ h) hv₄ hn₅.ge
  have r₅ := r₄.keeps (b80002a8c_keeps g₅)
  have x24₅ : u₅.getReg .x24 = 0xa00000b0 := by rw [b80002a8c_keeps g₅ .x24 (by decide)]; exact x24₄
  have I₅ := M₅.m.inv
  obtain ⟨t₆, q₆, ⟨pc₆, hp₆, M₆, C₆, mo₆, fr₆⟩ | d⟩ := ascM8d hA hpre M₅ (b80002a8c_pc g₅)
    (by rw [b80002a8c_x10 g₅]; exact spAdd hpre sp₄ (by decide)) (inSlot_off hpre (by decide))
    (l5_off hpre (by decide)) C₅ D₅ (len_term (by rw [D₅.val]; rfl)) (Or.inr (by rw [hn₃]))
    (by omega) (by omega) (by omega)
    (by rw [b80002a8c_x11 g₅, vecPtr, m₅, r₄.x23]; rv_eval [])
    (by rw [b80002a8c_x12 g₅, vecLen, m₅, r₄.x23]; rv_eval []) (by rw [b80002a8c_x13 g₅, x24₄])
  swap
  · exact ⟨t₆, Q₄.trans (p₅.trans q₆), Or.inr d⟩
  have Q₆ := Q₄.trans (p₅.trans q₆)
  have hv₆ := M₆.m.inv.heap
  have N₆ := N₅.cwx hpre I₅ (inSlot_off hpre (by decide)) (by omega) fr₆ hnA (inSlot_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) (Or.inl (by omega)) (by omega) hv₆ mo₆
  have J₆ := J₅.cwx hpre I₅ fr₆ hnA (apart_off hpre (by decide) (by decide) (by decide)) hv₆
    (by omega) mo₆
  have sp₆ : t₆.getReg .x2 = s.getReg .x2 - 2656 := M₆.m.inv.sp
  have r₆ := r₅.pres hp₆
  have x24₆ : t₆.getReg .x24 = 0xa00000b0 := by rw [hp₆.reg .x24]; exact x24₅
  have hu₆ := hv₆.hi
  simp only [heapEnd] at hu₆
  -- the sum moved to `sp + 2504`, `col(1, 0)` into `sp + 2432`
  obtain ⟨u₇, p₇, g₇⟩ := Sym.BlockSpec.reaches b80002aa8_spec
    (by rw [pc₆, returnAddress_eq, b80002a8c_x1 g₅]; decide) (by
      rv_eval [sp₆, r₆.x23]
      and_intros <;> valid_access hval [hb1])
  have fr₇ : Rv64Verifier.Layout.DFrame t₆ u₇ fun x ↦ Within x (s.getReg .x2 - 152) 24 :=
    Expect.ldframe g₇ (by
      rv_eval [sp₆, r₆.x23]
      simp only [Within]
      and_intros <;> addr_omega [hb1])
  obtain ⟨M₇, hn₇⟩ := M₆.slotStep hpre (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) fr₇
    (b80002aa8_keeps g₇ .x2 (by decide))
  have C₇ := C₆.move fr₇ (by mem_tac [r₆.x23] (b80002aa8_m_x23_360 g₇))
    (by mem_tac [r₆.x23] (b80002aa8_m_x23_368 g₇)) (by mem_tac [r₆.x23] (b80002aa8_m_x23_376 g₇))
    (fun x _ hx hw ↦ by simp only [Within] at hw; simp only [heapNext] at hx hu₆; addr_omega [hw, hx, hb1, hu₆])
    hv₆ hn₇.ge
  have N₇ := N₆.blk hpre (inSlot_off hpre (by decide)) (inSlot_off hpre (by decide)) (by omega) hv₆ fr₇
    (apart_off hpre (by decide) (by decide) (by decide)) hn₇.ge
  have J₇ := J₆.frame hpre fr₇ (apart_off hpre (by decide) (by decide) (by decide)) hv₆ hn₇.ge
  have r₇ := r₆.keeps (b80002aa8_keeps g₇)
  have x24₇ : u₇.getReg .x24 = 0xa00000b0 := by rw [b80002aa8_keeps g₇ .x24 (by decide)]; exact x24₆
  have I₇ := M₇.m.inv
  obtain ⟨t₈, q₈, ⟨pc₈, hp₈, M₈, E₈, fr₈, hv₈, mo₈⟩ | d⟩ := colF hC (o := s.getReg .x2 - 224) hpre M₇
    (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) (b80002aa8_pc g₇)
    (by rw [b80002aa8_x10 g₇]; exact spAdd hpre sp₆ (by decide))
  swap
  · exact ⟨t₈, Q₆.trans (p₇.trans q₈), Or.inr d⟩
  rw [b80002aa8_x11 g₇, b80002aa8_x12 g₇] at E₈
  have Q₈ := Q₆.trans (p₇.trans q₈)
  have N₈ := N₇.cw hpre I₇ (inSlot_off hpre (by decide)) (by omega) fr₈ hn (inSlot_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) hv₈ mo₈
  have C₈ := C₇.cw hpre I₇ (inSlot_off hpre (by decide)) hn₇.ge fr₈ hn (inSlot_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) hv₈ mo₈
  have J₈ := J₇.cw hpre I₇ fr₈ hn (apart_off hpre (by decide) (by decide) (by decide)) hv₈ mo₈
  have sp₈ : t₈.getReg .x2 = s.getReg .x2 - 2656 := M₈.m.inv.sp
  have r₈ := r₇.pres hp₈
  have x24₈ : t₈.getReg .x24 = 0xa00000b0 := by rw [hp₈.reg .x24]; exact x24₇
  -- `add_scaled` into `sp + 2504`
  obtain ⟨u₉, p₉, g₉⟩ := Sym.BlockSpec.reaches b80002ad8_spec
    (by rw [pc₈, returnAddress_eq, b80002aa8_x1 g₇]; decide) (by
      rv_eval [sp₈, r₈.x23]
      and_intros <;> valid_access hval [hb1])
  have m₉ := b80002ad8_mem_same g₉
  have hn₉ : heapNext u₉ = heapNext t₈ := by simp only [heapNext, m₉]
  have M₉ := M₈.same hpre m₉ (b80002ad8_keeps g₉ .x2 (by decide))
  have fr₉ := Rv64Verifier.Layout.DFrame.of_same m₉ (fun _ ↦ False)
  have N₉ := N₈.frame fr₉ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hv₈ hn₉.ge
  have C₉ := C₈.frame fr₉ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hv₈ hn₉.ge
  have E₉ := E₈.frame fr₉ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hv₈ hn₉.ge
  have J₉ := J₈.frame hpre fr₉ (fun _ _ h ↦ h) hv₈ hn₉.ge
  have r₉ := r₈.keeps (b80002ad8_keeps g₉)
  have x24₉ : u₉.getReg .x24 = 0xa00000b0 := by rw [b80002ad8_keeps g₉ .x24 (by decide)]; exact x24₈
  have I₉ := M₉.m.inv
  obtain ⟨t₁₀, q₁₀, ⟨pc₁₀, hp₁₀, M₁₀, F₁₀, mo₁₀, fr₁₀⟩ | d⟩ := ascM8d hA hpre M₉ (b80002ad8_pc g₉)
    (by rw [b80002ad8_x10 g₉]; exact spAdd hpre sp₈ (by decide)) (inSlot_off hpre (by decide))
    (l5_off hpre (by decide)) C₉ E₉ (len_term (by rw [E₉.val]; rfl)) (Or.inr (by rw [hn₇]))
    (by omega) (by omega) (by omega)
    (by rw [b80002ad8_x11 g₉, vecPtr, m₉, r₈.x23]; rv_eval [])
    (by rw [b80002ad8_x12 g₉, vecLen, m₉, r₈.x23]; rv_eval []) (by rw [b80002ad8_x13 g₉, x24₈])
  swap
  · exact ⟨t₁₀, Q₈.trans (p₉.trans q₁₀), Or.inr d⟩
  have Q₁₀ := Q₈.trans (p₉.trans q₁₀)
  have hv₁₀ := M₁₀.m.inv.heap
  have N₁₀ := N₉.cwx hpre I₉ (inSlot_off hpre (by decide)) (by omega) fr₁₀ hnA (inSlot_off hpre (by decide))
    (apart_off hpre (by decide) (by decide) (by decide)) (Or.inl (by omega)) (by omega) hv₁₀ mo₁₀
  have J₁₀ := J₉.cwx hpre I₉ fr₁₀ hnA (apart_off hpre (by decide) (by decide) (by decide)) hv₁₀
    (by omega) mo₁₀
  have sp₁₀ : t₁₀.getReg .x2 = s.getReg .x2 - 2656 := M₁₀.m.inv.sp
  have r₁₀ := r₉.pres hp₁₀
  have hu₁₀ := hv₁₀.hi
  simp only [heapEnd] at hu₁₀
  -- the next `fp` moved to `sp + 2240`, `state_derived`
  obtain ⟨u₁₁, p₁₁, g₁₁⟩ := Sym.BlockSpec.reaches b80002af4_spec
    (by rw [pc₁₀, returnAddress_eq, b80002ad8_x1 g₉]; decide) (by
      rv_eval [sp₁₀, r₁₀.x23]
      and_intros <;> valid_access hval [hb1])
  have fr₁₁ : Rv64Verifier.Layout.DFrame t₁₀ u₁₁ fun x ↦ Within x (s.getReg .x2 - 416) 24 :=
    Expect.ldframe g₁₁ (by
      rv_eval [sp₁₀, r₁₀.x23]
      simp only [Within]
      and_intros <;> addr_omega [hb1])
  obtain ⟨M₁₁, hn₁₁⟩ := M₁₀.slotStep hpre (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) fr₁₁
    (b80002af4_keeps g₁₁ .x2 (by decide))
  have F₁₁ := F₁₀.move fr₁₁ (by mem_tac [r₁₀.x23] (b80002af4_m_x23_96 g₁₁))
    (by mem_tac [r₁₀.x23] (b80002af4_m_x23_104 g₁₁)) (by mem_tac [r₁₀.x23] (b80002af4_m_x23_112 g₁₁))
    (fun x _ hx hw ↦ by simp only [Within] at hw; simp only [heapNext] at hx hu₁₀; addr_omega [hw, hx, hb1, hu₁₀])
    hv₁₀ hn₁₁.ge
  have N₁₁ := N₁₀.blk hpre (inSlot_off hpre (by decide)) (inSlot_off hpre (by decide)) (by omega) hv₁₀ fr₁₁
    (apart_off hpre (by decide) (by decide) (by decide)) hn₁₁.ge
  have J₁₁ := J₁₀.frame hpre fr₁₁ (apart_off hpre (by decide) (by decide) (by decide)) hv₁₀ hn₁₁.ge
  have r₁₁ := r₁₀.keeps (b80002af4_keeps g₁₁)
  have I₁₁ := M₁₁.m.inv
  have hnS : Rv64Verifier.Layout.stateDerivedStack ≤ 8736 := by decide
  have x10 : u₁₁.getReg .x10 = s.getReg .x2 - 928 := by
    rw [b80002af4_x10 g₁₁]; exact spAdd hpre sp₁₀ (by decide)
  have x11 : u₁₁.getReg .x11 = s.getReg .x2 - 344 := by
    rw [b80002af4_x11 g₁₁]; exact spAdd hpre sp₁₀ (by decide)
  have x12 : u₁₁.getReg .x12 = s.getReg .x2 - 416 := by
    rw [b80002af4_x12 g₁₁]; exact spAdd hpre sp₁₀ (by decide)
  obtain ⟨v1, v2, v3⟩ := slotW hpre I₁₁ (n := 6) (o := s.getReg .x2 - 928) (inSlot_off hpre (by decide)) hnS
  obtain ⟨w1, w2, w3⟩ := slotPre hpre I₁₁ (o := s.getReg .x2 - 344) (inSlot_off hpre (by decide)) hnS
  obtain ⟨z1, z2, z3⟩ := slotPre hpre I₁₁ (o := s.getReg .x2 - 416) (inSlot_off hpre (by decide)) hnS
  have hu₁₁ := I₁₁.heap.hi
  simp only [heapEnd] at hu₁₁
  have nb := N₁₁.buf
  have fb := F₁₁.buf
  have pre : Rv64Verifier.Layout.StateDerivedPre u₁₁ := {
    heap := I₁₁.heap
    stack := stk_sub hpre I₁₁ hnS (by decide)
    self := by rw [x10]; exact v1
    ok := by rw [x10]; exact J₁₁.ok
    selfFree := by rw [x10]; exact v2
    selfStack := by rw [x10]; exact v3
    rodata := I₁₁.rodata hpre
    npc := by rw [x11]; exact w1
    nfp := by rw [x12]; exact z1
    npcOk := by rw [x11]; exact N₁₁.ok
    nfpOk := by rw [x12]; exact F₁₁.ok
    npcFree := by rw [x11]; exact w2
    nfpFree := by rw [x12]; exact z2
    npcStack := by rw [x11]; exact w3
    nfpStack := by rw [x12]; exact z3
    apart := fun x hx hw ↦ by
      rw [x10] at hw
      rw [x11, x12] at hx
      rcases hw with hw | hw
      · have e1 := hu₀
        have e2 := hu₁₀
        simp only [heapNext] at e1 e2
        rcases hx with hx | hx | hx | hx
        · simp only [Within] at hx hw; addr_omega [hx, hw, hb1]
        · have := nb x hx; simp only [Within] at hw; simp only [heapNext] at this
          addr_omega [hw, this, hb1, e1]
        · simp only [Within] at hx hw; addr_omega [hx, hw, hb1]
        · have := fb x hx; simp only [Within] at hw; simp only [heapNext] at this
          addr_omega [hw, this, hb1, e2]
      · exact J₁₁.nd x (hw.imp Or.inl Or.inl) }
  obtain ⟨t₁₂, q₁₂, ⟨pc₁₂, hp₁₂, ⟨g, gv⟩⟩ | d⟩ := hSD u₁₁ (b80002af4_pc g₁₁) pre
  swap
  · exact ⟨t₁₂, Q₁₀.trans (p₁₁.trans q₁₂), Or.inr d⟩
  rw [x10] at g gv
  rw [x11, x12, J₁₁.val, N₁₁.val, F₁₁.val] at gv
  obtain ⟨M₁₂, F₁₂⟩ := M₁₁.growM hpre ⟨J₁₁.ok, J₁₁.val, fun x hx ↦ absurd hx (J₁₁.nd x)⟩ (le_refl _)
    (by omega) (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) g (fun x hx ↦ by
      rw [x11, x12] at hx
      rcases hx with hx | hx
      · exact (nb x hx).1
      · have := (fb x hx).1; omega) hnS (hp₁₂.reg .x2)
  rw [gv] at F₁₂
  exact ⟨t₁₂, Q₁₀.trans (p₁₁.trans q₁₂), Or.inl ⟨by rw [pc₁₂, returnAddress_eq, b80002af4_x1 g₁₁]; decide,
    M₁₂, F₁₂, r₁₁.pres hp₁₂⟩⟩

end Rv64Verifier.Proofs.Walk
