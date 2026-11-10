import Rv64Verifier.Proofs.Walk.R9C

/-!
# `walk`: R9, the tables' copies

`r9`: from `AtR9` (the first `memcpy`, `0x800126e4`) to `AtR10` (`0x80002e40`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

set_option maxRecDepth 8192 in
/-- **R9**: the six tables copied into `Bb`, the opcodes stored, to `AtR10`. -/
theorem r9 (hMC : MemcpySpec 0x800126e4)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} (hpre : WalkPre s)
    (h : AtR9 OI s u A k R Q B Bb) :
    ∃ t, Reaches Image.code u t ∧ (AtR10 OI s t A k R Q Bb ∨ Dead Image.code t) := by
  have M₀ := h.m
  obtain ⟨b1, b2, b3, -⟩ := M₀.bb
  have hu := M₀.m.inv.heap.hi
  obtain ⟨-, q2, q3, -⟩ := M₀.m.bufQ
  have hs := hpre.heap.lo
  simp only [heapEnd, heapStart, heapNext] at hu hs b3 q2
  have hBb : Bb.toNat + 480 ≤ 0x78000000 := by omega
  have hB0 : 0x20000000 ≤ Bb.toNat := by omega
  have hmB : Mapped Bb 480 := Or.inl ⟨by omega, by omega⟩
  have vB (c : Nat) (hc : c + 8 ≤ 480) (hc8 : c % 8 = 0) (x : Word) (hx : x = Bb + BitVec.ofNat 64 c) :
      Sym.validAccess 8 x = true := by
    have : x.toNat = Bb.toNat + c := by
      rw [hx, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact Mapped.valid8 hmB (by omega) (by omega) (by omega)
  have R₀ : R9R s u Bb := ⟨h.x8, h.x9, h.x18, h.x19, h.x20, h.x21, h.x22, h.x27⟩
  -- XOR
  obtain ⟨t₁, r₁, ⟨pc₁, hp₁, M₁, C₁, -⟩ | d⟩ := cpyC (n := 0) (o := s.getReg .x2 - 1632) hMC hpre M₀ (Cp.zero u _ _ _) (by decide)
    (by rw [tl_zero]; simp) h.pc (by rw [h.x10]; simp) h.x11 h.x12
  swap
  · exact ⟨t₁, r₁, Or.inr d⟩
  have R₁ := R₀.pres hp₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := M₁.m.inv.sp
  obtain ⟨v₁, q₁, g₁⟩ := Sym.BlockSpec.reaches b80002dbc_spec
    (by rw [pc₁, returnAddress_eq, h.x1]; decide) (by
      rv_eval [R₁.x18]; exact vB 72 (by omega) (by omega) _ rfl)
  obtain ⟨M₁', C₁', -⟩ := opC (n := 0) hpre M₁ C₁ (by decide)
    (by have := (b80002dbc_frame g₁ (by rw [R₁.x18]; omega)).dframe; rw [R₁.x18] at this; exact this)
    (by have := b80002dbc_m_x18_72 g₁; rw [R₁.x18] at this; exact this) (b80002dbc_keeps g₁ .x2 (by decide))
  have R₁' := R₁.keeps (b80002dbc_keeps g₁)
  -- MUL
  obtain ⟨t₂, r₂, ⟨pc₂, hp₂, M₂, C₂, -⟩ | d⟩ := cpyC (n := 1) (o := s.getReg .x2 - 1560) hMC hpre M₁' C₁' (by decide)
    (by rw [tl_one]; simp) (b80002dbc_pc g₁) (by rw [b80002dbc_x10 g₁, R₁.x18]; rfl)
    (by rw [b80002dbc_x11 g₁]; exact spAdd hpre sp₁ (N := 1096) (M := 1560) (by decide))
    (b80002dbc_x12 g₁)
  swap
  · exact ⟨t₂, r₁.trans (q₁.trans r₂), Or.inr d⟩
  have R₂ := R₁'.pres hp₂
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := M₂.m.inv.sp
  obtain ⟨v₂, q₂, g₂⟩ := Sym.BlockSpec.reaches b80002dd4_spec
    (by rw [pc₂, returnAddress_eq, b80002dbc_x1 g₁]; decide) (by
      rv_eval [R₂.x18]; exact vB 152 (by omega) (by omega) _ rfl)
  obtain ⟨M₂', C₂', -⟩ := opC (n := 1) hpre M₂ C₂ (by decide)
    (by have := (b80002dd4_frame g₂ (by rw [R₂.x18]; omega)).dframe; rw [R₂.x18] at this; exact this)
    (by have := b80002dd4_m_x18_152 g₂; rw [R₂.x18, R₂.x19] at this; exact this)
    (b80002dd4_keeps g₂ .x2 (by decide))
  have R₂' := R₂.keeps (b80002dd4_keeps g₂)
  -- SET
  obtain ⟨t₃, r₃, ⟨pc₃, hp₃, M₃, C₃, -⟩ | d⟩ := cpyC (n := 2) (o := s.getReg .x2 - 1488) hMC hpre M₂' C₂' (by decide)
    (by rw [tl_two]; simp) (b80002dd4_pc g₂) (by rw [b80002dd4_x10 g₂, R₂.x18]; rfl)
    (by rw [b80002dd4_x11 g₂]; exact spAdd hpre sp₂ (N := 1168) (M := 1488) (by decide))
    (b80002dd4_x12 g₂)
  swap
  · exact ⟨t₃, r₁.trans (q₁.trans (r₂.trans (q₂.trans r₃))), Or.inr d⟩
  have R₃ := R₂'.pres hp₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := M₃.m.inv.sp
  obtain ⟨v₃, q₃, g₃⟩ := Sym.BlockSpec.reaches b80002dec_spec
    (by rw [pc₃, returnAddress_eq, b80002dd4_x1 g₂]; decide) (by
      rv_eval [R₃.x18]; exact vB 232 (by omega) (by omega) _ rfl)
  obtain ⟨M₃', C₃', -⟩ := opC (n := 2) hpre M₃ C₃ (by decide)
    (by have := (b80002dec_frame g₃ (by rw [R₃.x18]; omega)).dframe; rw [R₃.x18] at this; exact this)
    (by have := b80002dec_m_x18_232 g₃; rw [R₃.x18, R₃.x22] at this; exact this)
    (b80002dec_keeps g₃ .x2 (by decide))
  have R₃' := R₃.keeps (b80002dec_keeps g₃)
  -- DEREF
  obtain ⟨t₄, r₄, ⟨pc₄, hp₄, M₄, C₄, -⟩ | d⟩ := cpyC (n := 3) (o := s.getReg .x2 - 512) hMC hpre M₃' C₃' (by decide)
    (by rw [tl_three]; simp) (b80002dec_pc g₃) (by rw [b80002dec_x10 g₃, R₃.x18]; rfl)
    (by rw [b80002dec_x11 g₃]; exact spAdd hpre sp₃ (N := 2144) (M := 512) (by decide))
    (b80002dec_x12 g₃)
  swap
  · exact ⟨t₄, r₁.trans (q₁.trans (r₂.trans (q₂.trans (r₃.trans (q₃.trans r₄))))), Or.inr d⟩
  have R₄ := R₃'.pres hp₄
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 2656 := M₄.m.inv.sp
  obtain ⟨v₄, q₄, g₄⟩ := Sym.BlockSpec.reaches b80002e08_spec
    (by rw [pc₄, returnAddress_eq, b80002dec_x1 g₃]; decide) (by
      rv_eval [R₄.x18]; exact vB 312 (by omega) (by omega) _ rfl)
  obtain ⟨M₄', C₄', -⟩ := opC (n := 3) hpre M₄ C₄ (by decide)
    (by have := (b80002e08_frame g₄ (by rw [R₄.x18]; omega)).dframe; rw [R₄.x18] at this; exact this)
    (by have := b80002e08_m_x18_312 g₄; rw [R₄.x18] at this; exact this)
    (b80002e08_keeps g₄ .x2 (by decide))
  have R₄' := R₄.keeps (b80002e08_keeps g₄)
  -- JUMP
  obtain ⟨t₅, r₅, ⟨pc₅, hp₅, M₅, C₅, -⟩ | d⟩ := cpyC (n := 4) (o := s.getReg .x2 - 928) hMC hpre M₄' C₄' (by decide)
    (by rw [tl_four]; simp) (b80002e08_pc g₄) (by rw [b80002e08_x10 g₄, R₄.x18]; rfl)
    (by rw [b80002e08_x11 g₄]; exact spAdd hpre sp₄ (N := 1728) (M := 928) (by decide))
    (b80002e08_x12 g₄)
  swap
  · exact ⟨t₅, r₁.trans (q₁.trans (r₂.trans (q₂.trans (r₃.trans (q₃.trans (r₄.trans (q₄.trans r₅))))))),
      Or.inr d⟩
  have R₅ := R₄'.pres hp₅
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 2656 := M₅.m.inv.sp
  obtain ⟨v₅, q₅, g₅⟩ := Sym.BlockSpec.reaches b80002e24_spec
    (by rw [pc₅, returnAddress_eq, b80002e08_x1 g₄]; decide) (by
      rv_eval [R₅.x18]; exact vB 392 (by omega) (by omega) _ rfl)
  obtain ⟨M₅', C₅', -⟩ := opC (n := 4) hpre M₅ C₅ (by decide)
    (by have := (b80002e24_frame g₅ (by rw [R₅.x18]; omega)).dframe; rw [R₅.x18] at this; exact this)
    (by have := b80002e24_m_x18_392 g₅; rw [R₅.x18] at this; exact this)
    (b80002e24_keeps g₅ .x2 (by decide))
  have R₅' := R₅.keeps (b80002e24_keeps g₅)
  -- KECCAK
  obtain ⟨t₆, r₆, ⟨pc₆, hp₆, M₆, C₆, -⟩ | d⟩ := cpyC (n := 5) (o := s.getReg .x2 - 1704) hMC hpre M₅' C₅' (by decide)
    (by rw [tl_five]; simp) (b80002e24_pc g₅) (by rw [b80002e24_x10 g₅, R₅.x18]; rfl)
    (by rw [b80002e24_x11 g₅]; exact spAdd hpre sp₅ (N := 952) (M := 1704) (by decide))
    (b80002e24_x12 g₅)
  swap
  · exact ⟨t₆, r₁.trans (q₁.trans (r₂.trans (q₂.trans (r₃.trans (q₃.trans (r₄.trans (q₄.trans
      (r₅.trans (q₅.trans r₆))))))))), Or.inr d⟩
  exact ⟨t₆, r₁.trans (q₁.trans (r₂.trans (q₂.trans (r₃.trans (q₃.trans (r₄.trans (q₄.trans
      (r₅.trans (q₅.trans r₆))))))))),
    Or.inl (atR10_of M₆ C₆ (R₅'.pres hp₆) (by rw [pc₆, returnAddress_eq, b80002e24_x1 g₅]; decide))⟩

end Rv64Verifier.Proofs.Walk
