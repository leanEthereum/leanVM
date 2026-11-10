import Rv64Verifier.Proofs.Walk.R6I

/-!
# `walk`: a cell's `memory_if` counter

From `add_scaled`'s first call (`I1`, `0x80001c58`): `col(count, 0) += prod(flag, count, 1)`, moved
to `sp + 1024`, `prod(flag, count, 0)` into `sp + 2240` (`I2`, `0x80001cb4`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FormOk formOf formBuf flushesDeep OptAt)

/-- At `0x80001cb4`, `add_scaled`'s second call: the counter's first two terms at `sp + 1024`,
`prod(flag, count, 0)` at `sp + 2240`; `s2` = `sp + 2144`, `s10` = `ONE`'s address. -/
structure I2 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) (c : Nat) (F : LayoutMirror.FlushesRust)
    (h0 h1 h2 h3 h4 h5 h6 : Nat) : Prop where
  is : IS OI s u A k R Q B c F h0 h1 h2 h3
  x18 : u.getReg .x18 = s.getReg .x2 - 512
  x25 : u.getReg .x25 = BitVec.ofNat 64 (flagOf c)
  x26 : u.getReg .x26 = 0xa00000b0
  addr : SF u (s.getReg .x2 - 344) (LayoutMirror.prodRust 1 9 c) h3 h4
  cnt : SF u (s.getReg .x2 - 1632) ((LayoutMirror.colRust (65 + 13 * 1 + c) 0).add
    (LayoutMirror.prodRust (flagOf c) (65 + 13 * 1 + c) 1)) h4 h5
  p0 : SF u (s.getReg .x2 - 416) (LayoutMirror.prodRust (flagOf c) (65 + 13 * 1 + c) 0) h5 h6
  le : h3 ≤ h4 ∧ h4 ≤ h5 ∧ h5 ≤ h6 ∧ h6 ≤ heapNext u

set_option maxRecDepth 8192 in
theorem toI2 (hP : Rv64Verifier.Layout.ProdSpec) (hA : Rv64Verifier.Layout.AddScaledSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {c : Nat} {F : LayoutMirror.FlushesRust}
    {h0 h1 h2 h3 h4 h5 h6 : Nat} (hpre : WalkPre s)
    (h : I1 OI s u A k R Q B c F h0 h1 h2 h3 h4 h5 h6) (hc : c < 13) (hpc : u.pc = 0x80001c58) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001cb4 ∧ ∃ h7 h8,
      I2 OI s t A k R Q B c F h0 h1 h2 h3 h4 h7 h8) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have I := h.is.km.m.inv
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : u.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  obtain ⟨w₁, q₁, g₁⟩ := Sym.BlockSpec.reaches b80001c58_spec hpc (by
    rv_eval [h.x26]
    and_intros <;> valid_access hpre.stack.valid [hb1])
  have kw₁ := b80001c58_keeps g₁
  have m₁ := b80001c58_mem_same g₁
  have fr₁ := Rv64Verifier.Layout.DFrame.of_same m₁ (fun _ ↦ False)
  have S₁ := h.is.blk hpre fr₁ (fun _ h ↦ h.elim) (h.is.ir.keeps kw₁) (kw₁ .x2 (by decide))
  have hh := I.heap
  have le := h.le
  have le' := h.is.le
  have C₁ := h.col.frame fr₁ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh S₁.2.ge
  have P₁ := h.p1.frame fr₁ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh S₁.2.ge
  have A₁ := h.addr.frame fr₁ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh S₁.2.ge
  have oC := offV_of hpre (o := s.getReg .x2 - 1560) (Or.inr (Or.inl rfl))
  have oP := offV_of hpre (o := s.getReg .x2 - 416) (Or.inr (Or.inr (Or.inl rfl)))
  have oA := offV_of hpre (o := s.getReg .x2 - 344) (Or.inl rfl)
  have x26 := h.x26
  have a104 : u.getReg .x26 + 104 = s.getReg .x2 - 416 + 8 := by
    rw [x26]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a112 : u.getReg .x26 + 112 = s.getReg .x2 - 416 + 16 := by
    rw [x26]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨t₁, hr₁, ⟨hpc₁, hp₁, K₁, D₁, C₂, hv₁, mono₁, fr₂⟩ | hd⟩ := ascCall hA hpre S₁.1.km
    (b80001c58_pc g₁) (by rw [b80001c58_x10 g₁, e 1096 1560 (by decide)]) oC.1 oC.2.1 oP.2.1 C₁ P₁
    (len_one (by rw [P₁.val]; rfl)) le_rfl le.2.1
    (fun x hx ↦ by have := S₁.1.deep x hx; have := S₁.1.hB; omega) (by have := S₁.1.hB; omega)
    (by rw [b80001c58_x11 g₁, a104]; simp only [vecPtr, m₁]) (by rw [b80001c58_x12 g₁, a112]; simp only [vecLen, m₁])
    (b80001c58_x13 g₁)
  swap
  · exact ⟨t₁, q₁.trans hr₁, Or.inr hd⟩
  have R₁ := q₁.trans hr₁
  have hn : Rv64Verifier.Layout.addScaledStack ≤ 8736 := by decide
  have hw₁ : h4 ≤ heapNext w₁ := by rw [S₁.2]; omega
  have I₁ := S₁.1.km.m.inv
  have T₁ := S₁.1.call hpre oC fr₂ hn le.1 hw₁ K₁ D₁ (S₁.1.ir.pres hp₁) hv₁ mono₁
  have A₂ := SF.call' hpre I₁ A₁ fr₂ hn oC.2.1 oA.2.1 (by addr_omega [hb1]) le_rfl hw₁ hv₁ mono₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := K₁.m.inv.sp
  have e₁ (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t₁.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp₁ hNM
  -- the move to `sp + 1024`, the call `prod(flag, count, 0)`
  obtain ⟨w₂, q₂, g₂⟩ := Sym.BlockSpec.reaches b80001c80_spec
    (by rw [hpc₁, returnAddress_eq, b80001c58_x1 g₁]; decide) (by
      rv_eval [sp₁]
      and_intros <;> valid_access hpre.stack.valid [hb1])
  have fr₃ : Rv64Verifier.Layout.DFrame t₁ w₂ (Within · (s.getReg .x2 - 1632) 24) := by
    have := MemFrame.dframe (b80001c80_frame g₂ (by rw [sp₁]; addr_omega [hb1]))
    rwa [e₁ 1024 1632 (by decide)] at this
  have kw₂ := b80001c80_keeps g₂
  have S₂ := T₁.blk hpre fr₃ (fun a ha ↦ ⟨Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, hb1]),
    by simp only [Within] at ha; addr_omega [ha, hb1]⟩) (T₁.ir.keeps kw₂) (kw₂ .x2 (by decide))
  have hh₁ := hv₁
  have nb (lo hi : Nat) (hhi : hi ≤ heapNext t₁) : ∀ x, lo ≤ x.toNat → x.toNat < hi →
      ¬ Within x (s.getReg .x2 - 1632) 24 := fun x _ hx hw ↦ by
    have := hh₁.hi; simp only [Within, heapEnd] at hw this; simp only [heapNext] at hhi this
    addr_omega [hw, hx, hhi, this, hb1]
  have C₃ := C₂.move (o := s.getReg .x2 - 1632) fr₃
    (by rw [← e₁ 1024 1632 (by decide), b80001c80_m_x2_1024 g₂, e₁ 1096 1560 (by decide)])
    (by rw [show s.getReg .x2 - 1632 + 8 = t₁.getReg .x2 + 1032 by rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
          b80001c80_m_x2_1032 g₂, show s.getReg .x2 - 1560 + 8 = t₁.getReg .x2 + 1104 by
            rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show s.getReg .x2 - 1632 + 16 = t₁.getReg .x2 + 1040 by rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
          b80001c80_m_x2_1040 g₂, show s.getReg .x2 - 1560 + 16 = t₁.getReg .x2 + 1112 by
            rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (nb _ _ le_rfl) hh₁ S₂.2.ge
  have A₃ := A₂.frame fr₃ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
    (nb _ _ (by have := mono₁; omega)) (by addr_omega [hb1]) hh₁ S₂.2.ge
  have I₂ := S₂.1.km.m.inv
  have x25₁ : t₁.getReg .x25 = BitVec.ofNat 64 (flagOf c) := by
    rw [hp₁ .x25 (by decide), kw₁ .x25 (by decide)]; exact h.x25
  obtain ⟨t₂, hr₂, ⟨hpc₂, hp₂, K₂, D₂, nf₂, fv₂⟩ | hd⟩ := prodCall hP hpre S₂.1.km (b80001c80_pc g₂)
    (by rw [b80001c80_x10 g₂, e₁ 2240 416 (by decide)]) oP.1 oP.2.1
  swap
  · exact ⟨t₂, R₁.trans (q₂.trans hr₂), Or.inr hd⟩
  have R₂ := R₁.trans (q₂.trans hr₂)
  have hf13 : flagOf c < 2 ^ 64 := by unfold flagOf; split_ifs <;> omega
  rw [b80001c80_x11 g₂, b80001c80_x12 g₂, b80001c80_x13 g₂, x25₁, T₁.ir.x24,
    toNat_small (x := BitVec.ofNat 64 (flagOf c)) rfl hf13,
    toNat_small (x := BitVec.ofNat 64 (65 + 13 * 1 + c)) rfl (by omega)] at fv₂
  have hw₂ : h5 ≤ heapNext w₂ := by rw [S₂.2]; have := mono₁; omega
  have T₂ := S₂.1.call hpre oP (cw_frame nf₂.frame) (by decide) (by omega) le_rfl K₂ D₂
    (S₂.1.ir.pres hp₂) nf₂.heap nf₂.mono
  have oC' := offV_of hpre (o := s.getReg .x2 - 1632) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have A₄ := SF.call hpre I₂ A₃ nf₂.frame (by decide) oP.2.1 oA.2.1 (by addr_omega [hb1])
    (by omega) nf₂.heap nf₂.mono
  have C₄ := SF.call hpre I₂ C₃ nf₂.frame (by decide) oP.2.1 oC'.2.1 (by addr_omega [hb1])
    (by rw [S₂.2]) nf₂.heap nf₂.mono
  have P₄ := SF.ofNew nf₂ fv₂
  have hm₂ := nf₂.mono
  have e₂ := S₂.2
  refine ⟨t₂, R₂, Or.inl ⟨by rw [hpc₂, returnAddress_eq, b80001c80_x1 g₂]; decide,
    heapNext t₁, heapNext t₂, {
      is := T₂
      x18 := by
        rw [hp₂ .x18 (by decide), kw₂ .x18 (by decide), hp₁ .x18 (by decide), b80001c58_x18 g₁,
          e 2144 512 (by decide)]
      x25 := by rw [hp₂ .x25 (by decide), kw₂ .x25 (by decide)]; exact x25₁
      x26 := by
        rw [hp₂ .x26 (by decide), kw₂ .x26 (by decide), hp₁ .x26 (by decide), b80001c58_x26 g₁]
      addr := A₄
      cnt := C₄
      p0 := by rw [e₂] at P₄; exact P₄
      le := ⟨le.1, by omega, by omega, le_rfl⟩ }⟩⟩

end Rv64Verifier.Proofs.Walk
