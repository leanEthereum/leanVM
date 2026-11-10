import Rv64Verifier.Proofs.Walk.R6J

/-!
# `walk`: a cell's `memory_if` flush, its end

From `add_scaled`'s second call (`I2`, `0x80001cb4`): the counter completed and moved to
`sp + 952`, `constant(SEP_MEM)` into `sp + 2240`, the address copied to `sp + 2264`, then
`Flushes::counted(prefix, counter, count, &values)` and the block restoring `s2`, `s9`, to the
latch at `0x80001d60`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FormOk formOf formBuf flushesDeep OptAt)

theorem cellStep_if (F : LayoutMirror.FlushesRust) {c : Nat} (hc : c < 13) (h1 : 1 ≤ c) :
    cellStep 1 F c = F.counted [LayoutMirror.constantRust LayoutMirror.genRust,
      LayoutMirror.prodRust 1 9 c]
      (((LayoutMirror.colRust (65 + 13 * 1 + c) 0).add
        (LayoutMirror.prodRust (flagOf c) (65 + 13 * 1 + c) 1)).add
        (LayoutMirror.prodRust (flagOf c) (65 + 13 * 1 + c) 0)) (65 + 13 * 1 + c)
      (cellValues 1 c) := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  simp only [cellStep, LayoutMirror.keccakCellRust, cellLanesGetD _ hc]
  rfl

theorem formsAt2 (u : MachineState) (p : Word) :
    Rv64Verifier.Layout.formsAt u p 2 = [formOf u p, formOf u (p + 24)] := by
  have h0 : p + BitVec.ofNat 64 (24 * 0) = p := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [Rv64Verifier.Layout.formsAt, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, h0]
  rfl

set_option maxRecDepth 8192 in
theorem ifTail (hA : Rv64Verifier.Layout.AddScaledSpec) (hT : Rv64Verifier.Layout.TermSpec)
    (hCt : Rv64Verifier.Layout.CountedSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {c : Nat} {F : LayoutMirror.FlushesRust}
    {h0 h1 h2 h3 h4 h5 h6 : Nat} (hpre : WalkPre s)
    (h : I2 OI s u A k R Q B c F h0 h1 h2 h3 h4 h5 h6) (hc : c < 13) (hc1 : 1 ≤ c)
    (hpc : u.pc = 0x80001cb4) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001d60 ∧
      KM OI s t A k R Q B 1 (cellStep 1 F c) ∧ KR s t 1 c) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have I := h.is.km.m.inv
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : u.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have le := h.le
  have le' := h.is.le
  have hBh := h.is.hB
  -- `add_scaled(prod(flag, count, 0), ONE)` on the counter at `sp + 1024`
  obtain ⟨w₁, q₁, g₁⟩ := Sym.BlockSpec.reaches b80001cb4_spec hpc (by
    rv_eval [h.x18]
    and_intros <;> valid_access hpre.stack.valid [hb1])
  have kw₁ := b80001cb4_keeps g₁
  have m₁ := b80001cb4_mem_same g₁
  have fr₁ := Rv64Verifier.Layout.DFrame.of_same m₁ (fun _ ↦ False)
  have S₁ := h.is.blk hpre fr₁ (fun _ h ↦ h.elim) (h.is.ir.keeps kw₁) (kw₁ .x2 (by decide))
  have hh := I.heap
  have C₁ := h.cnt.frame fr₁ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh S₁.2.ge
  have P₁ := h.p0.frame fr₁ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh S₁.2.ge
  have A₁ := h.addr.frame fr₁ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh S₁.2.ge
  have oC := offV_of hpre (o := s.getReg .x2 - 1632) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have oP := offV_of hpre (o := s.getReg .x2 - 416) (Or.inr (Or.inr (Or.inl rfl)))
  have oA := offV_of hpre (o := s.getReg .x2 - 344) (Or.inl rfl)
  have oK := offV_of hpre (o := s.getReg .x2 - 1704) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have a104 : u.getReg .x18 + 104 = s.getReg .x2 - 416 + 8 := by
    rw [h.x18]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a112 : u.getReg .x18 + 112 = s.getReg .x2 - 416 + 16 := by
    rw [h.x18]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨t₁, hr₁, ⟨hpc₁, hp₁, K₁, D₁, C₂, hv₁, mono₁, fr₂⟩ | hd⟩ := ascCall hA hpre S₁.1.km
    (b80001cb4_pc g₁) (by rw [b80001cb4_x10 g₁, e 1024 1632 (by decide)]) oC.1 oC.2.1 oP.2.1 C₁ P₁
    (len_one (by rw [P₁.val]; rfl)) le_rfl le.2.1
    (fun x hx ↦ by have := S₁.1.deep x hx; omega) (by omega)
    (by rw [b80001cb4_x11 g₁, a104]; simp only [vecPtr, m₁])
    (by rw [b80001cb4_x12 g₁, a112]; simp only [vecLen, m₁]) (by rw [b80001cb4_x13 g₁, h.x26])
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
  -- the counter moved to `sp + 952`, `One` at `sp + 1096`, the call `term(One, GEN)`
  obtain ⟨w₂, q₂, g₂⟩ := Sym.BlockSpec.reaches b80001cd4_spec
    (by rw [hpc₁, returnAddress_eq, b80001cb4_x1 g₁]; decide) (by
      rv_eval [sp₁]
      and_intros <;> valid_access hpre.stack.valid [hb1])
  have fr₃ : Rv64Verifier.Layout.DFrame t₁ w₂ (Within · (s.getReg .x2 - 1704) 152) := by
    have := MemFrame.dframe (b80001cd4_frame g₂ (by rw [sp₁]; addr_omega [hb1]))
    rwa [e₁ 952 1704 (by decide)] at this
  have kw₂ := b80001cd4_keeps g₂
  have S₂ := T₁.blk hpre fr₃ (fun a ha ↦ ⟨Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, hb1]),
    by simp only [Within] at ha; addr_omega [ha, hb1]⟩) (T₁.ir.keeps kw₂) (kw₂ .x2 (by decide))
  have nb (lo hi : Nat) (hhi : hi ≤ heapNext t₁) : ∀ x, lo ≤ x.toNat → x.toNat < hi →
      ¬ Within x (s.getReg .x2 - 1704) 152 := fun x _ hx hw ↦ by
    have := hv₁.hi; simp only [Within, heapEnd] at hw this; simp only [heapNext] at hhi this
    addr_omega [hw, hx, hhi, this, hb1]
  have K₃ := C₂.move (o := s.getReg .x2 - 1704) fr₃
    (by rw [← e₁ 952 1704 (by decide), b80001cd4_m_x2_952 g₂, e₁ 1024 1632 (by decide)])
    (by rw [show s.getReg .x2 - 1704 + 8 = t₁.getReg .x2 + 960 by rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
          b80001cd4_m_x2_960 g₂, show s.getReg .x2 - 1632 + 8 = t₁.getReg .x2 + 1032 by
            rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show s.getReg .x2 - 1704 + 16 = t₁.getReg .x2 + 968 by rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
          b80001cd4_m_x2_968 g₂, show s.getReg .x2 - 1632 + 16 = t₁.getReg .x2 + 1040 by
            rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (nb _ _ le_rfl) hv₁ S₂.2.ge
  have A₃ := A₂.frame fr₃ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
    (nb _ _ (by have := mono₁; omega)) (by addr_omega [hb1]) hv₁ S₂.2.ge
  have z₂ : w₂.getMem (s.getReg .x2 - 1560) = 0 := by
    rw [← e₁ 1096 1560 (by decide)]; exact b80001cd4_m_x2_1096 g₂
  obtain ⟨t₂, hr₂, ⟨hpc₂, hp₂, K₂, D₂, nf₂, fv₂⟩ | hd⟩ := termCall hT hpre S₂.1.km (b80001cd4_pc g₂)
    (by rw [b80001cd4_x10 g₂, e₁ 2240 416 (by decide)]) oP.1 oP.2.1
    (by rw [b80001cd4_x11 g₂, e₁ 1096 1560 (by decide)]) (by simp only [InSlot]; addr_omega [hb1, hb3]) z₂
    (b80001cd4_x12 g₂) ⟨by decide, by decide, by decide⟩
  swap
  · exact ⟨t₂, R₁.trans (q₂.trans hr₂), Or.inr hd⟩
  have R₂ := R₁.trans (q₂.trans hr₂)
  have I₂ := S₂.1.km.m.inv
  rw [Rv64Verifier.Layout.eAt_gen (I₂.rodata hpre)] at fv₂
  have hw₂ : heapNext t₁ ≤ heapNext w₂ := S₂.2.ge
  have T₂ := S₂.1.call hpre oP (cw_frame nf₂.frame) (by decide) (by have := mono₁; omega) le_rfl K₂ D₂
    (S₂.1.ir.pres hp₂) nf₂.heap nf₂.mono
  have K₄ := SF.call hpre I₂ K₃ nf₂.frame (by decide) oP.2.1 oK.2.1 (by addr_omega [hb1])
    hw₂ nf₂.heap nf₂.mono
  have A₄ := SF.call hpre I₂ A₃ nf₂.frame (by decide) oP.2.1 oA.2.1 (by addr_omega [hb1])
    (by have := mono₁; omega) nf₂.heap nf₂.mono
  have G₄ := SF.ofNew nf₂ fv₂
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := K₂.m.inv.sp
  have e₂ (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t₂.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp₂ hNM
  have x26₂ : t₂.getReg .x26 = s.getReg .x2 - 512 := by
    rw [hp₂ .x26 (by decide), kw₂ .x26 (by decide), hp₁ .x26 (by decide), b80001cb4_x26 g₁, e 2144 512 (by decide)]
  -- the address copied to `sp + 2264`, the call `counted`
  obtain ⟨w₃, q₃, g₃⟩ := Sym.BlockSpec.reaches b80001d0c_spec
    (by rw [hpc₂, returnAddress_eq, b80001cd4_x1 g₂]; decide) (by
      rv_eval [sp₂, x26₂]
      and_intros <;> valid_access hpre.stack.valid [hb1])
  have fr₄ : Rv64Verifier.Layout.DFrame t₂ w₃ (Within · (s.getReg .x2 - 392) 24) := by
    have := MemFrame.dframe (b80001d0c_frame g₃ (by rw [sp₂]; addr_omega [hb1]))
    rwa [e₂ 2264 392 (by decide)] at this
  have kw₃ := b80001d0c_keeps g₃
  have S₃ := T₂.blk hpre fr₄ (fun a ha ↦ ⟨Or.inr (Or.inr (Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, hb1]))),
    by simp only [Within] at ha; addr_omega [ha, hb1]⟩) (T₂.ir.keeps kw₃) (kw₃ .x2 (by decide))
  have hv₂ := nf₂.heap
  have nb' (lo hi : Nat) (hhi : hi ≤ heapNext t₂) : ∀ x, lo ≤ x.toNat → x.toNat < hi →
      ¬ Within x (s.getReg .x2 - 392) 24 := fun x _ hx hw ↦ by
    have := hv₂.hi; simp only [Within, heapEnd] at hw this; simp only [heapNext] at hhi this
    addr_omega [hw, hx, hhi, this, hb1]
  have a26 (N M : Word) (hNM : N.toNat + M.toNat = 512) : t₂.getReg .x26 + N = s.getReg .x2 - M := by
    rw [x26₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hNM]
  have hm₂ := nf₂.mono
  have A₅ := A₄.move (o := s.getReg .x2 - 392) fr₄
    (by rw [← e₂ 2264 392 (by decide), b80001d0c_m_x2_2264 g₃, a26 168 344 (by decide)])
    (by rw [show s.getReg .x2 - 392 + 8 = t₂.getReg .x2 + 2272 by rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
          b80001d0c_m_x2_2272 g₃, a26 176 336 (by decide), show s.getReg .x2 - 344 + 8 = s.getReg .x2 - 336 by
            apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show s.getReg .x2 - 392 + 16 = t₂.getReg .x2 + 2280 by rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
          b80001d0c_m_x2_2280 g₃, a26 184 328 (by decide), show s.getReg .x2 - 344 + 16 = s.getReg .x2 - 328 by
            apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (nb' _ _ (by have := mono₁; omega)) hv₂ S₃.2.ge
  have K₅ := K₄.frame fr₄ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
    (nb' _ _ (by omega)) (by addr_omega [hb1]) hv₂ S₃.2.ge
  have G₅ := G₄.frame fr₄ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
    (nb' _ _ le_rfl) (by addr_omega [hb1]) hv₂ S₃.2.ge
  have I₃ := S₃.1.km.m.inv
  have hm : Rv64Verifier.Layout.countedStack ≤ 8736 := by decide
  have sF := slotW (n := 6) hpre I₃ (o := s.getReg .x2 - 1488) (by simp only [InSlot]; addr_omega [hb1, hb3]) hm
  have sPre := slotW (n := 6) hpre I₃ (o := s.getReg .x2 - 416) (by simp only [InSlot]; addr_omega [hb1, hb3]) hm
  have sK := slotW (n := 3) hpre I₃ (o := s.getReg .x2 - 1704) (by simp only [InSlot]; addr_omega [hb1, hb3]) hm
  have sV := slotW (n := 9) hpre I₃ (o := s.getReg .x2 - 224) (by simp only [InSlot]; addr_omega [hb1, hb3]) hm
  have a24 : s.getReg .x2 - 224 + 24 = s.getReg .x2 - 200 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a48 : s.getReg .x2 - 224 + 48 = s.getReg .x2 - 176 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have p24 : s.getReg .x2 - 416 + 24 = s.getReg .x2 - 392 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x10₃ : w₃.getReg .x10 = s.getReg .x2 - 1488 := by rw [b80001d0c_x10 g₃, e₂ 1168 1488 (by decide)]
  have x11₃ : w₃.getReg .x11 = s.getReg .x2 - 416 := by rw [b80001d0c_x11 g₃, e₂ 2240 416 (by decide)]
  have x12₃ : w₃.getReg .x12 = s.getReg .x2 - 1704 := by rw [b80001d0c_x12 g₃, e₂ 952 1704 (by decide)]
  have x14₃ : w₃.getReg .x14 = s.getReg .x2 - 224 := by rw [b80001d0c_x14 g₃, e₂ 2432 224 (by decide)]
  have x15₃ : (w₃.getReg .x15).toNat = 3 := by rw [b80001d0c_x15 g₃]; rfl
  have V := S₃.1
  have cpre : Rv64Verifier.Layout.CountedPre w₃ := {
    heap := I₃.heap
    stack := stk_sub hpre I₃ hm (by decide)
    self := by rw [x10₃]; exact sF.1
    ok := by rw [x10₃]; exact V.km.fl.ok
    selfFree := by rw [x10₃]; exact sF.2.1
    selfStack := by rw [x10₃]; exact sF.2.2
    rodata := I₃.rodata hpre
    pre := by rw [x11₃]; exact sPre.1
    preOk := by
      rw [x11₃]; intro i hi
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · simpa using G₅.ok
      · rw [show (24 * 1 : Nat) = 24 from rfl, show BitVec.ofNat 64 24 = (24 : Word) from rfl, p24]
        exact A₅.ok
    preFree := by rw [x11₃]; exact sPre.2.1
    preStack := by rw [x11₃]; exact sPre.2.2
    counter := by rw [x12₃]; exact sK.1
    counterOk := by rw [x12₃]; exact K₅.ok
    counterFree := by rw [x12₃]; exact sK.2.1
    counterStack := by rw [x12₃]; exact sK.2.2
    suf := by rw [x14₃, x15₃]; exact sV.1
    sufOk := by
      rw [x14₃, x15₃]; intro i hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · simpa using V.v0.ok
      · rw [show (24 * 1 : Nat) = 24 from rfl, show BitVec.ofNat 64 24 = (24 : Word) from rfl, a24]
        exact V.v1.ok
      · rw [show (24 * 2 : Nat) = 48 from rfl, show BitVec.ofNat 64 48 = (48 : Word) from rfl, a48]
        exact V.v2.ok
    sufFree := by rw [x14₃, x15₃]; exact sV.2.1
    sufStack := by rw [x14₃, x15₃]; exact sV.2.2 }
  obtain ⟨t₃, hr₃, ⟨hpc₃, hp₃, g, gv⟩ | hd⟩ := hCt w₃ (b80001d0c_pc g₃) cpre
  swap
  · exact ⟨t₃, R₂.trans (q₃.trans hr₃), Or.inr hd⟩
  rw [x10₃] at g gv
  rw [x11₃, x12₃, x14₃, x15₃, b80001d0c_x13 g₃, T₂.ir.x24, formsAt2, formsAt3, p24, a24, a48,
    G₅.val, A₅.val, K₅.val, V.v0.val, V.v1.val, V.v2.val, V.km.fl.val,
    toNat_small (x := BitVec.ofNat 64 (65 + 13 * 1 + c)) rfl (by omega)] at gv
  have K₆ := KM.grow hpre V.km g hm (hp₃ .x2 (by decide)) gv
  obtain ⟨w₄, q₄, g₄⟩ := Sym.BlockSpec.reaches b80001d54_spec
    (by rw [hpc₃, returnAddress_eq, b80001d0c_x1 g₃]; decide) (by rv_eval [])
  have kw₄ := b80001d54_keeps g₄
  have K₇ := KM.scr hpre K₆ (Rv64Verifier.Layout.DFrame.of_same (b80001d54_mem_same g₄) (fun _ ↦ False))
    (fun _ h ↦ h.elim) (kw₄ .x2 (by decide))
  have ir := (V.ir.pres hp₃).keeps kw₄
  refine ⟨w₄, R₂.trans (q₃.trans (hr₃.trans q₄)), Or.inl ⟨b80001d54_pc g₄, ?_, ?_⟩⟩
  · rw [cellStep_if F hc hc1]; exact K₇.1
  · exact ⟨ir.x8, ir.x9, b80001d54_x18 g₄, ir.x19, ir.x20, ir.x21, ir.x22, ir.x23,
      by rw [b80001d54_x25 g₄, hp₃ .x2 (by decide), kw₃ .x2 (by decide)]; exact spAdd hpre sp₂ (by decide),
      by rw [kw₄ .x26 (by decide), hp₃ .x26 (by decide), kw₃ .x26 (by decide)]; exact x26₂, ir.x27⟩

end Rv64Verifier.Proofs.Walk
