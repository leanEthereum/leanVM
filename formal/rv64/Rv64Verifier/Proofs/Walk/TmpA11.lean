import Rv64Verifier.Proofs.Walk.Fill11

/-!
# `walk`: `vec![h; w]` for `h ≠ 0` (R11)

`try_allocate_in(w)`, the `Vec` `{w, T, 0}` at `sp + 1728`, `reserve(w)` (room enough), the fill
loop.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

set_option maxRecDepth 8192 in
theorem kapTmpA (hTA : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x8000d628)
    {OI : MachineState → Word → List (List Opening) → Prop}
    {s u c : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo lo2 i : Nat}
    (hpre : WalkPre s) (h : Kap11 OI s u A k R Q B lo lo2 i) (hc : c.pc = 0x80003100)
    (mc : ∀ a, c.getMem a = u.getMem a)
    (kc : ∀ r ∈ ([.x2, .x8, .x9, .x19, .x20, .x22, .x27] : List Reg), c.getReg r = u.getReg r)
    (x10 : c.getReg .x10 = s.getReg .x2 - 928)
    (x21 : c.getReg .x21 = BitVec.ofNat 64 ((hts A).getD i 0))
    (x24 : c.getReg .x24 = BitVec.ofNat 64 (tableWidthsRust.getD i 0)) :
    ∃ t, Reaches Image.code c t ∧ (Dead Image.code t ∨
      (t.pc = 0x800031a4 ∧ ∃ T, Tmp11 OI s t A k R Q B lo lo2 i T)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hi := h.lt
  have hk := kapPre_ne A k (le_of_lt hi)
  have hw := width_pos hi
  set w := tableWidthsRust.getD i 0 with hwdef
  have hhi := h.keep.at11.base.inv.heap.hi
  have spc : c.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [kc .x2 (by decide)]; exact h.keep.at11.base.inv.sp
  obtain ⟨c₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003100_spec hc (by rv_eval [])
  have m₁ (a : Word) : c₁.getMem a = u.getMem a := by rw [b80003100_mem_same h₁, mc]
  have k₁ := b80003100_keeps h₁
  have K₁ := h.keep.same hpre m₁ (by rw [k₁ .x2 (by decide), kc .x2 (by decide)])
  have kv₁ := h.kv.same hpre hk hhi m₁
  obtain ⟨t, hr, hd | ⟨hpct, hp, K', kv', hP, hC, hok⟩⟩ := tryCall hTA hpre hk K₁ kv₁
    (b80003100_pc h₁) (by rw [k₁ .x10 (by decide)]; exact x10) hw.2
    (by rw [b80003100_x11 h₁]; exact x24) (b80003100_x13 h₁) (b80003100_x14 h₁) (by omega)
  · exact ⟨t, hr₁.trans hr, Or.inl hd⟩
  have pct : t.pc = 0x80003118 := by rw [hpct, returnAddress_eq, b80003100_x1 h₁]; decide
  have spt : t.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [hp .x2 (by decide), k₁ .x2 (by decide)]; exact spc
  obtain ⟨t₁, hrt₁, ht₁⟩ := Sym.BlockSpec.reaches b80003118_spec pct (by
    rv_eval [spt]; simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have e1728 : t.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [spt]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  by_cases hz : t.getMem (s.getReg .x2 - 928) = 0
  swap
  · have pc' := b80003118_pc_not_taken ht₁ (by rw [e1728]; exact hz)
    obtain ⟨t', hrt', ht'⟩ := Sym.BlockSpec.reaches b80003120_spec pc' (by rv_eval [])
    exact ⟨t', hr₁.trans (hr.trans (hrt₁.trans hrt')), Or.inl (trapAt (b80003120_pc ht'))⟩
  have pc₁ := b80003118_pc_taken ht₁ (by rw [e1728]; exact hz)
  obtain ⟨o8, o1, o2, o3, -⟩ := hok hz
  set T := t.getMem (s.getReg .x2 - 912) with hT
  have m₁t := b80003118_mem_same ht₁
  have k₁t := b80003118_keeps ht₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁t .x2 (by decide)]; exact spt
  obtain ⟨t₂, hrt₂, ht₂⟩ := Sym.BlockSpec.reaches b80003124_spec pc₁ (by
    rv_eval [sp₁]; simp only [Sym.validAccess_eight]; and_intros <;> addr_omega [hb1, hb2, hb3])
  have fr₂ := b80003124_frame ht₂ (by rw [sp₁]; addr_omega [hb1])
  have e1728' : t₁.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [e1728'] at fr₂
  have k₂ := b80003124_keeps ht₂
  have w0 : t₂.getMem (s.getReg .x2 - 928) = BitVec.ofNat 64 w := by
    rw [← e1728', b80003124_m_x2_1728 ht₂, sp₁]; rv_eval [m₁t]; exact o8
  have w8 : t₂.getMem (s.getReg .x2 - 920) = T := by
    have := b80003124_m_x2_1736 ht₂; rw [sp₁] at this; rv_eval [m₁t] at this; exact this
  have w16 : t₂.getMem (s.getReg .x2 - 912) = 0 := by
    have := b80003124_m_x2_1744 ht₂; rw [sp₁] at this; rv_eval [] at this; exact this
  have pc₂ := b80003124_pc ht₂
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₂ .x2 (by decide)]; exact sp₁
  have x10₂ : t₂.getReg .x10 = s.getReg .x2 - 928 := by rw [b80003124_x10 ht₂, e1728']
  have x11₂ : t₂.getReg .x11 = BitVec.ofNat 64 w := by
    rw [b80003124_x11 ht₂, k₁t .x24 (by decide), hp .x24 (by decide), k₁ .x24 (by decide)]
    exact x24
  have hwN : (BitVec.ofNat 64 w).toNat = w := by rw [BitVec.toNat_ofNat]; omega
  have e16 : s.getReg .x2 - 928 + 16 = s.getReg .x2 - 912 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨t₃, hrt₃, ⟨hpct₃, hp₃, -, m₃⟩ | hd⟩ := hRF t₂ pc₂ ⟨by
      rw [x10₂]; exact validMemRange_of (by addr_omega [hb1, hb3]) (Or.inr ⟨by addr_omega [hb1],
        by addr_omega [hb1, hb2]⟩), by
      rw [x10₂, x11₂]; simp only [vecLen, vecCap]; rw [e16, w16, w0, hwN]; simp⟩
  swap
  · exact ⟨t₃, hr₁.trans (hr.trans (hrt₁.trans (hrt₂.trans hrt₃))), Or.inl hd⟩
  have pc₃ : t₃.pc = 0x80003148 := by rw [hpct₃, returnAddress_eq, b80003124_x1 ht₂]; decide
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := by rw [hp₃ .x2 (by decide)]; exact sp₂
  obtain ⟨f₀, hrf, hf⟩ := Sym.BlockSpec.reaches b80003148_spec pc₃ (by
    rv_eval [sp₃]; simp only [Sym.validAccess_eight]; and_intros <;> addr_omega [hb1, hb2, hb3])
  have mf := b80003148_mem_same hf
  have kf := b80003148_keeps hf
  have rg (r : Reg) (hr : r ∈ ([.x8, .x9, .x19, .x20, .x21, .x22, .x24, .x27] : List Reg)) :
      f₀.getReg r = c.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [kf _ (by decide), hp₃ _ (by decide), k₂ _ (by decide), k₁t _ (by decide), hp _ (by decide),
        k₁ _ (by decide)]
  have x10f : f₀.getReg .x10 = 0 := by rw [b80003148_x10 hf, sp₃]; rv_eval [m₃, w16]
  have x11f : f₀.getReg .x11 = T + BitVec.ofNat 64 (8 * 0) := by
    rw [b80003148_x11 hf, sp₃]; rv_eval [m₃, w8, w16]; simp
  have hhc := K₁.at11.base.inv.heap.hi
  obtain ⟨b1, b2, b3, b4⟩ := kv'.bounds hk
  rw [hP] at b1 b2
  rw [hP, hC] at b3
  have hht := K'.at11.base.inv.heap.hi
  simp only [heapEnd, heapStart] at hht hhc b2
  have hT1 : 0x20000000 ≤ T.toNat := by omega
  have hT2 : T.toNat + 8 * w ≤ 0x78000000 := by omega
  have x12f : f₀.getReg .x12 = T + BitVec.ofNat 64 (8 * w) - 8 := by
    rw [b80003148_x12 hf, sp₃, hp₃ .x24 (by decide), k₂ .x24 (by decide), k₁t .x24 (by decide),
      hp .x24 (by decide), k₁ .x24 (by decide), x24]
    rv_eval [m₃, w8, w16]
    apply BitVec.eq_of_toNat_eq; addr_omega [hT1, hT2, hw]
  obtain ⟨tf, hrtf, pcf, regsf, x24f, frf, valsf⟩ := fillLoop o1 hT1 hT2 x12f (w - 2 - 0) 0 f₀ rfl
    ⟨b80003148_pc hf, by omega, x11f, fun _ _ ↦ rfl, Layout.DFrame.refl _ _,
      fun j hj ↦ absurd hj (Nat.not_lt_zero _)⟩
  have frT : Layout.DFrame t tf fun a ↦ Within a (s.getReg .x2 - 928) 24 ∨ Within a T (8 * w) :=
    fun a ha hw8 ↦ by
      rw [frf a (fun x hx h ↦ ha x hx (Or.inr h)) hw8, mf, m₃,
        (MemFrame.dframe fr₂) a (fun x hx h ↦ ha x hx (Or.inl h)) hw8, m₁t]
  have hnf : heapNext tf = heapNext t := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (frT nextAddr (fun y hy hw ↦ by
      simp only [Within, nextAddr] at hy hw
      rcases hw with hw | hw <;> addr_omega [hy, hw, hb1, hT1, hT2]) (by decide))
  have hvf : HeapOk tf := ⟨hnf ▸ K'.at11.base.inv.heap.lo, hnf ▸ K'.at11.base.inv.heap.hi⟩
  have spf : tf.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [regsf .x2 (by decide), kf .x2 (by decide)]; exact sp₃
  have hfr := kv'.fresh
  rw [hP] at hfr
  have Kf := K'.keep hpre frT (fun a ha ↦ by
      rcases ha with ha | ha
      · simp only [Within] at ha
        refine Or.inl ⟨by addr_omega [ha, hb1], by addr_omega [ha, hb1], ?_⟩
        simp only [hdrs, Within]; addr_omega [ha, hb1]
      · simp only [Within] at ha
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by rw [hnf]; omega⟩))) hvf hnf.ge
    (spf.trans (hp .x2 (by decide) |>.trans (k₁ .x2 (by decide)) |>.trans spc).symm)
  have hhdr : ∀ x, Within x (s.getReg .x2 - 1344) 24 →
      ¬ (Within x (s.getReg .x2 - 928) 24 ∨ Within x T (8 * w)) := fun x hx hw ↦ by
    simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, hT1, hT2]
  have kvf := kv'.keep hk frT hhdr (fun x hx hw ↦ by
      simp only [kapBuf, Within] at hx hw; rw [hP, hC] at hx
      rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, b2, b3, hht, o2])
    (by addr_omega [hb1]) K'.at11.base.inv.heap.hi hnf.ge
  have g (o : Nat) (ho : o + 8 ≤ 24) : tf.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 o) =
      t.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 o) :=
    frT _ (fun x hx ↦ hhdr x (by addr_omega [hx, ho, hb1])) (by addr_omega [ho, hb1])
  have e1 : vecPtr tf (s.getReg .x2 - 1344) = vecPtr c₁ (s.getReg .x2 - 1344) :=
    (g 8 (by decide)).trans hP
  have e2 : vecCap tf (s.getReg .x2 - 1344) = vecCap c₁ (s.getReg .x2 - 1344) := by
    have := g 0 (by decide); simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    exact this.trans hC
  refine ⟨tf, hr₁.trans (hr.trans (hrt₁.trans (hrt₂.trans (hrt₃.trans (hrf.trans hrtf))))),
    Or.inr ⟨pcf, T, {
      keep := Kf
      kv := kvf
      lt := hi
      x8 := by rw [regsf .x8 (by decide), rg .x8 (by decide), kc .x8 (by decide)]; exact h.x8
      x9 := by rw [regsf .x9 (by decide), rg .x9 (by decide), kc .x9 (by decide)]; exact h.x9
      x19 := by rw [regsf .x19 (by decide), rg .x19 (by decide), kc .x19 (by decide)]; exact h.x19
      x20 := by rw [regsf .x20 (by decide), rg .x20 (by decide), kc .x20 (by decide)]; exact h.x20
      x22 := by rw [regsf .x22 (by decide), rg .x22 (by decide), kc .x22 (by decide)]; exact h.x22
      x27 := by rw [regsf .x27 (by decide), rg .x27 (by decide), kc .x27 (by decide)]; exact h.x27
      x24 := by rw [x24f, x10f, rg .x24 (by decide)]; exact (BitVec.add_zero _).trans x24
      x25 := by rw [regsf .x25 (by decide), b80003148_x25 hf, sp₃]; rv_eval [m₃, w8]
      tal := o1
      tlo := by rw [e1, e2]; exact o2
      thi := by rw [hnf]; exact o3
      tvals := fun j hj ↦ by rw [valsf j hj, rg .x21 (by decide)]; exact x21 }⟩⟩

end Rv64Verifier.Proofs.Walk
