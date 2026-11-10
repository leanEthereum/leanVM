import Rv64Verifier.Proofs.Walk.Kap11

/-!
# `walk`: `kappas`' head (R11), from `0x80003038` to the loop's header

The bound on `sp + 152` (zero), `alloc(8, 48)`, the six framework kappas, `kappas` at `sp + 1312`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem ofNat_add6 (h : Nat) :
    BitVec.ofNat 64 h + 6 = BitVec.ofNat 64 (h + 6) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : (6 : Word).toNat = 6 := rfl
  omega

set_option maxRecDepth 8192 in
/-- From `0x80003038` to `kappas`' loop header, no table done. -/
theorem r11head (hAS : AllocSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo : Nat} (hpre : WalkPre s)
    (hpc : u.pc = 0x80003038) (h : AtR11 OI s u A k R Q B lo) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = 0x800030c8 ∧ Kap11 OI s t A k R Q B lo (heapNext u) 0)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have K0 := h.keep11
  have H := h.base
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := H.inv.sp
  obtain ⟨-, s136, s152, -, sQ, sB⟩ := H.slots
  obtain ⟨-, -, -, -, -, -, s144, s160, -⟩ := H.spills
  have hQ := H.bufQ
  have hl := H.loLe
  have hhu := H.inv.heap.hi
  have hs0 := hpre.heap.lo
  have hmo := H.inv.mono
  simp only [heapEnd, heapStart] at hhu hs0
  -- the bound
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003038_spec hpc (by
    rv_eval [sp]; simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have pc₁ := b80003038_pc_taken h₁ (by rw [sp]; rv_eval [s152]; decide)
  have m₁ := b80003038_mem_same h₁
  have k₁ := b80003038_keeps h₁
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide)]; exact sp
  -- `alloc(8, 48)`
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003048_spec pc₁ (by
    rv_eval [sp₁, m₁, sQ]
    simp only [Sym.validAccess_eight]
    and_intros <;> addr_omega [hb1, hb2, hb3, hQ, hl, hhu, hs0])
  have m₂ (a : Word) : u₂.getMem a = u.getMem a := by rw [b80003048_mem_same h₂, m₁]
  have k₂ := b80003048_keeps h₂
  have hn₂ : heapNext u₂ = heapNext u := by simp only [heapNext, m₂]
  have x18₂ : u₂.getReg .x18 = BitVec.ofNat 64 ((hts A).getD 5 0) := by
    rw [b80003048_x18 h₂, sp₁]
    rv_eval [m₁, sQ]
    exact H.heights 5 (by decide)
  have preA : AllocPre u₂ := ⟨⟨hn₂ ▸ H.inv.heap.lo, hn₂ ▸ H.inv.heap.hi⟩, by
    rw [b80003048_x10 h₂]; decide⟩
  obtain ⟨t₂, hrt₂, ⟨hpct₂, hp₂, postA⟩ | hd⟩ := hAS.call (Reaches.refl u₂) (b80003048_pc h₂) preA
  swap
  · exact ⟨t₂, hr₁.trans (hr₂.trans hrt₂), Or.inl hd⟩
  have hal := postA.aligned
  have hab := postA.above
  have hnx := postA.next
  rw [b80003048_x10 h₂] at hal
  rw [b80003048_x11 h₂] at hnx
  have e8 : (8 : Word).toNat = 8 := rfl
  have e48 : (48 : Word).toNat = 48 := rfl
  rw [e8] at hal
  rw [e48] at hnx
  rw [hn₂] at hab
  set F := t₂.getReg .x10 with hF
  have hht₂ := postA.heap.hi
  simp only [heapEnd] at hht₂
  have hFhi : F.toNat + 48 ≤ 2013265920 := by rw [← hnx]; exact hht₂
  have mt₂ (a : Word) (ha : a ≠ nextAddr) : t₂.getMem a = u.getMem a := by rw [postA.mem a ha, m₂]
  have frA : Layout.DFrame u t₂ (Within · nextAddr 8) := fun a ha _ ↦
    mt₂ a fun he ↦ ha a ⟨le_refl _, by omega⟩ (by rw [he]; simp only [Within]; omega)
  have hnA : heapNext u ≤ heapNext t₂ := by rw [hnx]; omega
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [hp₂ .x2 (by decide), k₂ .x2 (by decide)]; exact sp₁
  have K₂ := K0.keep hpre frA (fun a ha ↦ Or.inr (Or.inr (Or.inl ha))) postA.heap hnA (sp₂.trans sp.symm)
  -- the framework kappas
  have pc₂ : t₂.pc = 0x80003060 := by rw [hpct₂, returnAddress_eq, b80003048_x1 h₂]; decide
  have nS (a : Word) (h1 : (s.getReg .x2 - 2656).toNat ≤ a.toNat) : a ≠ nextAddr := fun he ↦ by
    rw [he] at h1; simp only [nextAddr] at h1; addr_omega [h1, hb1]
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80003060_spec pc₂ (by
    rv_eval [sp₂]; simp only [Sym.validAccess_eight]; and_intros <;> addr_omega [hb1, hb2, hb3])
  have pc₃ := b80003060_pc_taken h₃ (fun he ↦ by
    have := congrArg BitVec.toNat he; rw [← hF] at this
    have h0 : (0 : Word).toNat = 0 := rfl
    omega)
  have m₃ := b80003060_mem_same h₃
  have k₃ := b80003060_keeps h₃
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₃ .x2 (by decide)]; exact sp₂
  have rd (a : Word) (h1 : (s.getReg .x2 - 2656).toNat ≤ a.toNat) : t₂.getMem a = u.getMem a :=
    mt₂ _ (nS _ h1)
  have x10₃ : u₃.getReg .x10 = F := k₃ .x10 (by decide)
  have x11₃ : u₃.getReg .x11 = lmOf A := by
    rw [b80003060_x11 h₃, sp₂]; rv_eval []; rw [rd _ (by addr_omega [hb1])]; exact s144
  have x22₃ : u₃.getReg .x22 = 6 := by
    rw [b80003060_x22 h₃, sp₂]; rv_eval []; rw [rd _ (by addr_omega [hb1])]; exact s136
  have x23₃ : u₃.getReg .x23 = BitVec.ofNat 64 (k - 4) := by
    rw [b80003060_x23 h₃, sp₂]; rv_eval []; rw [rd _ (by addr_omega [hb1])]; exact s160
  have x18₃ : u₃.getReg .x18 = BitVec.ofNat 64 ((hts A).getD 5 0) := by
    rw [k₃ .x18 (by decide), hp₂ .x18 (by decide)]; exact x18₂
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80003074_spec pc₃ (by
    rv_eval [sp₃, x10₃]
    simp only [Sym.validAccess_eight]
    and_intros <;> addr_omega [hb1, hb2, hb3, hal, hab, hFhi, hs0, hl, hmo])
  have fr₄ : Layout.DFrame u₃ u₄ fun a ↦ Within a F 48 ∨ Within a (s.getReg .x2 - 1344) 24 :=
    exL h₄ (by
      rv_eval [sp₃, x10₃]
      simp only [Within]
      and_intros <;> addr_omega [hb1, hal, hab, hFhi, hs0, hl, hmo])
  have k₄ := b80003074_keeps h₄
  have fr₄' : Layout.DFrame t₂ u₄ fun a ↦ Within a F 48 ∨ Within a (s.getReg .x2 - 1344) 24 :=
    fun a ha hw8 ↦ (fr₄ a ha hw8).trans (m₃ a)
  have hn₄ : heapNext u₄ = heapNext t₂ := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr₄' nextAddr (fun y hy hw ↦ by
      simp only [Within, nextAddr] at hy hw
      rcases hw with hw | hw <;> addr_omega [hy, hw, hb1, hFhi]) (by decide))
  have hv₄ : HeapOk u₄ := ⟨hn₄ ▸ postA.heap.lo, hn₄ ▸ postA.heap.hi⟩
  have sp₄ : u₄.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₄ .x2 (by decide)]; exact sp₃
  have K₄ := K₂.keep hpre fr₄' (fun a ha ↦ by
      rcases ha with ha | ha
      · simp only [Within] at ha
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by rw [hn₄, hnx]; omega⟩))
      · simp only [Within] at ha
        refine Or.inl ⟨by addr_omega [ha, hb1], by addr_omega [ha, hb1], ?_⟩
        simp only [hdrs, Within]
        addr_omega [ha, hb1]) hv₄ hn₄.ge (sp₄.trans sp₂.symm)
  have e1312 : u₃.getReg .x2 + 1312 = s.getReg .x2 - 1344 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1320 : u₃.getReg .x2 + 1320 = s.getReg .x2 - 1344 + 8 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1328 : u₃.getReg .x2 + 1328 = s.getReg .x2 - 1344 + 16 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hc : vecCap u₄ (s.getReg .x2 - 1344) = 6 := by
    simp only [vecCap]; rw [← e1312]; exact b80003074_m_x2_1312 h₄
  have hp : vecPtr u₄ (s.getReg .x2 - 1344) = F := by
    simp only [vecPtr]; rw [← e1320, b80003074_m_x2_1320 h₄, x10₃]
  have hln : vecLen u₄ (s.getReg .x2 - 1344) = 6 := by
    simp only [vecLen]; rw [← e1328]; exact b80003074_m_x2_1328 h₄
  have hlnN : (vecLen u₄ (s.getReg .x2 - 1344)).toNat = 6 := by rw [hln]; rfl
  refine ⟨u₄, hr₁.trans (hr₂.trans (hrt₂.trans (hr₃.trans hr₄))), Or.inr ⟨b80003074_pc h₄, {
    keep := K₄
    kv := {
      ok := ⟨by
        simp only [RawVecOk, Buf, hc, hp]
        refine ⟨hal, Or.inr ⟨by simp only [heapStart]; omega, ?_⟩⟩
        rw [hn₄, hnx]; simp, by rw [hlnN, hc]; decide⟩
      fresh := by rw [hp]; exact hab
      len := hlnN
      vals := fun j hj ↦ by
        rw [hp]
        have hj6 : j < 6 := hj
        have hh5 := heightsLe H.ok 5
        interval_cases j
        · show u₄.getMem (F + BitVec.ofNat 64 (8 * 0)) = BitVec.ofNat 64 (lmOf A).toNat
          rw [show F + BitVec.ofNat 64 (8 * 0) = F by simp, ← x10₃, b80003074_m_x10_0 h₄, x11₃,
            ofNat_toNat']
        · show u₄.getMem (F + 8) = BitVec.ofNat 64 (lmOf A).toNat
          rw [← x10₃, b80003074_m_x10_8 h₄, x11₃, ofNat_toNat']
        · show u₄.getMem (F + 16) = BitVec.ofNat 64 (lmOf A).toNat
          rw [← x10₃, b80003074_m_x10_16 h₄, x11₃, ofNat_toNat']
        · show u₄.getMem (F + 24) = BitVec.ofNat 64 (lmOf A).toNat
          rw [← x10₃, b80003074_m_x10_24 h₄, x11₃, ofNat_toNat']
        · show u₄.getMem (F + 32) = BitVec.ofNat 64 (k - 4)
          rw [← x10₃, b80003074_m_x10_32 h₄, x23₃]
        · show u₄.getMem (F + 40) = BitVec.ofNat 64 ((hts A).getD 5 0 + 6)
          rw [← x10₃, b80003074_m_x10_40 h₄, x18₃, ofNat_add6] }
    lt := by decide
    x8 := by rw [b80003074_x8 h₄]; rfl
    x9 := b80003074_x9 h₄
    x19 := b80003074_x19 h₄
    x20 := b80003074_x20 h₄
    x22 := by rw [k₄ .x22 (by decide)]; exact x22₃
    x27 := by
      rw [b80003074_x27 h₄, sp₃]; rv_eval [m₃]; rw [rd _ (by addr_omega [hb1])]; exact sB }⟩⟩

end Rv64Verifier.Proofs.Walk
