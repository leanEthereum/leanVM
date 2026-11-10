import Rv64Verifier.Proofs.Layout.ArithMul

/-!
# `flushes_arith`, at `0x8000547c`

The phases in order (`ArithBase.lean` describes the frame): `start`, `operands`, `copyOps`,
`cols`, then `addPath` or `mulPath` to the result, `toMemory` and `finish`.
-/

namespace Rv64Verifier.Layout.Arith
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F19 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.Limb (Held)

/-- `multiply` false: the three sums `col(va[i], 0) + col(vb[i], 0)`. -/
theorem addPath (hC : ColSpec) (hA : AddScaledSpec) {s u0 u : MachineState}
    (hpre : FlushesArithPre s) (hr : Reaches Image.code u0 u) (A : AtBranch s u)
    (hz : s.getReg .x12 = 0) :
    ∃ v, Reaches Image.code u0 v ∧ (AtTail s v (s.getReg .x2 - 328) (heapNext u)
      ((colRust 5 0).add (colRust 8 0)) ((colRust 6 0).add (colRust 9 0))
      ((colRust 7 0).add (colRust 10 0)) ∨ Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have c := A.toInv
  obtain ⟨z, hrz, hz₁⟩ := Sym.BlockSpec.reaches b800059f4_spec
    (by rw [A.pc]; simp only [hz, ↓reduceIte]; rfl) trivial
  have kz := b800059f4_keeps hz₁
  have hmz := b800059f4_mem_same hz₁
  have cz := c.same hpre hmz fun r hr ↦ kz r (mem_of_mem hr _)
  have Kz := sameKeeps hpre c hmz
  have hnz : heapNext z = heapNext u := by simp only [heapNext, hmz]
  obtain ⟨w₀, hr₀, ⟨c₀, hL₀, pc₀, x10₀, x11₀, x12₀, x1₀, x9₀, f₀, r₀⟩ | hd⟩ :=
    addLane0 hC hA hpre cz (hr.trans hrz) (b800059f4_pc hz₁)
      (by rw [b800059f4_x10 hz₁, c.x2]; rv_eval []) (b800059f4_x11 hz₁) (b800059f4_x12 hz₁)
      (b800059f4_x1 hz₁) (Kz.2 _ _ A.fl (Nat.le_refl _)) (by omega)
  swap
  · exact ⟨w₀, hr₀, Or.inr hd⟩
  obtain ⟨w₁, hr₁, ⟨c₁, hL₁, pc₁, x10₁, x11₁, x12₁, x1₁, x9₁, f₁, r₀₁, r₁⟩ | hd⟩ :=
    addLane1 hC hA hpre c₀ hr₀ pc₀ x10₀ x11₀ x12₀ x1₀ x9₀ f₀ hL₀ r₀
  swap
  · exact ⟨w₁, hr₁, Or.inr hd⟩
  obtain ⟨w₂, hr₂, ⟨c₂, hL₂, pc₂, x11₂, f₂, r₀₂, r₁₂, r₂⟩ | hd⟩ :=
    addLane2 hC hA hpre c₁ hr₁ pc₁ x10₁ x11₁ x12₁ x1₁ x9₁ f₁ hL₁ r₀₁ r₁
  swap
  · exact ⟨w₂, hr₂, Or.inr hd⟩
  exact ⟨w₂, hr₂, Or.inl {
    toInv := c₂
    pc := pc₂
    x11 := x11₂
    srcAt := Or.inr rfl
    hL := hL₂
    fl := f₂
    r0 := r₀₂
    r1 := by rw [show s.getReg .x2 - 328 + 24 = s.getReg .x2 - 304 by addr_omega [hsb]]; exact r₁₂
    r2 := by rw [show s.getReg .x2 - 328 + 48 = s.getReg .x2 - 280 by addr_omega [hsb]]; exact r₂ }⟩

/-- `multiply` true: the three lanes' product sums. -/
theorem mulPath (hP : ProdSpec) (hA : AddScaledSpec) {s u0 u : MachineState}
    (hpre : FlushesArithPre s) (hr : Reaches Image.code u0 u) (A : AtBranch s u)
    (hz : s.getReg .x12 ≠ 0) :
    ∃ v, Reaches Image.code u0 v ∧
      (AtTail s v (s.getReg .x2 - 136) (heapNext u) lane0 lane1 lane2 ∨ Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have c := A.toInv
  obtain ⟨w₀, hr₀, ⟨pc₀, c₀, hL₀, x9₀, x18₀, x19₀, f₀, b₀⟩ | hd⟩ :=
    mulLane0 hP hA hpre c hr (by rw [A.pc]; simp only [hz, ↓reduceIte]) A.fl (Nat.le_refl _)
  swap
  · exact ⟨w₀, hr₀, Or.inr hd⟩
  obtain ⟨w₁, hr₁, ⟨pc₁, c₁, hL₁, x9₁, x18₁, x19₁, f₁, r₀₁, b₁⟩ | hd⟩ :=
    mulLane1 hP hA hpre c₀ hr₀ pc₀ x9₀ x18₀ x19₀ f₀ hL₀ b₀
  swap
  · exact ⟨w₁, hr₁, Or.inr hd⟩
  obtain ⟨w₂, hr₂, ⟨pc₂, c₂, hL₂, f₂, r₀₂, r₁₂, b₂⟩ | hd⟩ :=
    mulLane2 hP hA hpre c₁ hr₁ pc₁ x9₁ x18₁ x19₁ f₁ hL₁ r₀₁ b₁
  swap
  · exact ⟨w₂, hr₂, Or.inr hd⟩
  -- the last lane's sum to `sp' + 392`
  obtain ⟨t, hrt, ht⟩ := Sym.BlockSpec.reaches b800059d4_spec pc₂
    (by rv_eval [c₂.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have kt := b800059d4_keeps ht
  have hmt := b800059d4_frame ht (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hmt
  obtain ⟨ct, hnt⟩ := c₂.block hpre hmt (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ kt r (mem_of_mem hr _)
  have Kt := blockKeeps hpre c₂ hmt (by addr_omega [hsb]) (by addr_omega [hsb])
  have hres := moveHeld (e := s.getReg .x2 - 88) b₂ hmt.dframe c₂.heap hnt.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, c₂.heap.hi])
    (by have := b800059d4_m_x2_392 ht; rw [c₂.x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b800059d4_m_x2_400 ht; rw [c₂.x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b800059d4_m_x2_408 ht; rw [c₂.x2] at this; rv_eval [] at this ⊢; exact this)
  exact ⟨t, hr₂.trans hrt, Or.inl {
    toInv := ct
    pc := b800059d4_pc ht
    x11 := by rw [b800059d4_x11 ht, c₂.x2]; rv_eval []
    srcAt := Or.inl rfl
    hL := by omega
    fl := Kt.2 _ _ f₂ (by omega)
    r0 := Kt.1 _ _ _ _ r₀₂ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
      |> fun h ↦ heldMono h (Nat.le_refl _) (by omega)
    r1 := by
      rw [show s.getReg .x2 - 136 + 24 = s.getReg .x2 - 112 by addr_omega [hsb]]
      exact heldMono (Kt.1 _ _ _ _ r₁₂ (by omega) (Or.inl (by addr_omega [hsb]))
        (by addr_omega [hsb])) (Nat.le_refl _) (by omega)
    r2 := by
      rw [show s.getReg .x2 - 136 + 48 = s.getReg .x2 - 88 by addr_omega [hsb]]
      exact heldMono hres (Nat.le_refl _) (by omega) }⟩

theorem flushes_arith_spec (hS : StateStepSpec) (hAl : AllocSpec) (hC : ColSpec) (hT : TermSpec)
    (hBc : BytecodeSpec) (hP : ProdSpec) (hK : MemoryColsSpec) (hA : AddScaledSpec)
    (hM : MemcpySpec 0x800126e4) (hMem : MemorySpec) : FlushesArithSpec := by
  intro s hpc hpre
  obtain ⟨u₁, B, hr₁, A₁ | hd⟩ := start hS hAl hC hpc hpre
  swap
  · exact ⟨u₁, hr₁, Or.inr hd⟩
  obtain ⟨u₂, hr₂, A₂ | hd⟩ := operands hC hT hpre hr₁ A₁
  swap
  · exact ⟨u₂, hr₂, Or.inr hd⟩
  obtain ⟨u₃, hr₃, A₃ | hd⟩ := copyOps hBc hpre hr₂ A₂
  swap
  · exact ⟨u₃, hr₃, Or.inr hd⟩
  obtain ⟨u₄, hr₄, A₄ | hd⟩ := cols hP hK hpre hr₃ A₃
  swap
  · exact ⟨u₄, hr₄, Or.inr hd⟩
  by_cases hz : s.getReg .x12 = 0
  · obtain ⟨u₅, hr₅, A₅ | hd⟩ := addPath hC hA hpre hr₄ A₄ hz
    swap
    · exact ⟨u₅, hr₅, Or.inr hd⟩
    obtain ⟨u₆, hr₆, A₆ | hd⟩ := toMemory hM hP hpre hr₅ A₅
    swap
    · exact ⟨u₆, hr₆, Or.inr hd⟩
    obtain ⟨t, hrt, ⟨hpct, hpt, hnew, hval⟩ | hd⟩ := finish hMem hpre hr₆ A₆
    swap
    · exact ⟨t, hrt, Or.inr hd⟩
    have hb : (s.getReg .x12 != 0) = false := by simp [hz]
    exact ⟨t, hrt, Or.inl ⟨hpct, hpt, hnew, by rw [hval, hb]; rfl⟩⟩
  · obtain ⟨u₅, hr₅, A₅ | hd⟩ := mulPath hP hA hpre hr₄ A₄ hz
    swap
    · exact ⟨u₅, hr₅, Or.inr hd⟩
    obtain ⟨u₆, hr₆, A₆ | hd⟩ := toMemory hM hP hpre hr₅ A₅
    swap
    · exact ⟨u₆, hr₆, Or.inr hd⟩
    obtain ⟨t, hrt, ⟨hpct, hpt, hnew, hval⟩ | hd⟩ := finish hMem hpre hr₆ A₆
    swap
    · exact ⟨t, hrt, Or.inr hd⟩
    have hb : (s.getReg .x12 != 0) = true := bne_iff_ne.mpr hz
    exact ⟨t, hrt, Or.inl ⟨hpct, hpt, hnew, by rw [hval, hb]; rfl⟩⟩

end Rv64Verifier.Layout.Arith
