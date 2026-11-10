import Rv64Verifier.Proofs.Gkr.KeccakFirst

/-!
# `keccak::verify_keccak`: the committed outputs' value, the first claim

`next_scalar()` into `f + 1952`, its `Err` returned (`to_committed`); the value copied to
`f + 176`.
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F35 Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- An `Err` written to the result's first 24 bytes, at the exit. -/
theorem err_exit {s u v : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u)
    (hpc : v.pc = 0x80009684) (hx2 : v.getReg .x2 = s.getReg .x2 - 5248)
    (f : MemFrame u v (s.getReg .x10) 24) (hcap : v.getMem (s.getReg .x10) = errNiche)
    (hf : Fails s) : ∃ t, Reaches Image.code v t ∧ Done s t := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  have hN : v.getMem nextAddr = u.getMem nextAddr := f _ (by addr_omega [ho, hpre.outFree])
  have Bv : Base s v := B.next hpre hx2
    ⟨by simp only [heapNext, hN]; exact B.heap.lo, by simp only [heapNext, hN]; exact B.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) (DFrame.of_memFrame f) fun a ha ↦
      ⟨Or.inl (by addr_omega [ha]), by unfold verifyKeccakStack at hb hos; addr_omega [ha, hos, hb]⟩
  obtain ⟨t, hr, pc, pres, same⟩ := exit hpre hpc Bv.x2 Bv.saved
  exact ⟨t, hr, Or.inl ⟨pc, pres, post_err Bv hcap hf same⟩⟩

/-- The committed outputs' value at `f + 176`, its limbs in `s1`, `a0`, `a2`. -/
structure A10 (s u : MachineState) (seg lp : List E) (wp : Word) (c : E) : Prop
    extends M s u seg where
  pc : u.pc = 0x80009198
  wb : WB s u wp lp
  x9 : u.getReg .x9 = u.getMem (s.getReg .x2 - 5072)
  x10 : u.getReg .x10 = u.getMem (s.getReg .x2 - 5064)
  x11 : u.getReg .x11 = s.getReg .x14
  x12 : u.getReg .x12 = u.getMem (s.getReg .x2 - 5056)
  x18 : u.getReg .x18 = s.getReg .x12
  x19 : u.getReg .x19 = 12
  x24 : u.getReg .x24 = 1
  last : eAt u (s.getReg .x2 - 5096) = lastOf s seg lp
  committed : eAt u (s.getReg .x2 - 5072) = c
  lpLen : lp.length = 5
  rest : Rest s u (kCommitted (s.getReg .x12).toNat (instOf s) (outOf s) seg lp c)

theorem to_committed (hNS : NextScalarSpec) {s u : MachineState} {seg lp : List E} {wp : Word}
    (hpre : VerifyKeccakPre s) (A : A9 s u seg lp wp) : ∃ v, Reaches Image.code u v ∧
      ((∃ c, A10 s v seg lp wp c) ∨ Done s v) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have B := A.base
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009110_spec A.pc trivial
  have pc₁ := b80009110_pc_not_taken h₁ (by rw [A.x19]; decide)
  have k₁ := b80009110_keeps h₁
  have m₁ := b80009110_mem_same h₁
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80009118_spec pc₁ trivial
  have k₂ := b80009118_keeps h₂
  have m₂ := b80009118_mem_same h₂
  have mu : ∀ a, u₂.getMem a = u.getMem a := fun a ↦ by rw [m₂, m₁]
  have x2₂ : u₂.getReg .x2 = s.getReg .x2 - 5248 := by
    rw [k₂ .x2 (by decide), k₁ .x2 (by decide), B.x2]
  have B₂ := B.same x2₂ mu
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - 3296 := by
    rw [b80009118_x10 h₂, k₁ .x2 (by decide), B.x2]
    exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have x11₂ : u₂.getReg .x11 = s.getReg .x11 := by
    rw [b80009118_x11 h₂, k₁ .x9 (by decide), A.x9]
  have tp := B₂.tpre hpre (n := 32) (k := nextScalarStack) 3296 x10₂ x11₂ (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hnp : NextScalarPre u₂ := {
    out := tp.out
    self := tp.self
    stack := tp.stack
    outStack := tp.outStack
    selfStack := tp.selfStack
    outSelf := tp.outSelf
    proofStack := tp.proofStack
    proofOut := tp.proofOut
    rodata := tp.rodata
    outRodata := tp.outRodata
    selfRodata := tp.selfRodata }
  obtain ⟨u₃, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hd⟩ := hNS.call (hr₁.trans hr₂) (b80009118_pc h₂) hnp
  swap
  · exact ⟨u₃, hr₃, Or.inr (Or.inr hd)⟩
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 5248 := (hpres₃.reg .x2).trans x2₂
  have F₃ : DFrame u₂ u₃ (SW s u₂ u₃ [(3296, 32)] true) := DFrame.mono hpost₃.frame
    fun a ha ↦ by
      rcases ha with h | h | h
      · exact Or.inl (out_sw (K := 3296) (n := 32) x10₂ h)
      · rw [x11₂] at h; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))
      · exact Or.inr (Or.inl (stk_sw hpre x2₂ (by decide) h))
  have hnx := hpre.stack.next
  unfold verifyKeccakStack at hnx
  have hN₃ : heapNext u₃ = heapNext u₂ := by
    simp only [heapNext]
    rw [hpost₃.frame _ fun i hi h ↦ by
      rw [x10₂, x11₂] at h
      have hS := hpre.self.self
      have hsf := hpre.selfFree.2
      simp only [stackLo, x2₂] at h
      rcases h with h | h | h <;> addr_omega [h, hi, hb, hnx, hS, hsf]]
  have H₃ : HeapOk u₃ := ⟨by rw [hN₃]; exact B₂.heap.lo, by rw [hN₃]; exact B₂.heap.hi⟩
  have B₃ := B₂.step hpre x2₃ H₃ (le_of_eq hN₃.symm) (by decide) F₃
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80009128_spec
    (by rw [hpc₃, returnAddress_eq, b80009118_x1 h₂]; decide) (by
      rv_eval [x2₃]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₄ := b80009128_keeps h₄
  have m₄ := b80009128_mem_same h₄
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 5248 := (k₄ .x2 (by decide)).trans x2₃
  have tag : u₃.getMem (u₃.getReg .x2 + 1952) = u₃.getMem (s.getReg .x2 - 3296) := by
    rw [x2₃]; exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
  have R₂ := A.rest.keep fun T hT ↦ Layer.transcriptAt_congr mu hT
  have M₂ : M s u₂ seg := A.toM.step hpre x2₂ B₂.heap (le_of_eq (by simp only [heapNext, mu]))
    (rs := []) (sp := false) (by decide) (by decide) (DFrame.of_same mu _)
  have M₃ := M₂.step hpre x2₃ H₃ (le_of_eq hN₃.symm) (by decide) (by decide) F₃
  have a8 : s.getReg .x2 - 3296 + 8 = s.getReg .x2 - 3288 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  by_cases hok : u₃.getMem (s.getReg .x2 - 3296) = 0
  swap
  · -- `Err`
    have pc₄ := b80009128_pc_not_taken h₄ (by rw [tag]; exact hok)
    have m48 : u₄.getMem (u₄.getReg .x2 + 48) = s.getReg .x10 := by
      rw [m₄, x2₄, show s.getReg .x2 - 5248 + 48 = s.getReg .x2 - 5200 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb])]; exact M₃.m48
    have ho := hpre.out
    have m48' : u₄.getMem (s.getReg .x2 - 5200) = s.getReg .x10 := by rw [m₄]; exact M₃.m48
    obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000913c_spec pc₄ (by
      rv_eval [x2₄]
      rv_eval [m48']
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have f₅ : MemFrame u₄ u₅ (s.getReg .x10) 24 := h₅.memFrame (by
      intro k hk
      simp only [b8000913c, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> rv_eval [m48] <;> addr_omega [ho])
    have hcap := b8000913c_m2 h₅
    rw [m48] at hcap
    obtain ⟨t, hr₆, ht⟩ := err_exit hpre (B₃.same x2₄ m₄) (b8000913c_pc h₅)
      ((b8000913c_keeps h₅ .x2 (by decide)).trans x2₄) f₅ hcap (R₂.fail fun T hT ↦ by
        have hv := hpost₃.value T (by rw [x11₂]; exact hT)
        rw [x10₂] at hv
        generalize TM.nextScalar.run T = o at hv
        rcases o with _ | ⟨x, T'⟩
        · rfl
        · exact absurd hv.1 hok)
    exact ⟨t, hr₃.trans (hr₄.trans (hr₅.trans hr₆)), Or.inr ht⟩
  -- `Ok`: the value to `f + 176`
  have pc₄ := b80009128_pc_taken h₄ (by rw [tag]; exact hok)
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80009188_spec pc₄ (by
    rv_eval [x2₄]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₅ := b80009188_keeps h₅
  have x2₅ : u₅.getReg .x2 = s.getReg .x2 - 5248 := (k₅ .x2 (by decide)).trans x2₄
  have F₅ : DFrame u₄ u₅ (Slots s [(5072, 24)]) := by
    have f := b80009188_frame h₅ (by rw [x2₄]; addr_omega [hb])
    rw [x2₄] at f
    rv_eval [] at f
    exact (DFrame.of_memFrame f).mono fun a ha ↦ ⟨(5072, 24), List.mem_singleton_self _, ha⟩
  have B₄ := B₃.same x2₄ m₄
  have B₅ := B₄.block hpre x2₅ (by decide) F₅
  have M₅ := (M₃.step hpre x2₄ B₄.heap (le_of_eq (by simp only [heapNext, m₄])) (rs := [])
    (sp := false) (by decide) (by decide) (DFrame.of_same m₄ _)).step hpre x2₅ B₅.heap
    (le_of_eq (by simp only [heapNext, slots_next hpre (by decide) F₅])) (by decide) (by decide)
    (slots_sw F₅)
  have mm (a b : Word) (h : b = a) : u₄.getMem a = u₃.getMem b := by rw [m₄, h]
  have e176 := b80009188_m_x2_176 h₅
  have e184 := b80009188_m_x2_184 h₅
  have e192 := b80009188_m_x2_192 h₅
  have a176 : u₄.getReg .x2 + 176 = s.getReg .x2 - 5072 := by
    rw [x2₄]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have a184 : u₄.getReg .x2 + 184 = s.getReg .x2 - 5064 := by
    rw [x2₄]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have a192 : u₄.getReg .x2 + 192 = s.getReg .x2 - 5056 := by
    rw [x2₄]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  rw [a176] at e176
  rw [a184] at e184
  rw [a192] at e192
  have hc : eAt u₅ (s.getReg .x2 - 5072) = eAt u₃ (s.getReg .x2 - 3288) := by
    refine eAt_congr ?_ ?_ ?_
    · rw [e176, b80009128_x9 h₄, x2₃]
      exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
    · rw [show s.getReg .x2 - 5072 + 8 = s.getReg .x2 - 5064 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb]), e184, b80009128_x10 h₄, x2₃]
      exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
    · rw [show s.getReg .x2 - 5072 + 16 = s.getReg .x2 - 5056 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb]), e192, m₄, x2₄]
      exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
  have chain (r : Reg) (hc : r ∈ calleeSaved)
      (h5 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x13, .x14, .x15, .x16,
        .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30,
        .x31] : List Reg))
      (h4 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x13, .x14, .x15, .x16, .x17, .x18, .x19,
        .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (h2 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14, .x15, .x16, .x17, .x18,
        .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (h1 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16,
        .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30,
        .x31] : List Reg)) :
      u₅.getReg r = u.getReg r := by
    rw [k₅ r h5, k₄ r h4, hpres₃.reg r hc, k₂ r h2, k₁ r h1]
  have hN₅ : heapNext u₅ = heapNext u₄ := by simp only [heapNext, slots_next hpre (by decide) F₅]
  have hN₂ : heapNext u₂ = heapNext u := by simp only [heapNext, mu]
  have hN₄ : heapNext u₄ = heapNext u₃ := by simp only [heapNext, m₄]
  have Ft : DFrame u u₅ (SW s u u₅ [(3296, 32), (5072, 24)] true) := by
    have F₂ : DFrame u u₂ (SW s u u₂ [] false) := DFrame.of_same mu _
    have F₄ : DFrame u₃ u₄ (SW s u₃ u₄ [] false) := DFrame.of_same m₄ _
    exact SW.trans (SW.trans (SW.trans F₂ F₃ (by simp) (fun p hp ↦ by simp at hp ⊢; exact Or.inl hp)
      (fun h ↦ by cases h) (fun h ↦ h) (le_of_eq hN₂.symm) (le_of_eq hN₃.symm)) F₄ (fun p hp ↦ hp)
      (by simp) (fun h ↦ h) (fun h ↦ by cases h) (le_of_eq (by rw [hN₃, hN₂]))
      (le_of_eq hN₄.symm)) (slots_sw F₅) (fun p hp ↦ hp)
      (fun p hp ↦ by simp at hp ⊢; exact Or.inr hp) (fun h ↦ h) (fun h ↦ by cases h)
      (le_of_eq (by rw [hN₄, hN₃, hN₂])) (le_of_eq hN₅.symm)
  have hNt : heapNext u ≤ heapNext u₅ := le_of_eq (by rw [hN₅, hN₄, hN₃, hN₂])
  have H₅ := B₅.heap
  refine ⟨u₅, hr₃.trans (hr₄.trans hr₅), Or.inl ⟨eAt u₃ (s.getReg .x2 - 3288), { M₅ with
    pc := b80009188_pc h₅
    wb := A.wb.step hpre B hNt (by decide) Ft fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact chain _ (by decide) (by decide) (by decide)
        (by decide) (by decide)
    x9 := by rw [k₅ .x9 (by decide)]; exact e176.symm
    x10 := by rw [k₅ .x10 (by decide)]; exact e184.symm
    x11 := by
      rw [k₅ .x11 (by decide), b80009128_x11 h₄, x2₃, show s.getReg .x2 - 5248 + 56 =
        s.getReg .x2 - 5192 from BitVec.eq_of_toNat_eq (by addr_omega [hb])]
      exact M₃.m56
    x12 := by rw [b80009188_x12 h₅]; exact e192.symm
    x18 := (chain .x18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans A.x18
    x19 := (chain .x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans A.x19
    x24 := (chain .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans A.x24
    last := (SW.e hpre H₅ (by decide) (J := 5096) (by decide) (by decide) (by decide) Ft).trans A.last
    committed := hc
    lpLen := A.lpLen
    rest := R₂.step fun T hT ↦ ?_ }⟩⟩
  have hv := hpost₃.value T (by rw [x11₂]; exact hT)
  rw [x10₂, x11₂, a8] at hv
  generalize TM.nextScalar.run T = o at hv ⊢
  rcases o with _ | ⟨x, T'⟩
  · rw [hok] at hv; exact absurd hv.1 (by decide)
  · obtain ⟨-, hx, hT'⟩ := hv
    refine ⟨T', by rw [hx], B₄.block_tat hpre (by decide) F₅ (Layer.transcriptAt_congr m₄ hT')⟩

theorem newVecE_copy {s v : MachineState} {a b : Word} {xs : List E} (h : NewVecE s v a xs)
    (e0 : v.getMem b = v.getMem a) (e8 : v.getMem (b + 8) = v.getMem (a + 8))
    (e16 : v.getMem (b + 16) = v.getMem (a + 16)) : NewVecE s v b xs := by
  obtain ⟨⟨hr, hl⟩, hb, he⟩ := h
  have c : vecCap v b = vecCap v a := e0
  have p : vecPtr v b = vecPtr v a := e8
  have l : vecLen v b = vecLen v a := e16
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [RawVecOk, c, p] at hr ⊢; exact hr
  · rw [l, c]; exact hl
  · rw [c, p]; exact hb
  · rw [← he]; simp only [vecEs, p, l]

/-- At `verify_layer`'s entry with the first claim at `f + 200`. -/
structure A11 (s u : MachineState) (seg lp : List E) (c : E) : Prop extends M s u seg where
  pc : u.pc = 0x8000f04c
  x1 : u.getReg .x1 = 0x80009214
  x10 : u.getReg .x10 = s.getReg .x2 - 3296
  x11 : u.getReg .x11 = s.getReg .x11
  x9 : u.getReg .x9 = s.getReg .x11
  x12 : u.getReg .x12 = s.getReg .x12
  x13 : u.getReg .x13 = 12
  x14 : u.getReg .x14 = 0
  x15 : u.getReg .x15 = s.getReg .x2 - 5048
  x18 : u.getReg .x18 = s.getReg .x12
  x19 : u.getReg .x19 = 12
  x24 : u.getReg .x24 = 1
  committed : eAt u (s.getReg .x2 - 5072) = c
  muV : NewVecE s u (s.getReg .x2 - 5048) (eqKernelRust ((instOf s).take 4))
  pointV' : NewVecE s u (s.getReg .x2 - 5024) ((instOf s).drop 4 ++ seg)
  weightsV : NewVecE s u (s.getReg .x2 - 5000) (kWeights (eqKernelRust lp))
  value : eAt u (s.getReg .x2 - 4976) = c + lastOf s seg lp
  lpLen : lp.length = 5
  rest : Rest s u (kCommitted (s.getReg .x12).toNat (instOf s) (outOf s) seg lp c)

theorem to_claim (hEK : EqKernelSpec) {s u : MachineState} {seg lp : List E} {wp : Word} {c : E}
    (hpre : VerifyKeccakPre s) (A : A10 s u seg lp wp c) : ∃ v, Reaches Image.code u v ∧
      (A11 s v seg lp c ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have B := A.base
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009198_spec A.pc (by
    rv_eval [B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b80009198_keeps h₁
  have m₁ := b80009198_mem_same h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 5248 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ := B.same x2₁ m₁
  have hN₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 5048 := by
    rw [b80009198_x10 h₁, B.x2]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have x11₁ : u₁.getReg .x11 = s.getReg .x14 := (k₁ .x11 (by decide)).trans A.x11
  have hok := A.ok
  have hiR := hpre.inst
  have hiF := hpre.instFree
  have hiS := hpre.instStack
  have hinst : kInstLen s = (s.getReg .x12).toNat := by simp only [kInstLen, hok.1]
  rw [hinst] at hiR hiF hiS
  simp only [kInst] at hiR hiF hiS
  rcases hiR with h0 | hiR
  · have := hok.2; omega
  have hl := hok.2
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  have hnx := hpre.stack.next
  unfold verifyKeccakStack at hb hab hrs hnx hiS
  have hek : EqKernelPre u₁ := {
    heap := B₁.heap
    out := by rw [x10₁]; addr_omega [hb, hsm]
    point := by
      rw [x11₁, b80009198_x12 h₁]; right
      exact ⟨by addr_omega [hiR, hl], by addr_omega [hiR]⟩
    stack := hpre.stack.sub 5248 x2₁ (by unfold verifyKeccakStack; decide) (by decide)
      (by decide) (by decide) (by decide)
    outFree := by rw [x10₁]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    pointFree := by
      rw [x11₁, b80009198_x12 h₁]; right
      obtain ⟨f1, f2⟩ := hiF
      have hm := B₁.mono
      exact ⟨by addr_omega [f1, hiR, hl, hm], by addr_omega [f2, hiR, hl]⟩
    outStack := by rw [x10₁]; simp only [stackLo, x2₁]; addr_omega [hb]
    pointStack := by
      rw [x11₁, b80009198_x12 h₁]; simp only [stackLo, x2₁]; addr_omega [hb, hiS, hiR, hl]
    pointOut := by rw [x11₁, b80009198_x12 h₁, x10₁]; addr_omega [hb, hiS, hiR, hl]
    rodata := B₁.rodata hpre
    outRodata := by rw [x10₁]; addr_omega [hb, hrs] }
  obtain ⟨u₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hEK.call hr₁ (b80009198_pc h₁) hek
  swap
  · exact ⟨u₂, hr₂, Or.inr hd⟩
  have x2₂ : u₂.getReg .x2 = s.getReg .x2 - 5248 := (hpres₂.reg .x2).trans x2₁
  have F₂ : DFrame u₁ u₂ (SW s u₁ u₂ [(5048, 24)] false) := DFrame.mono hpost₂.frame
    fun a ha ↦ cframe_sw hpre 5048 x2₁ x10₁ (by decide) a ha
  have B₂ := B₁.step hpre x2₂ hpost₂.heap hpost₂.mono (by decide) F₂
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800091c0_spec
    (by rw [hpc₂, returnAddress_eq, b80009198_x1 h₁]; decide) (by
      rv_eval [x2₂]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b800091c0_keeps h₃
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 5248 := (k₃ .x2 (by decide)).trans x2₂
  have F₃ : DFrame u₂ u₃ (Slots s [(5024, 72)]) := by
    have f := b800091c0_frame h₃ (by rw [x2₂]; addr_omega [hb])
    rw [x2₂] at f
    rv_eval [] at f
    exact (DFrame.of_memFrame f).mono fun a ha ↦ ⟨(5024, 72), List.mem_singleton_self _, ha⟩
  have B₃ := B₂.block hpre x2₃ (by decide) F₃
  have hN₃ : heapNext u₃ = heapNext u₂ := by simp only [heapNext, slots_next hpre (by decide) F₃]
  have hN₁₂ : heapNext u ≤ heapNext u₂ := by rw [← hN₁]; exact hpost₂.mono
  have Ft : DFrame u u₃ (SW s u u₃ [(5048, 24), (5024, 72)] false) :=
    SW.trans (SW.trans (DFrame.of_same m₁ (SW s u u₁ [] false)) F₂ (by simp)
      (fun p hp ↦ by simp at hp ⊢; exact Or.inl hp) (fun h ↦ h) (fun h ↦ h) (le_of_eq hN₁.symm)
      hpost₂.mono) (slots_sw F₃) (fun p hp ↦ hp) (fun p hp ↦ by simp at hp ⊢; exact Or.inr hp)
      (fun h ↦ h) (fun h ↦ h) hN₁₂ (le_of_eq hN₃.symm)
  have hNt : heapNext u ≤ heapNext u₃ := by rw [hN₃]; exact hN₁₂
  have M₃ := A.toM.step hpre x2₃ B₃.heap hNt (by decide) (by decide) Ft
  have W₃ := A.wb.step hpre B hNt (by decide) Ft fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [k₃ _ (by decide), hpres₂.reg _ (by decide), k₁ _ (by decide)]
  have chain (r : Reg) (hc : r ∈ calleeSaved)
      (h3 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x16, .x17, .x18, .x19, .x20, .x21, .x22,
        .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (h1 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x11, .x16, .x17, .x18, .x19, .x20, .x23, .x24,
        .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg)) :
      u₃.getReg r = u.getReg r := by rw [k₃ r h3, hpres₂.reg r hc, k₁ r h1]
  have a2 (k : Nat) (hk : k ≤ 5248) : u₂.getReg .x2 + BitVec.ofNat 64 k =
      s.getReg .x2 - BitVec.ofNat 64 (5248 - k) := by
    rw [x2₂]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb, hk])
  have kb (J : Nat) (hJ : J ≤ 5248) (h8 : 8 ≤ J) (hsep : SlotsSep [(5024, 72)] J 8 = true) :=
    SW.mem hpre B₃.heap (by decide) hJ h8 hsep (slots_sw F₃)
  -- the claim's `Vec`s
  have hmu := hpost₂.value
  rw [x10₁, x11₁, b80009198_x12 h₁] at hmu
  have emu : eListAt u₁ (s.getReg .x14) (4 : Word).toNat = (instOf s).take 4 := by
    rw [instOf, kInst, kInstLen, hok.1, eListAt_take _ _ hl]
    have hm := missInst hpre B₁.heap
    rw [hinst] at hm
    simp only [kInst] at hm
    exact B₁.eListAt (fun y hy ↦ hm y (by addr_omega [hy, hiR, hl])) (Or.inr (by addr_omega [hiR, hl]))
  rw [emu] at hmu
  have e72 : u₂.getMem (u₂.getReg .x2 + 72) = s.getReg .x11 := by
    rw [show u₂.getReg .x2 + 72 = s.getReg .x2 - 5176 from a2 72 (by decide)]; exact (kb 5176 (by decide) (by decide) (by decide)).symm.trans M₃.m72
  have hw := W₃.wbuf
  simp only [NewBuf] at hw
  have w248 : u₃.getMem (s.getReg .x2 - 5000) = 1600 := by
    have := b800091c0_m_x2_248 h₃; rw [show u₂.getReg .x2 + 248 = s.getReg .x2 - 5000 from a2 248 (by decide)] at this
    rw [this, ← k₃ .x20 (by decide)]; exact W₃.x20
  have w256 : u₃.getMem (s.getReg .x2 - 5000 + 8) = wp := by
    have := b800091c0_m_x2_256 h₃; rw [show u₂.getReg .x2 + 256 = s.getReg .x2 - 4992 from a2 256 (by decide)] at this
    rw [show s.getReg .x2 - 5000 + 8 = s.getReg .x2 - 4992 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb]), this, ← k₃ .x8 (by decide)]; exact W₃.x8
  have w264 : u₃.getMem (s.getReg .x2 - 5000 + 16) = 1600 := by
    have := b800091c0_m_x2_264 h₃; rw [show u₂.getReg .x2 + 264 = s.getReg .x2 - 4984 from a2 264 (by decide)] at this
    rw [show s.getReg .x2 - 5000 + 16 = s.getReg .x2 - 4984 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb]), this, ← k₃ .x26 (by decide)]; exact W₃.x26
  have hweights : NewVecE s u₃ (s.getReg .x2 - 5000) (kWeights (eqKernelRust lp)) := by
    have c1 : vecCap u₃ (s.getReg .x2 - 5000) = 1600 := w248
    have c2 : vecPtr u₃ (s.getReg .x2 - 5000) = wp := w256
    have c3 : vecLen u₃ (s.getReg .x2 - 5000) = 1600 := w264
    have h16 : (1600 : Word).toNat = 1600 := rfl
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [RawVecOk, Buf, c1, c2, h16]; have := hpre.heap.lo; omega
    · rw [c3, c1]
    · simp only [NewBuf, c1, c2, h16]; omega
    · rw [vecEs, c2, c3, h16]; exact W₃.weights
  have hval : eAt u₃ (s.getReg .x2 - 4976) = c + lastOf s seg lp := by
    rw [← A.committed, ← A.last]
    apply eAt_eq_of_limbs
    rw [limbs_add, limbs_eAt, limbs_eAt]
    have v272 := b800091c0_m_x2_272 h₃
    have v280 := b800091c0_m_x2_280 h₃
    have v288 := b800091c0_m_x2_288 h₃
    rw [show u₂.getReg .x2 + 272 = s.getReg .x2 - 4976 from a2 272 (by decide), hpres₂.reg .x9, b80009198_x9 h₁, A.x9, B.x2] at v272
    rw [show u₂.getReg .x2 + 280 = s.getReg .x2 - 4968 from a2 280 (by decide), hpres₂.reg .x21, b80009198_x21 h₁, A.x10, B.x2] at v280
    rw [show u₂.getReg .x2 + 288 = s.getReg .x2 - 4960 from a2 288 (by decide), hpres₂.reg .x22, b80009198_x22 h₁, A.x12, B.x2] at v288
    have q (x y : Word) (h : x.toNat = y.toNat) : u.getMem x = u.getMem y := by
      rw [BitVec.eq_of_toNat_eq h]
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [v272, BitVec.xor_comm, q (s.getReg .x2 - 5248 + 152) (s.getReg .x2 - 5096)
        (by addr_omega [hb])]
    · rw [show s.getReg .x2 - 4976 + 8 = s.getReg .x2 - 4968 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb]), v280, BitVec.xor_comm,
        q (s.getReg .x2 - 5248 + 160) (s.getReg .x2 - 5096 + 8) (by addr_omega [hb]),
        q (s.getReg .x2 - 5064) (s.getReg .x2 - 5072 + 8) (by addr_omega [hb])]
    · rw [show s.getReg .x2 - 4976 + 16 = s.getReg .x2 - 4960 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb]), v288, BitVec.xor_comm,
        q (s.getReg .x2 - 5248 + 168) (s.getReg .x2 - 5096 + 16) (by addr_omega [hb]),
        q (s.getReg .x2 - 5056) (s.getReg .x2 - 5072 + 16) (by addr_omega [hb])]
  have hp0 : u₃.getMem (s.getReg .x2 - 5024) = u₃.getMem (s.getReg .x2 - 5144) := by
    have := b800091c0_m_x2_224 h₃
    rw [show u₂.getReg .x2 + 224 = s.getReg .x2 - 5024 from a2 224 (by decide),
      show u₂.getReg .x2 + 104 = s.getReg .x2 - 5144 from a2 104 (by decide)] at this
    rw [this]; exact (kb 5144 (by decide) (by decide) (by decide)).symm
  have hp8 : u₃.getMem (s.getReg .x2 - 5024 + 8) = u₃.getMem (s.getReg .x2 - 5144 + 8) := by
    have := b800091c0_m_x2_232 h₃
    rw [show u₂.getReg .x2 + 232 = s.getReg .x2 - 5024 + 8 from
        (a2 232 (by decide)).trans (BitVec.eq_of_toNat_eq (by addr_omega [hb])),
      show u₂.getReg .x2 + 112 = s.getReg .x2 - 5136 from a2 112 (by decide)] at this
    rw [this, show s.getReg .x2 - 5144 + 8 = s.getReg .x2 - 5136 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb])]
    exact (kb 5136 (by decide) (by decide) (by decide)).symm
  have hp16 : u₃.getMem (s.getReg .x2 - 5024 + 16) = u₃.getMem (s.getReg .x2 - 5144 + 16) := by
    have := b800091c0_m_x2_240 h₃
    rw [show u₂.getReg .x2 + 240 = s.getReg .x2 - 5024 + 16 from
        (a2 240 (by decide)).trans (BitVec.eq_of_toNat_eq (by addr_omega [hb])),
      show u₂.getReg .x2 + 120 = s.getReg .x2 - 5128 from a2 120 (by decide)] at this
    rw [this, show s.getReg .x2 - 5144 + 16 = s.getReg .x2 - 5128 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb])]
    exact (kb 5128 (by decide) (by decide) (by decide)).symm
  refine ⟨u₃, hr₂.trans hr₃, Or.inl { M₃ with
    pc := b800091c0_pc h₃
    x1 := b800091c0_x1 h₃
    x10 := by rw [b800091c0_x10 h₃]; exact a2 1952 (by decide)
    x11 := by rw [b800091c0_x11 h₃]; exact e72
    x9 := by rw [b800091c0_x9 h₃]; exact e72
    x12 := by rw [b800091c0_x12 h₃, hpres₂.reg .x18, k₁ .x18 (by decide), A.x18]
    x13 := by rw [b800091c0_x13 h₃, hpres₂.reg .x19, k₁ .x19 (by decide), A.x19]
    x14 := b800091c0_x14 h₃
    x15 := by rw [b800091c0_x15 h₃]; exact a2 200 (by decide)
    x18 := (chain .x18 (by decide) (by decide) (by decide)).trans A.x18
    x19 := (chain .x19 (by decide) (by decide) (by decide)).trans A.x19
    x24 := (chain .x24 (by decide) (by decide) (by decide)).trans A.x24
    committed := (SW.e hpre B₃.heap (by decide) (J := 5072) (by decide) (by decide) (by decide)
      Ft).trans A.committed
    muV := SW.vec hpre B₂ B₃.heap (le_of_eq hN₃.symm) (by decide) (J := 5048) (by decide)
      (by decide) (by decide) (slots_sw F₃) (Open.newVecE_mono hmu B₁.mono)
    pointV' := newVecE_copy M₃.pointV hp0 hp8 hp16
    weightsV := hweights
    value := hval
    lpLen := A.lpLen
    rest := A.rest.keep fun T hT ↦ SW.tat hpre B B₃.heap hNt (by decide) Ft hT }⟩

/-- The claim at `f + 200` is the mirror's first. -/
theorem A11.claim {s u : MachineState} {seg lp : List E} {c : E} (hpre : VerifyKeccakPre s)
    (A : A11 s u seg lp c) :
    claimAt u (s.getReg .x2 - 5048) = kFirst (instOf s) seg lp (outOf s) c := by
  have hb := bounds hpre
  have e24 : s.getReg .x2 - 5048 + 24 = s.getReg .x2 - 5024 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have e48 : s.getReg .x2 - 5048 + 48 = s.getReg .x2 - 5000 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have e72 : s.getReg .x2 - 5048 + 72 = s.getReg .x2 - 4976 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  simp only [claimAt, e24, e48, e72, A.value, A.muV.elems, A.pointV'.elems, A.weightsV.elems,
    kFirst, lastOf]

end Rv64Verifier.Gkr.Keccak
