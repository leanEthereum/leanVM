import Rv64Verifier.Proofs.Pcs.VsoRowsD1
import Rv64Verifier.Proofs.Pcs.VsoRowed

/-!
# `verify_stacked_opening`'s level loop: a deeper level's rows, the row's buffer

The row loop's head at `0x8000b210` (`DeepAt`, row `j` of the leaves `LeavesAt`, the values so
far at `O`), and its first part (`rowAlloc`): row `j`'s pointer and length read from the slices,
`n / 3` by the constant at `S - 880`, `try_allocate_in(S - 384, n / 3, 0, 8, 24)`, the trap on
`Err`, the `Vec` at `S - 384` and `reserve` with room, to `0x8000b27c` (`RowAlloc`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso.RowsD
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A deeper row's value: `dot(ext_row(row), kernel)`. -/
def rowF (ker : List E) (row : List K) : E := Model.dotRust (Model.Pcs.extRowRust row) ker

theorem b210_x19 {s t : MachineState} (h : b8000b210.Holds s t) :
    t.getReg .x19 = rv64_mulhu (s.getMem (s.getReg .x24 + s.getReg .x18 * 16 + 8))
      (s.getMem (s.getReg .x2 + 160) + s.getMem (s.getReg .x2 + 160) <<< 32) >>> 1 :=
  h.reg_eq .x19 rfl (by rv_eval [])

theorem b210_x11 {s t : MachineState} (h : b8000b210.Holds s t) :
    t.getReg .x11 = rv64_mulhu (s.getMem (s.getReg .x24 + s.getReg .x18 * 16 + 8))
      (s.getMem (s.getReg .x2 + 160) + s.getMem (s.getReg .x2 + 160) <<< 32) >>> 1 :=
  h.reg_eq .x11 rfl (by rv_eval [])

/-! ## What the rows write -/

theorem rowW_mono {s k u r : MachineState} (h : heapNext u ≤ heapNext r) {a : Word}
    (ha : RowW s k u a) : RowW s k r a := by
  rcases ha with ha | ha | ha | ha | ha | ha | ⟨h1, h2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩)))))

/-- A `Clear` range misses what the rows write. -/
theorem clear_notRowW {s k u : MachineState} (hpre : VsoPre s) {a : Word} {n : ℕ}
    (h : Clear s (heapNext k) a n) (hu : heapNext u ≤ heapEnd) :
    ∀ y, Within y a n → ¬ RowW s k u y := by
  have hb := bounds hpre
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := h
  intro y hy hw
  rcases hw with hw | hw | hw | hw | hw | hw | ⟨hw1, hw2⟩
  · addr_omega [hy, hw, h2, hb]
  · addr_omega [hy, hw, h2, hb]
  · addr_omega [hy, hw, h2, hb]
  · addr_omega [hy, hw, h2, hb]
  · addr_omega [hy, hw, h2, hb]
  · addr_omega [hy, hw, h3]
  · rcases h1 with h1 | h1
    · addr_omega [hy, hw1, h1]
    · addr_omega [hy, hw2, h1, hu]

/-- The heap below `heapNext k` misses what the rows write. -/
theorem low_notRowW {s k u : MachineState} (hpre : VsoPre s) (hk : heapNext k ≤ heapEnd) {y : Word}
    (hy : y.toNat < heapNext k) : ¬ RowW s k u y := by
  have hsm := stack_mapped hpre
  intro hw
  rcases hw with hw | hw | hw | hw | hw | hw | ⟨hw1, -⟩
  · addr_omega [hy, hw, hsm, hk]
  · addr_omega [hy, hw, hsm, hk]
  · addr_omega [hy, hw, hsm, hk]
  · addr_omega [hy, hw, hsm, hk]
  · addr_omega [hy, hw, hsm, hk]
  · addr_omega [hy, hw, hk]
  · omega

theorem keepClear {s k u : MachineState} (hpre : VsoPre s) (hfr : DFrame k u (RowW s k u))
    (hu : heapNext u ≤ heapEnd) {a : Word} {n : ℕ} (h : Clear s (heapNext k) a n) {y : Word}
    (h1 : a.toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ a.toNat + n) (h3 : a.toNat + n ≤ 2 ^ 64) :
    u.getMem y = k.getMem y :=
  hfr y fun i hi hw ↦ clear_notRowW hpre h hu _ (by addr_omega [h1, h2, h3, hi]) hw

theorem keepLow {s k u : MachineState} (hpre : VsoPre s) (hfr : DFrame k u (RowW s k u))
    (hk : heapNext k ≤ heapEnd) {y : Word} (hy : y.toNat + 8 ≤ heapNext k) :
    u.getMem y = k.getMem y :=
  hfr y fun i hi hw ↦ low_notRowW hpre hk (by addr_omega [hy, hi, hk]) hw

/-- The slots the rows read, kept. -/
theorem keepSlot {s k u : MachineState} (hpre : VsoPre s) (hfr : DFrame k u (RowW s k u))
    (hu : HeapOk u) (o : ℕ) (ho : o = 832 ∨ o = 880 ∨ o = 528 ∨ o = 520) :
    u.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = k.getMem (s.getReg .x2 - BitVec.ofNat 64 o) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hhi := hu.hi
  refine hfr _ fun i hi hw ↦ ?_
  rcases hw with hw | hw | hw | hw | hw | hw | ⟨-, hw⟩ <;>
    rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hb, hnx, hhi]

/-! ## The loop's head -/

/-- The inputs: the kernel, the leaves, the constant of the division by three. -/
structure DCtx (s t' k : MachineState) (lf : List E) (ws : List (List K)) : Prop where
  pre : VsoPre s
  ker : Kerneled s t' k lf
  leaves : LeavesAt s k ws
  m880 : k.getMem (s.getReg .x2 - 880) = 0xffffffffaaaaaaab

/-- At `0x8000b210`, row `j` next: the values of the rows before it at `O`. -/
structure DeepAt (s k u : MachineState) (ws : List (List K)) (ker : List E) (O : Word) (j : ℕ) :
    Prop where
  pc : u.pc = 0x8000b210
  sp : u.getReg .x2 = s.getReg .x2 - 1040
  x18 : u.getReg .x18 = BitVec.ofNat 64 j
  x27 : u.getReg .x27 = BitVec.ofNat 64 j
  x20 : u.getReg .x20 = k.getReg .x20
  x21 : u.getReg .x21 = vecLen k (s.getReg .x2 - 536)
  x24 : u.getReg .x24 = k.getMem (s.getReg .x2 - 832)
  x25 : u.getReg .x25 = O
  regs : ∀ q ∈ [Reg.x9, .x23, .x26], u.getReg q = k.getReg q
  m784 : u.getMem (s.getReg .x2 - 784) = vecPtr k (s.getReg .x2 - 536)
  inv : InvR s u (u.getMem nextAddr)
  heap : HeapOk u
  mono : heapNext k ≤ heapNext u
  buf : O.toNat % 8 = 0 ∧ heapNext k ≤ O.toNat ∧ O.toNat + 24 * ws.length ≤ heapNext u
  value : eListAt u O j = (ws.take j).map (rowF ker)
  fr : DFrame k u (RowW s k u)

/-- At `0x8000b27c`, `reserve` returned: row `j`'s buffer `B` of `n / 3` `E`s, empty. -/
structure RowAlloc (s k u v : MachineState) (j : ℕ) (B : Word) : Prop where
  pc : v.pc = 0x8000b27c
  sp : v.getReg .x2 = s.getReg .x2 - 1040
  x8 : v.getReg .x8 = sliceP s k j
  x22 : v.getReg .x22 = sliceL s k j
  x19 : v.getReg .x19 = BitVec.ofNat 64 ((sliceL s k j).toNat / 3)
  regs : ∀ q ∈ [Reg.x9, .x18, .x20, .x21, .x23, .x24, .x25, .x26, .x27], v.getReg q = u.getReg q
  m376 : v.getMem (s.getReg .x2 - 376) = B
  m368 : v.getMem (s.getReg .x2 - 368) = 0
  bal : B.toNat % 8 = 0
  bnew : (sliceL s k j).toNat / 3 = 0 ∨
    heapNext u ≤ B.toNat ∧ B.toNat + 24 * ((sliceL s k j).toNat / 3) ≤ heapNext v
  fr : DFrame u v fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨ Within a (s.getReg .x2 - 1088) 48 ∨
    Within a nextAddr 8 ∨ Fresh u v a
  heap : HeapOk v
  mono : heapNext u ≤ heapNext v

theorem ofNat_mul16 (j : ℕ) : BitVec.ofNat 64 j * 16 = BitVec.ofNat 64 (16 * j) := by
  apply BitVec.eq_of_toNat_eq
  have h16 : (16 : Word).toNat = 16 := rfl
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, h16]
  rw [Nat.mod_mul_mod, Nat.mul_comm]

/-- **Row `j`'s buffer**: from the loop's head to `reserve`'s return, or a trap. -/
theorem rowAlloc (hT : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x80008a10)
    {s t' k u : MachineState} {lf : List E} {ws : List (List K)} {ker : List E} {O : Word} {j : ℕ}
    (C : DCtx s t' k lf ws) (hu : DeepAt s k u ws ker O j) (hj : j < ws.length) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ ∃ B, RowAlloc s k u v j B) := by
  have hpre := C.pre
  have hb := bounds hpre
  have hst := hpre.stack
  have hsm := stack_mapped hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := hu.sp
  have hhu := hu.heap
  have hL := C.leaves
  have hn0 : ws.length ≠ 0 := by omega
  obtain ⟨hPr, hPc⟩ : Region (k.getMem (s.getReg .x2 - 832)) (16 * ws.length) ∧
      Clear s (heapNext k) (k.getMem (s.getReg .x2 - 832)) (16 * ws.length) := by
    rcases hL.slices with h0 | h0
    · exact absurd h0 hn0
    · exact h0
  have hPb := Region.bounds hPr
  have kP (o : ℕ) (ho : o + 8 ≤ 16 * ws.length) :
      u.getMem (k.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 o) =
        k.getMem (k.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 o) :=
    keepClear hpre hu.fr hhu.hi hPc (by addr_omega [hPb, ho]) (by addr_omega [hPb, ho])
      (by addr_omega [hPb])
  have e880 : u.getMem (s.getReg .x2 - 880) = 0xffffffffaaaaaaab :=
    (keepSlot hpre hu.fr hhu 880 (by simp)).trans C.m880
  -- `0x8000b210`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000b210_spec hu.pc (by
    rv_eval [hsp, hu.x24, hu.x18, ofNat_mul16]
    and_intros
    · valid_access hst.valid [hb]
    · exact Region.valid hPr (by addr_omega [hPb, hj]) (by addr_omega [hPb, hj])
        (by addr_omega [hPb, hj])
    · exact Region.valid hPr (by addr_omega [hPb, hj]) (by addr_omega [hPb, hj])
        (by addr_omega [hPb, hj]))
  have k₁ := b8000b210_keeps h₁
  have m₁ := b8000b210_mem_same h₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1040 := (k₁ .x2 (by decide)).trans hsp
  have hn₁ : heapNext t₁ = heapNext u := by simp only [heapNext, m₁]
  have eA : u.getReg .x24 + u.getReg .x18 * 16 =
      k.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (16 * j) := by
    rw [hu.x24, hu.x18, ofNat_mul16]
  have eA8 : u.getReg .x24 + u.getReg .x18 * 16 + 8 =
      k.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (16 * j + 8) := by
    rw [eA]; addr_omega [hPb, hj]
  have x8₁ : t₁.getReg .x8 = sliceP s k j := by
    rw [b8000b210_x8 h₁, eA, kP _ (by omega)]; rfl
  have x22₁ : t₁.getReg .x22 = sliceL s k j := by
    rw [b8000b210_x22 h₁, show u.getReg .x24 + u.getReg .x18 * (16 : Word) + (8 : Word) =
      u.getReg .x24 + u.getReg .x18 * 16 + 8 from rfl, eA8, kP _ (by omega)]; rfl
  have e160 : u.getMem (u.getReg .x2 + 160) = 0xffffffffaaaaaaab := by
    rw [hsp, show s.getReg .x2 - 1040 + 160 = s.getReg .x2 - 880 by rv_eval [], e880]
  have hL3 : u.getMem (u.getReg .x24 + u.getReg .x18 * 16 + 8) = sliceL s k j := by
    rw [eA8, kP _ (by omega)]; rfl
  have x19₁ : t₁.getReg .x19 = BitVec.ofNat 64 ((sliceL s k j).toNat / 3) := by
    rw [b210_x19 h₁, e160, hL3, div3]
  have x11₁ : t₁.getReg .x11 = BitVec.ofNat 64 ((sliceL s k j).toNat / 3) := by
    rw [b210_x11 h₁, e160, hL3, div3]
  -- `try_allocate_in`
  obtain ⟨t₂, r₂, hv₂⟩ := callTryAlloc24 hT hpre (b8000b210_pc h₁) sp₁
    (by rw [b8000b210_x10 h₁, hsp]; rv_eval []) (b8000b210_x13 h₁) (b8000b210_x14 h₁)
    ⟨by rw [hn₁]; exact hhu.lo, by rw [hn₁]; exact hhu.hi⟩
  rcases hv₂ with hd | ⟨pc₂, pr₂, heap₂, mono₂, ok₂, fr₂⟩
  · exact ⟨t₂, r₁.trans r₂, Or.inl hd⟩
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1040 := (pr₂.reg .x2).trans sp₁
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000b250_spec
    (by rw [pc₂, returnAddress_eq, b8000b210_x1 h₁]; rfl) (by
      rv_eval [sp₂]; valid_access hst.valid [hb])
  have q656 : t₂.getMem (t₂.getReg .x2 + 656) = t₂.getMem (s.getReg .x2 - 384) := by
    rw [sp₂]; rv_eval []
  by_cases htag : t₂.getMem (s.getReg .x2 - 384) = 0
  swap
  · have hpc₃ := b8000b250_pc_taken h₃ (by rw [q656]; exact htag)
    exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inl (dead_of_fetch (by rw [hpc₃]; exact Vso.trap))⟩
  have hpc₃ := b8000b250_pc_not_taken h₃ (by rw [q656]; exact htag)
  obtain ⟨hcap, hnew⟩ := ok₂ htag
  rw [x11₁] at hcap hnew
  have k₃ := b8000b250_keeps h₃
  have m₃ := b8000b250_mem_same h₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 1040 := (k₃ .x2 (by decide)).trans sp₂
  -- the `Vec` at `S - 384`, and `reserve` with room
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000b258_spec hpc₃ (by
    rv_eval [sp₃]; and_intros <;> valid_access hst.valid [hb])
  have k₄ := b8000b258_keeps h₄
  have fr₄ := DFrame.of_memFrame (b8000b258_frame h₄ (by rw [sp₃]; addr_omega [hb]))
  rw [sp₃, show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval []] at fr₄
  have v0 := b8000b258_m_x2_656 h₄
  have v1 := b8000b258_m_x2_664 h₄
  have v2 := b8000b258_m_x2_672 h₄
  rw [sp₃] at v0 v1 v2
  rv_eval [m₃] at v0 v1 v2
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 1040 := (k₄ .x2 (by decide)).trans sp₃
  have x10₄ : t₄.getReg .x10 = s.getReg .x2 - 384 := by rw [b8000b258_x10 h₄, sp₃]; rv_eval []
  have x11₄ : t₄.getReg .x11 = BitVec.ofNat 64 ((sliceL s k j).toNat / 3) := by
    rw [b8000b258_x11 h₄, k₃ .x19 (by decide), pr₂.reg .x19, x19₁]
  obtain ⟨t₅, r₅, ⟨pc₅, pr₅, -, m₅⟩ | hd⟩ := hRF.call (Reaches.refl t₄) (b8000b258_pc h₄)
    ⟨by rw [x10₄]; valid_sub hst.valid [hb], by
      rw [x10₄, x11₄]
      simp only [vecLen, vecCap]
      rw [show s.getReg .x2 - 384 + 16 = s.getReg .x2 - 368 by rv_eval [], v2, v0, hcap]
      exact Nat.le_of_eq (by rw [show (0 : Word).toNat = 0 from rfl, Nat.zero_add])⟩
  swap
  · exact ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inl hd⟩
  -- `NEXT` and the frame
  have nx₄ : t₄.getMem nextAddr = t₃.getMem nextAddr :=
    fr₄ _ fun i hi hw ↦ by addr_omega [hw, hi, hb, hnx]
  have hn₅ : heapNext t₅ = heapNext t₂ := by simp only [heapNext, m₅, nx₄, m₃]
  have hLlt := (sliceL s k j).isLt
  have hm : (BitVec.ofNat 64 ((sliceL s k j).toNat / 3)).toNat = (sliceL s k j).toNat / 3 := by
    rw [BitVec.toNat_ofNat]; omega
  rw [hm] at hnew
  have kk (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27]) : t₅.getReg r = t₁.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [pr₅.reg _, k₄ _ (by decide), k₃ _ (by decide), pr₂.reg _]
  have regs₅ : ∀ r ∈ [Reg.x9, .x18, .x20, .x21, .x23, .x24, .x25, .x26, .x27],
      t₅.getReg r = u.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [kk _ (by simp), k₁ _ (by decide)]
  refine ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inr ⟨t₂.getMem (s.getReg .x2 - 368), {
    pc := by rw [pc₅, returnAddress_eq, b8000b258_x1 h₄]; rfl
    sp := by rw [pr₅.reg .x2, sp₄]
    x8 := by rw [kk .x8 (by simp), x8₁]
    x22 := by rw [kk .x22 (by simp), x22₁]
    x19 := by rw [kk .x19 (by simp), x19₁]
    regs := regs₅
    m376 := by rw [m₅, v1]
    m368 := by rw [m₅, v2]
    bal := hnew.1
    bnew := by
      rcases hnew.2 with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by rw [← hn₁]; exact h0.1, by rw [hn₅]; omega⟩
    fr := by
      have d2 : DFrame u t₂ fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨
          Within a (s.getReg .x2 - 1088) 48 ∨ Within a nextAddr 8 ∨ Fresh u t₅ a :=
        (DFrame.of_same m₁ _).trans fr₂ fun a ha ↦ by
          rcases ha with ha | ha | ha | ⟨ha1, ha2⟩
          · exact Or.inl ha
          · exact Or.inr (Or.inl ha)
          · exact Or.inr (Or.inr (Or.inl ha))
          · exact Or.inr (Or.inr (Or.inr ⟨by rw [← hn₁]; exact ha1, by rw [hn₅]; exact ha2⟩))
      exact ((d2.trans (DFrame.of_same m₃ _) fun _ h ↦ h).trans fr₄ fun a ha ↦ Or.inl ha).trans
        (DFrame.of_same m₅ _) fun _ h ↦ h
    heap := ⟨by rw [hn₅]; exact heap₂.lo, by rw [hn₅]; exact heap₂.hi⟩
    mono := by rw [hn₅, ← hn₁]; exact mono₂ }⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso.RowsD
