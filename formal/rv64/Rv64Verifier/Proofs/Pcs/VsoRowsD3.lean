import Rv64Verifier.Proofs.Pcs.VsoRowsD2

/-!
# `verify_stacked_opening`'s level loop: a deeper level's rows, `ext_row`

From `reserve`'s return (`RowAlloc`, `0x8000b27c`): a row of fewer than three words goes straight
to `dot`; a longer one is copied, `n / 3` `E`s, from its words into the new buffer (`0x8000b28c`,
the loop `copyRow`), to `0x8000b1c8` (`RowCopied`). The buffer then holds `ext_row(row)`
(`rowWords`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso.RowsD
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Row `j` as `E`s: its words from `k`, three at a time. -/
theorem rowWords {s t' k : MachineState} {lf : List E} {ws : List (List K)}
    (C : DCtx s t' k lf ws) {j : ℕ} (hj : j < ws.length) :
    Model.Pcs.extRowRust ws[j] = eListAt k (sliceP s k j) ((sliceL s k j).toNat / 3) := by
  rw [← C.leaves.words j hj, readWords_eq_map, List.map_map, ← extRow_kListAt]
  rfl

/-- From the loop's head to `reserve`'s return, the frame is the rows'. -/
theorem RowAlloc.frK {s k u v : MachineState} {ws : List (List K)} {ker : List E} {O : Word}
    {j : ℕ} {B : Word} (hpre : VsoPre s) (hu : DeepAt s k u ws ker O j) (hv : RowAlloc s k u v j B) :
    DFrame k v (RowW s k v) :=
  (hu.fr.mono fun _ ha ↦ rowW_mono hv.mono ha).trans hv.fr fun a ha ↦ by
    have hb := bounds hpre
    rcases ha with ha | ha | ha | ⟨h1, h2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by have := hu.mono; omega, h2⟩)))))

/-- At `0x8000b1c8`, before `dot`: the buffer `B` holds `ext_row` of the `L` words at `p`. -/
structure RowCopied (s k u w : MachineState) (p L B : Word) : Prop where
  pc : w.pc = 0x8000b1c8
  sp : w.getReg .x2 = s.getReg .x2 - 1040
  x11 : w.getReg .x11 = B
  x12 : w.getReg .x12 = BitVec.ofNat 64 (L.toNat / 3)
  regs : ∀ q ∈ [Reg.x9, .x18, .x20, .x21, .x23, .x24, .x25, .x26, .x27], w.getReg q = u.getReg q
  elems : eListAt w B (L.toNat / 3) = eListAt k p (L.toNat / 3)
  bal : B.toNat % 8 = 0
  bnew : L.toNat / 3 = 0 ∨ heapNext u ≤ B.toNat ∧ B.toNat + 24 * (L.toNat / 3) ≤ heapNext w
  fr : DFrame u w fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨ Within a (s.getReg .x2 - 1088) 48 ∨
    Within a nextAddr 8 ∨ Fresh u w a
  heap : HeapOk w
  mono : heapNext u ≤ heapNext w

/-- **`ext_row`**: from `reserve`'s return to `dot`'s call. -/
theorem rowCopy {s t' k u v : MachineState} {lf : List E} {ws : List (List K)} {ker : List E}
    {O : Word} {j : ℕ} {B : Word} (C : DCtx s t' k lf ws) (hu : DeepAt s k u ws ker O j)
    (hj : j < ws.length) (hv : RowAlloc s k u v j B) :
    ∃ w, Reaches Image.code v w ∧ RowCopied s k u w (sliceP s k j) (sliceL s k j) B := by
  have hpre := C.pre
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := hv.sp
  have hhv := hv.heap
  have hfK := hv.frK hpre hu
  have hbuf := C.leaves.buf j hj
  have hx8v := hv.x8
  have hx22v := hv.x22
  have hx19v := hv.x19
  have hbnew := hv.bnew
  generalize hLd : sliceL s k j = L at hx22v hx19v hbnew hbuf ⊢
  generalize hpd : sliceP s k j = p at hx8v hbuf ⊢
  obtain ⟨m, hmd⟩ : ∃ m, L.toNat / 3 = m := ⟨_, rfl⟩
  rw [hmd] at hx19v hbnew
  have hLlt := L.isLt
  have e376 : v.getMem (v.getReg .x2 + 664) = B := by
    rw [hsp, show s.getReg .x2 - 1040 + 664 = s.getReg .x2 - 376 by rv_eval [], hv.m376]
  have e368 : v.getMem (v.getReg .x2 + 672) = 0 := by
    rw [hsp, show s.getReg .x2 - 1040 + 672 = s.getReg .x2 - 368 by rv_eval [], hv.m368]
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000b27c_spec hv.pc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000b27c_keeps h₁
  have m₁ := b8000b27c_mem_same h₁
  have x11₁ : t₁.getReg .x11 = B := by rw [b8000b27c_x11 h₁, e376]
  have x12₁ : t₁.getReg .x12 = 0 := by rw [b8000b27c_x12 h₁, e368]
  have regs₁ : ∀ q ∈ [Reg.x9, .x18, .x20, .x21, .x23, .x24, .x25, .x26, .x27],
      t₁.getReg q = u.getReg q := by
    intro q hq
    have hq' := hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rw [← hv.regs q hq]
    rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₁ _ (by decide)
  have hhn : heapNext t₁ = heapNext v := by simp only [heapNext, m₁]
  have hv22 : (v.getReg .x22).toNat = L.toNat := by rw [hx22v]
  by_cases h3 : L.toNat < 3
  · -- no full chunk: straight to `dot`
    have hm0 : m = 0 := by omega
    have hpc₁ := b8000b27c_pc_taken h₁ (by rw [hv22]; exact h3)
    refine ⟨t₁, r₁, {
      pc := hpc₁
      sp := (k₁ .x2 (by decide)).trans hsp
      x11 := x11₁
      x12 := by rw [x12₁, hmd, hm0]; rfl
      regs := regs₁
      elems := by rw [hmd, hm0]; rfl
      bal := hv.bal
      bnew := Or.inl (hmd.trans hm0)
      fr := (hv.fr.trans (DFrame.of_same m₁ _) fun _ h ↦ h).mono fun a ha ↦ by
        rcases ha with ha | ha | ha | ⟨h1, h2⟩
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, by rw [hhn]; exact h2⟩))
      heap := ⟨by rw [hhn]; exact hhv.lo, by rw [hhn]; exact hhv.hi⟩
      mono := by rw [hhn]; exact hv.mono }⟩
  -- the copy
  have hm1 : 1 ≤ m := by omega
  have hpc₁ := b8000b27c_pc_not_taken h₁ (by rw [hv22]; show 3 ≤ L.toNat; omega)
  obtain ⟨hpr, hpc⟩ : Region p (8 * L.toNat) ∧ Clear s (heapNext k) p (8 * L.toNat) := by
    rcases hbuf with h0 | h0
    · exact absurd h0 (by omega)
    · exact h0
  have hpb := Region.bounds hpr
  obtain ⟨hB1, hB2⟩ : heapNext u ≤ B.toNat ∧ B.toNat + 24 * m ≤ heapNext v := by
    rcases hbnew with h0 | h0
    · omega
    · exact h0
  have hku := hu.mono
  have hhl := hhv.lo
  have hhh := hhv.hi
  have hhul := hu.heap.lo
  have hmb : m < 2 ^ 62 := by omega
  simp only [heapStart, heapEnd] at hhl hhh hhul
  have hs : Region p (24 * m) := ⟨by simp only [Region, Mapped] at hpr ⊢; omega, hpr.2⟩
  have hd : Region B (24 * m) := heap_region (by omega) (by simp only [heapEnd]; omega) hv.bal
  have hsd : Apart p (24 * m) B (24 * m) := by
    obtain ⟨⟨c1, -, -⟩, -⟩ := hpc
    simp only [Apart]
    rcases c1 with c1 | c1
    · right; right; left; omega
    · right; right; right; simp only [heapEnd] at c1; omega
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b8000b28c_spec hpc₁ trivial
  have k₂ := b8000b28c_keeps h₂
  have m₂ := b8000b28c_mem_same h₂
  have hx8 : t₁.getReg .x8 = p := by rw [k₁ .x8 (by decide), hx8v]
  have hx19 : t₁.getReg .x19 = BitVec.ofNat 64 m := by rw [k₁ .x19 (by decide), hx19v]
  obtain ⟨t₃, r₃, hpc₃, cp₃, fr₃, kr₃⟩ := copyRow hs hd hsd t₂ m 0 t₂ (by omega) (by omega)
    (b8000b28c_pc h₂)
    (by rw [b8000b28c_x8 h₂, hx8]; rfl)
    (by rw [b8000b28c_x10 h₂, x11₁, x12₁]; rv_eval []; rfl)
    (by rw [b8000b28c_x13 h₂, hx8, hx19]; addr_omega [hpb, hm1, hmb, hmd, hLlt])
    (DFrame.refl _ _) fun i hi ↦ absurd hi (by omega)
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000b2dc_spec hpc₃ trivial
  have k₄ := b8000b2dc_keeps h₄
  have m₄ := b8000b2dc_mem_same h₄
  have hm₃ : ∀ a, t₂.getMem a = v.getMem a := fun a ↦ (m₂ a).trans (m₁ a)
  have frB : DFrame v t₄ (Within · B (24 * m)) :=
    ((DFrame.of_same hm₃ _).trans fr₃ fun _ h ↦ h).trans (DFrame.of_same m₄ _) fun _ h ↦ h
  have hn₄ : heapNext t₄ = heapNext v := by
    have e := frB nextAddr fun i hi hw ↦ by addr_omega [hw, hi, hhh, hB2]
    simp only [heapNext, e]
  have rr (q : Reg) (hq : q ∈ [Reg.x2, .x9, .x11, .x18, .x20, .x21, .x23, .x24, .x25, .x26, .x27]) :
      t₄.getReg q = t₁.getReg q := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k₄ _ (by decide), kr₃ _ (by decide), k₂ _ (by decide)]
  refine ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), {
    pc := b8000b2dc_pc h₄
    sp := by rw [rr .x2 (by simp), k₁ .x2 (by decide), hsp]
    x11 := by rw [rr .x11 (by simp), x11₁]
    x12 := by
      rw [hmd, k₄ .x12 (by decide), kr₃ .x12 (by decide), b8000b28c_x12 h₂, x12₁, hx19]
      exact BitVec.zero_add _
    regs := fun q hq ↦ by
      have hq' := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rw [← regs₁ q hq]
      rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact rr _ (by simp)
    elems := by
      rw [hmd]
      have e1 : eListAt t₄ B m = eListAt t₃ B m := by simp only [eListAt, eAt, m₄]
      have e2 : eListAt t₂ p m = eListAt v p m := by simp only [eListAt, eAt, hm₃]
      rw [e1, cp₃.eList, e2]
      exact hfK.eListAt fun i hi hw ↦ clear_notRowW hpre hpc hhv.hi _ (by addr_omega [hpb, hi, hmd, hLlt]) hw
    bal := hv.bal
    bnew := Or.inr ⟨hB1, by rw [hn₄, hmd]; exact hB2⟩
    fr := (hv.fr.trans frB fun a ha ↦ Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, hB1],
        by addr_omega [ha, hB2]⟩))).mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨h1, h2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨h1, by rw [hn₄]; exact h2⟩))
    heap := ⟨by rw [hn₄]; exact hhv.lo, by rw [hn₄]; exact hhh⟩
    mono := by rw [hn₄]; exact hv.mono }⟩

end Rv64Verifier.Proofs.Pcs.Vso.RowsD
