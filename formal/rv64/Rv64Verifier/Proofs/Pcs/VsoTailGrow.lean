import Rv64Verifier.Proofs.Pcs.VsoTailPush

/-!
# `verify_stacked_opening`'s level tail: room for the intro message

`0x8000b47c` spills `s4` to `S - 904` and compares the pending claims' count with their capacity;
when full, `grow_one` (`0x8000c7d0`) moves them to a new buffer, their bytes copied (`callGrow80B`).
Either way the push at `0x8000b498` follows with room for one more (`Roomy`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `callGrow80`, the old buffer's bytes copied. -/
theorem callGrow80B (hG : GrowOneFreshSpec 0x8000c7d0 80 8) {s t : MachineState} {nx A : Word}
    (hpre : VsoPre s) (hinv : InvR s t nx) (hheap : HeapOk t) (hpc : t.pc = 0x8000c7d0)
    (hx10 : t.getReg .x10 = A)
    (hA : (s.getReg .x2 - 1040).toNat ≤ A.toNat ∧ A.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      A.toNat % 8 = 0)
    (hv : VecOk t A 80 8) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      DFrame t v (fun a ↦ Within a A 16 ∨ Within a (s.getReg .x2 - 1200) 160 ∨
        Within a nextAddr 8 ∨ Fresh t v a) ∧
      vecLen v A = vecLen t A ∧ (vecCap t A).toNat + 1 ≤ (vecCap v A).toNat ∧
      RawVecOk v A 80 8 ∧ NewBuf t v (vecPtr v A) ((vecCap v A).toNat * 80) 8 ∧
      Runtime.bytesAt v (vecPtr v A) ((vecCap t A).toNat * 80) =
        Runtime.bytesAt t (vecPtr t A) ((vecCap t A).toNat * 80))) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := hinv.sp
  have hsl : stackLo t growOneStack = s.getReg .x2 - 1200 := by
    simp only [stackLo, growOneStack, hsp]; rv_eval []
  have hpreG : GrowOnePre 80 8 t := {
    heap := hheap
    self := by rw [hx10]; valid_sub hst.valid [hb, hA]
    raw := by rw [hx10]; exact hv.raw
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := by
      rw [hx10]; exact stack_outside hpre (by addr_omega [hA, hb]) (by addr_omega [hA, hb])
    selfStack := by rw [hx10, hsl]; addr_omega [hA, hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost, hnew⟩ | hdead⟩ := hG.call (Reaches.refl t) hpc hpreG
  swap
  · exact ⟨v, hr, Or.inl hdead⟩
  have hfr := DFrame.of_byteFrame hpost.frame
  rw [hx10, hsl] at hfr
  rw [hx10] at hnew
  have hcap := hpost.cap
  have hraw' := hpost.raw
  have hby := hpost.bytes
  rw [hx10] at hcap hraw' hby
  have hhv := hpost.heap.hi
  have e2 : vecLen v A = vecLen t A := hfr _ fun i hi hx ↦ by
    rcases hx with hx | hx | hx | hx
    · addr_omega [hx, hi, hA]
    · addr_omega [hx, hi, hA, hb]
    · addr_omega [hx, hi, hA, hb, hnx]
    · simp only [Fresh] at hx; addr_omega [hx.2, hi, hA, hb, hhv]
  exact ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono, hfr, e2, hcap, hraw', hnew, hby⟩⟩

/-- At `0x8000b498`, from `t` at `0x8000b47c`: room for one more pending claim. -/
structure Roomy (s t p : MachineState) : Prop where
  pc : p.pc = 0x8000b498
  sp : p.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s p (p.getMem nextAddr)
  heap : HeapOk p
  mono : heapNext t ≤ heapNext p
  fr : DFrame t p fun a ↦ Within a (s.getReg .x2 - 904) 8 ∨ Within a (s.getReg .x2 - 616) 16 ∨
    Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh t p a
  regs : ∀ q ∈ [Reg.x8, .x9, .x19, .x21, .x23, .x26], p.getReg q = t.getReg q
  x22 : p.getReg .x22 = vecLen p (s.getReg .x2 - 616)
  len : vecLen p (s.getReg .x2 - 616) = vecLen t (s.getReg .x2 - 616)
  lt : (vecLen p (s.getReg .x2 - 616)).toNat < (vecCap p (s.getReg .x2 - 616)).toNat
  buf : HS s p (vecPtr p (s.getReg .x2 - 616)) ((vecCap p (s.getReg .x2 - 616)).toNat * 80)
  same : (vecPtr p (s.getReg .x2 - 616) = vecPtr t (s.getReg .x2 - 616) ∧
      vecCap p (s.getReg .x2 - 616) = vecCap t (s.getReg .x2 - 616)) ∨
    NewBuf t p (vecPtr p (s.getReg .x2 - 616)) ((vecCap p (s.getReg .x2 - 616)).toNat * 80) 8
  old : ∀ o, o % 8 = 0 → o + 8 ≤ 80 * (vecLen t (s.getReg .x2 - 616)).toNat →
    p.getMem (vecPtr p (s.getReg .x2 - 616) + BitVec.ofNat 64 o) =
      t.getMem (vecPtr t (s.getReg .x2 - 616) + BitVec.ofNat 64 o)

/-- **`0x8000b47c`**: the pending claims with room for one more, grown if full. -/
theorem room (hG : GrowOneFreshSpec 0x8000c7d0 80 8) {s t : MachineState} (hpre : VsoPre s)
    (hpc : t.pc = 0x8000b47c) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hinv : InvR s t (t.getMem nextAddr)) (hheap : HeapOk t) (hv : VecOk t (s.getReg .x2 - 616) 80 8)
    (hbuf : HS s t (vecPtr t (s.getReg .x2 - 616)) ((vecCap t (s.getReg .x2 - 616)).toNat * 80)) :
    ∃ p, Reaches Image.code t p ∧ (Dead Image.code p ∨ Roomy s t p) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hhi := hheap.hi
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000b47c_spec hpc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000b47c_keeps h₁
  have f₁ := DFrame.of_memFrame (b8000b47c_frame h₁ (by rw [hsp]; addr_omega [hb]))
  rw [hsp, show s.getReg .x2 - 1040 + 136 = s.getReg .x2 - 904 by rv_eval []] at f₁
  obtain ⟨nx₁, inv₁⟩ := InvR.stk hpre hinv f₁ (fun a ha ↦ by addr_omega [ha, hb])
    (k₁ .x2 (by decide))
  have hn₁ : heapNext t₁ = heapNext t := by simp only [heapNext, nx₁]
  have hheap₁ : HeapOk t₁ := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1040 := (k₁ .x2 (by decide)).trans hsp
  have kf (y : Word) (hy : (s.getReg .x2 - 896).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat ∨
      y.toNat + 8 ≤ (s.getReg .x2 - 904).toNat) :
      t₁.getMem y = t.getMem y := f₁ y fun i hi hw ↦ by addr_omega [hw, hi, hy, hb]
  have hA : ∀ o, o < 24 → o % 8 = 0 → t₁.getMem (s.getReg .x2 - 616 + BitVec.ofNat 64 o) =
      t.getMem (s.getReg .x2 - 616 + BitVec.ofNat 64 o) := fun o ho _ ↦
    kf _ (Or.inl (by addr_omega [hb, ho]))
  have c₁ : vecCap t₁ (s.getReg .x2 - 616) = vecCap t (s.getReg .x2 - 616) := by
    simpa only [vecCap, add_ofNat_zero] using hA 0 (by decide) rfl
  have p₁ : vecPtr t₁ (s.getReg .x2 - 616) = vecPtr t (s.getReg .x2 - 616) := hA 8 (by decide) rfl
  have l₁ : vecLen t₁ (s.getReg .x2 - 616) = vecLen t (s.getReg .x2 - 616) := hA 16 (by decide) rfl
  obtain ⟨hP8, hPb⟩ := hbuf
  have hlc := hv.len
  have hold : ∀ o, o % 8 = 0 → o + 8 ≤ 80 * (vecLen t (s.getReg .x2 - 616)).toNat →
      t₁.getMem (vecPtr t (s.getReg .x2 - 616) + BitVec.ofNat 64 o) =
        t.getMem (vecPtr t (s.getReg .x2 - 616) + BitVec.ofNat 64 o) := fun o _ ho ↦
    kf _ (Or.inr (by
      rcases hPb with h0 | h0
      · omega
      · addr_omega [h0, ho, hlc, hhi, hb]))
  have x22₁ : t₁.getReg .x22 = vecLen t (s.getReg .x2 - 616) := by
    rw [b8000b47c_x22 h₁, hsp]; simp only [vecLen]; rv_eval []
  by_cases hfull : vecLen t (s.getReg .x2 - 616) = vecCap t (s.getReg .x2 - 616)
  · -- `grow_one`
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000b48c_spec
      (b8000b47c_pc_not_taken h₁ (by
        rw [hsp]; simp only [vecLen, vecCap] at hfull
        rw [show s.getReg .x2 - 1040 + 440 = s.getReg .x2 - 616 + 16 by rv_eval [],
          show s.getReg .x2 - 1040 + 424 = s.getReg .x2 - 616 by rv_eval []]
        exact hfull)) trivial
    have k₂ := b8000b48c_keeps h₂
    have m₂ := b8000b48c_mem_same h₂
    have inv₂ : InvR s t₂ (t₂.getMem nextAddr) := by
      rw [m₂]; exact Inv.same' inv₁ m₂ (k₂ .x2 (by decide))
    have hn₂ : heapNext t₂ = heapNext t := by simp only [heapNext, m₂]; exact hn₁
    have hv₂ : VecOk t₂ (s.getReg .x2 - 616) 80 8 := by
      have hraw := hv.raw
      simp only [RawVecOk, Buf] at hraw
      refine ⟨?_, ?_⟩
      · simp only [RawVecOk, Buf, vecPtr, vecCap, heapNext, m₂] at hraw ⊢
        simp only [vecPtr, vecCap] at p₁ c₁
        rw [p₁, c₁]; simp only [heapNext] at hn₁; rw [hn₁]; exact hraw
      · simp only [vecLen, vecCap, m₂] at l₁ c₁ ⊢; rw [l₁, c₁]; exact hlc
    obtain ⟨t₃, hr₃, hv₃⟩ := callGrow80B (A := s.getReg .x2 - 616) hG hpre inv₂
      ⟨hn₂ ▸ hheap.lo, hn₂ ▸ hheap.hi⟩ (b8000b48c_pc h₂)
      (by rw [b8000b48c_x10 h₂, sp₁]; rv_eval []) (by addr_omega [hb]) hv₂
    rcases hv₃ with hd | ⟨hpc₃, hpres₃, hheap₃, hmono₃, X₃, hl₃, hc₃, hraw₃, hnb₃, hby₃⟩
    · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inl hd⟩
    have hhi₃ := hheap₃.hi
    have inv₃ := InvR.callT (o := s.getReg .x2 - 616) hpre inv₂ (X₃.mono fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · exact Or.inl (by addr_omega [ha, hb])
        · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ha))))
      (by simp only [Slot24]; addr_omega [hb]) hheap₃ hmono₃ (hpres₃ .x2 (by decide))
    have c₂ : vecCap t₂ (s.getReg .x2 - 616) = vecCap t (s.getReg .x2 - 616) := by
      rw [← c₁]; simp only [vecCap, m₂]
    have p₂ : vecPtr t₂ (s.getReg .x2 - 616) = vecPtr t (s.getReg .x2 - 616) := by
      rw [← p₁]; simp only [vecPtr, m₂]
    have l₂ : vecLen t₂ (s.getReg .x2 - 616) = vecLen t (s.getReg .x2 - 616) := by
      rw [← l₁]; simp only [vecLen, m₂]
    have hsn : heapNext s ≤ heapNext t := hinv.mono
    have hraw := hv.raw
    simp only [RawVecOk, Buf] at hraw
    simp only [NewBuf] at hnb₃
    rw [hn₂] at hnb₃ hmono₃
    have hraw3 := hraw₃
    simp only [RawVecOk, Buf] at hraw3
    refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr {
      pc := by rw [hpc₃, returnAddress_eq, b8000b48c_x1 h₂]; decide
      sp := by rw [hpres₃ .x2 (by decide), k₂ .x2 (by decide), sp₁]
      inv := inv₃
      heap := hheap₃
      mono := hmono₃
      fr := ((f₁.mono fun a ha ↦ Or.inl ha).trans (DFrame.of_same m₂ _) fun _ h ↦ h).trans X₃
        fun a ha ↦ by
          rcases ha with ha | ha | ha | ha
          · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
          · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
          · simp only [Fresh] at ha ⊢; rw [hn₂] at ha; exact Or.inr (Or.inr (Or.inr (Or.inr ha)))
      regs := fun q hq ↦ by
        have h1 : q ∈ calleeSaved := (by decide : ∀ q ∈ [Reg.x8, .x9, .x19, .x21, .x23, .x26],
          q ∈ calleeSaved) q hq
        rw [hpres₃ q h1, k₂ q (mem_of_calleeSaved h1 _), k₁ q ((by decide : ∀ q ∈ [Reg.x8, .x9,
          .x19, .x21, .x23, .x26], q ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12,
          .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27, .x28,
          .x29, .x30, .x31] : List Reg)) q hq)]
      x22 := by rw [hpres₃ .x22 (by decide), k₂ .x22 (by decide), x22₁, hl₃, l₂]
      len := by rw [hl₃, l₂]
      lt := by rw [hl₃, l₂, hfull]; rw [c₂] at hc₃; exact hc₃
      buf := ⟨hraw3.1, by
        rcases hnb₃.2 with h0 | h0
        · exact Or.inl h0
        · exact Or.inr ⟨by omega, h0.2⟩⟩
      same := Or.inr ⟨hnb₃.1, hnb₃.2.imp id fun h ↦ ⟨h.1, h.2⟩⟩
      old := fun o ho hoN ↦ by
        rw [getMem_eq_of_bytesAt hby₃ hraw3.1 (by rw [p₂]; exact hP8) ho (by
          rw [c₂, ← hfull]; omega), p₂, show t₂.getMem _ = t₁.getMem _ from m₂ _]
        exact hold o ho hoN }⟩
  · refine ⟨t₁, hr₁, Or.inr {
      pc := b8000b47c_pc_taken h₁ (by
        rw [hsp]; simp only [vecLen, vecCap] at hfull
        rw [show s.getReg .x2 - 1040 + 440 = s.getReg .x2 - 616 + 16 by rv_eval [],
          show s.getReg .x2 - 1040 + 424 = s.getReg .x2 - 616 by rv_eval []]
        exact hfull)
      sp := sp₁
      inv := inv₁
      heap := hheap₁
      mono := by rw [hn₁]
      fr := f₁.mono fun a ha ↦ Or.inl ha
      regs := fun q hq ↦ k₁ q ((by decide : ∀ q ∈ [Reg.x8, .x9, .x19, .x21, .x23, .x26],
        q ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16,
          .x17, .x18, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30,
          .x31] : List Reg)) q hq)
      x22 := by rw [x22₁, l₁]
      len := l₁
      lt := by
        rw [l₁, c₁]
        have hne : (vecLen t (s.getReg .x2 - 616)).toNat ≠ (vecCap t (s.getReg .x2 - 616)).toNat :=
          fun he ↦ hfull (BitVec.eq_of_toNat_eq he)
        omega
      buf := by rw [p₁, c₁]; simpa only [HS, hn₁] using (⟨hP8, hPb⟩ : HS s t _ _)
      same := Or.inl ⟨p₁, c₁⟩
      old := fun o ho hoN ↦ by rw [p₁]; exact hold o ho hoN }⟩

end Rv64Verifier.Proofs.Pcs.Vso
