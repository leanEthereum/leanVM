import Rv64Verifier.Proofs.Pcs.VsoGlueClaim

/-!
# `verify_stacked_opening`'s final level: a glued claim's head

`0x8000bb58` loads claim `j`'s scalar into `S - 232` and its fold start `fs` into `s1`, the point's
length into `s2`, a trap if `fs` is past it; `0x8000bb7c` keeps the claim at `S - 872`, the
point's suffix `point + 24 fs` at `S - 848`, its length in `s10`, and branches on the weight's
kind (`GH`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- After `0x8000bb7c`: claim `j` at `a`, its fold start `fs` no more than the point's length. -/
structure GH (OA : MachineState → Word → Model.TState → Prop) (s : MachineState) (x : LCtx)
    (u v w : MachineState) (Wl : Model.Pcs.WhirLocals) (residual tf : List E) (rt w0 : E)
    (j : ℕ) (a : Word) (acc : E) : Prop where
  tb : TB OA s x u v Wl residual tf rt w0
  gs : GS s v w
  jlt : j < (vecLen u (s.getReg .x2 - 664)).toNat
  addr : gAddr u s j = a
  m880 : w.getMem (s.getReg .x2 - 880) =
    vecPtr u (s.getReg .x2 - 664) + vecLen u (s.getReg .x2 - 664) * 88
  fold : gluedFold (Wl.glued.take j) (Wl.folds ++ tf) w0 = some acc
  wt : eAt w (s.getReg .x2 - 184) = acc
  x8 : w.getReg .x8 = a
  x9 : w.getReg .x9 = u.getMem (a + 80)
  x18 : w.getReg .x18 = vecLen v (s.getReg .x2 - 280)
  fsle : (u.getMem (a + 80)).toNat ≤ (vecLen v (s.getReg .x2 - 280)).toNat
  x26 : w.getReg .x26 = BitVec.ofNat 64
    ((vecLen v (s.getReg .x2 - 280)).toNat - (u.getMem (a + 80)).toNat)
  m872 : w.getMem (s.getReg .x2 - 872) = a
  m848 : w.getMem (s.getReg .x2 - 848) = vecPtr v (s.getReg .x2 - 280) +
    BitVec.ofNat 64 (24 * (u.getMem (a + 80)).toNat)
  scalar : eAt w (s.getReg .x2 - 232) = eAt u (a + 56)
  pc : w.pc = if u.getMem a = 0xffffffffffffffff then 0x8000bad0 else 0x8000bba8

/-- The claim's word at `a + o`, kept since `u`. -/
theorem TI.claimWord {OA : MachineState → Word → Model.TState → Prop} {s : MachineState}
    {x : LCtx} {u w : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E}
    (hpre : VsoPre s) (h : TI OA s x u w Wl residual) {j : ℕ}
    (hj : j < (vecLen u (s.getReg .x2 - 664)).toNat) (o : ℕ) (ho : o + 8 ≤ 88) :
    w.getMem (gAddr u s j + BitVec.ofNat 64 o) = u.getMem (gAddr u s j + BitVec.ofNat 64 o) := by
  obtain ⟨e, h1, h2, -⟩ := h.fin.claimAt hj
  have hs := h.fin.hs
  have hhu := h.fin.heap.hi
  simp only [heapEnd] at hhu
  exact h.keepHeap hpre (by addr_omega [e, h1, h2, hs, hhu, ho]) (by addr_omega [e, h1, h2, hs, hhu, ho])

theorem word_mul24 (F : Word) : F * 16 + F * 8 = BitVec.ofNat 64 (24 * F.toNat) := by
  bv_omega

/-- **A claim's head**: `0x8000bb58` and `0x8000bb7c`, or the trap past the point's end. -/
theorem claimHead {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v w : MachineState} {Wl : Model.Pcs.WhirLocals} {residual tf : List E} {rt w0 : E} {j : ℕ}
    {acc : E} (hpre : VsoPre s) (h : GLI OA s x u v w Wl residual tf rt w0 j acc) :
    ∃ w', Reaches Image.code w w' ∧
      (Dead Image.code w' ∨ GH OA s x u v w' Wl residual tf rt w0 j (gAddr u s j) acc) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.gs.sp
  have T := GS.ti hpre h.tb h.gs
  have kw := T.claimWord hpre h.jlt
  obtain ⟨ea, ha1, ha2, ha8⟩ := h.tb.toTI.fin.claimAt h.jlt
  have hs := h.tb.toTI.fin.hs
  have hhs := hpre.heap.lo
  have hhu := h.tb.toTI.fin.heap.hi
  simp only [heapEnd] at hhu
  have hx8 := h.x8
  obtain ⟨a, haddr⟩ : ∃ a, gAddr u s j = a := ⟨_, rfl⟩
  rw [haddr] at kw ea ha1 ha2 ha8 hx8
  rw [haddr]
  have hR : Region a 88 := heap_region (by simp only [heapStart, heapNext] at hhs hs ⊢; omega)
    (by simp only [heapEnd]; omega) ha8
  -- `0x8000bb58`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bb58_spec h.pc (by
    rv_eval [hsp, hx8]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hR (by addr_omega [ha2, hhu]) (by addr_omega [ha2, hhu])
          (by addr_omega [ha2, hhu, ha8]))
  have k₁ := b8000bb58_keeps h₁
  have F₁ : DFrame w t₁ fun y ↦ Within y (s.getReg .x2 - 232) 24 := by
    have := DFrame.of_memFrame (b8000bb58_frame h₁ (by rw [hsp]; addr_omega [hb]))
    rw [hsp] at this
    exact this.mono fun y hy ↦ by addr_omega [hy, hb]
  obtain ⟨G₁, n₁⟩ := h.gs.stepS hpre F₁ (fun y hy ↦ Or.inr (Or.inr (Or.inr (Or.inl (by
    addr_omega [hy, hb]))))) (k₁ .x2 (by decide))
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₁.sp
  -- the point's length and the fold start
  have hP := h.tb.point
  have e776 : w.getMem (s.getReg .x2 - BitVec.ofNat 64 1040 + 776) = vecLen v (s.getReg .x2 - 280) := by
    rw [show s.getReg .x2 - BitVec.ofNat 64 1040 + 776 = s.getReg .x2 - 280 + 16 by addr_omega [hb]]
    exact h.gs.keepStk hpre (Or.inr (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))))
  have e80 : w.getMem (a + 80) = u.getMem (a + 80) := kw 80 (by decide)
  by_cases hfs : (vecLen v (s.getReg .x2 - 280)).toNat < (u.getMem (a + 80)).toNat
  · refine ⟨t₁, r₁, Or.inl (dead_of_fetch ?_)⟩
    rw [b8000bb58_pc_taken h₁ (by rw [hsp, e776, hx8, e80]; exact hfs)]
    exact trap
  have pc₁ := b8000bb58_pc_not_taken h₁ (by rw [hsp, e776, hx8, e80]; omega)
  -- `0x8000bb7c`
  have x8₁ : t₁.getReg .x8 = a := by rw [k₁ .x8 (by decide), hx8]
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b8000bb7c_spec pc₁ (by
    rv_eval [sp₁, x8₁]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hR (by addr_omega [ha2, hhu]) (by addr_omega [ha2, hhu])
          (by addr_omega [ha2, hhu, ha8]))
  have k₂ := b8000bb7c_keeps h₂
  have F₂ : DFrame t₁ t₂ fun y ↦ Within y (s.getReg .x2 - 872) 8 ∨
      Within y (s.getReg .x2 - 848) 8 :=
    (holds_dframe h₂).mono fun y ⟨k, hk, hw⟩ ↦ by
      simp only [b8000bb7c, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [sp₁] at hw <;>
        first | exact Or.inl (by addr_omega [hw, hb]) | exact Or.inr (by addr_omega [hw, hb])
  obtain ⟨G₂, n₂⟩ := G₁.stepS hpre F₂ (fun y hy ↦ by
    rcases hy with hy | hy
    · exact Or.inl (by addr_omega [hy, hb])
    · exact Or.inr (Or.inl (by addr_omega [hy, hb]))) (k₂ .x2 (by decide))
  have kw₂ := (GS.ti hpre h.tb G₂).claimWord hpre h.jlt
  rw [haddr] at kw₂
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  -- the words `0x8000bb58` read, as at `u`
  have m808 := b8000bb58_m_x2_808 h₁
  have m816 := b8000bb58_m_x2_816 h₁
  have m824 := b8000bb58_m_x2_824 h₁
  have c56 : w.getMem (a + 56) = u.getMem (a + 56) := kw 56 (by decide)
  have c64 : w.getMem (a + 64) = u.getMem (a + 64) := kw 64 (by decide)
  have c72 : w.getMem (a + 72) = u.getMem (a + 72) := kw 72 (by decide)
  rw [hsp, hx8, c56] at m808
  rw [hsp, hx8, c64] at m816
  rw [hsp, hx8, c72] at m824
  rv_eval [] at m808 m816 m824
  have x9₁ : t₁.getReg .x9 = u.getMem (a + 80) := by rw [b8000bb58_x9 h₁, hx8, e80]
  have x18₁ : t₁.getReg .x18 = vecLen v (s.getReg .x2 - 280) := by rw [b8000bb58_x18 h₁, hsp, e776]
  have kS (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 872).toNat ∨
      (s.getReg .x2 - 864).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 848).toNat ∨
      (s.getReg .x2 - 840).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 232).toNat ∨
      (s.getReg .x2 - 208).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₂.getMem y = w.getMem y := by
    rw [F₂ y fun i hi hw ↦ by rcases hw with hw | hw <;> rcases hy with hy | hy | hy | hy <;>
      addr_omega [hw, hi, hy, hb]]
    exact F₁ y fun i hi hw ↦ by rcases hy with hy | hy | hy | hy <;> addr_omega [hw, hi, hy, hb]
  have kS₁ (y : Word) (hy : Within y (s.getReg .x2 - 232) 24) (hy8 : y.toNat % 8 = 0) :
      t₂.getMem y = t₁.getMem y :=
    F₂ y fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hy, hy8, hb]
  have e0 : t₁.getMem a = u.getMem a := by
    have := kw₂ 0 (by decide)
    rw [add_ofNat_zero] at this
    rw [← this]
    exact (F₂ a fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb, ha2, hhu, hab]).symm
  refine ⟨t₂, r₁.trans r₂, Or.inr {
    tb := h.tb
    gs := G₂
    jlt := h.jlt
    addr := haddr
    m880 := by rw [kS _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.m880
    fold := h.fold
    wt := by
      rw [← h.wt]
      exact ((F₁.mono fun y hy ↦ Or.inl hy).trans F₂ fun y hy ↦ Or.inr hy).eAt fun i hi hw ↦ by
        rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb]
    x8 := by rw [k₂ .x8 (by decide), x8₁]
    x9 := by rw [k₂ .x9 (by decide), x9₁]
    x18 := by rw [k₂ .x18 (by decide), x18₁]
    fsle := by omega
    x26 := by
      rw [b8000bb7c_x26 h₂, x18₁, x9₁]
      have := hfs
      bv_omega
    m872 := by
      have := b8000bb7c_m_x2_168 h₂
      rw [sp₁, x8₁] at this; rv_eval [] at this; exact this
    m848 := by
      have := b8000bb7c_m_x2_192 h₂
      rw [sp₁, x9₁] at this; rv_eval [] at this
      have e272 : w.getMem (s.getReg .x2 - 272) = vecPtr v (s.getReg .x2 - 280) := by
        rw [show vecPtr v (s.getReg .x2 - 280) = v.getMem (s.getReg .x2 - 272) by
          simp only [vecPtr]; rv_eval []]
        exact h.gs.keepStk (y := s.getReg .x2 - 272) hpre
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))))
      have f272 : t₁.getMem (s.getReg .x2 - 272) = w.getMem (s.getReg .x2 - 272) :=
        F₁ _ fun i hi hw ↦ by addr_omega [hw, hi, hb]
      rw [this, word_mul24, f272, e272]
    scalar := by
      simp only [eAt]
      rw [kS₁ _ (by addr_omega [hb]) (by addr_omega [hb]), kS₁ _ (by addr_omega [hb]) (by addr_omega [hb]),
        kS₁ _ (by addr_omega [hb]) (by addr_omega [hb])]
      rv_eval [m808, m816, m824]
    pc := by
      by_cases ht : u.getMem a = 0xffffffffffffffff
      · simp only [ht, ↓reduceIte]; exact b8000bb7c_pc_taken h₂ (by rw [x8₁, e0]; exact ht)
      · simp only [ht, ↓reduceIte]; exact b8000bb7c_pc_not_taken h₂ (by rw [x8₁, e0]; exact ht) }⟩

end Rv64Verifier.Proofs.Pcs.Vso
