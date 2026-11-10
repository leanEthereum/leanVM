import Rv64Verifier.Proofs.Pcs.VsoGlueProdsCoord

/-!
# `verify_stacked_opening`'s final level: one query's product

From `0x8000bea8` (`PrQ`): query `i`'s weight to `S - 128`; with an empty point straight to
`0x8000be84`, else `0x8000bee0` loads the query, the counters and the pointers, and the coordinates
run (`prInner`) to `0x8000be84` (`PrE`). `prNext`: `0x8000be84` adds the product to the sum and goes
on with the next query, or to `0x8000baf8` after the last.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  Rv64Verifier.FieldContracts LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem pr_mul24 (F : Word) : F * 16 + F * 8 = BitVec.ofNat 64 (24 * F.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h16 : (16 : Word).toNat = 16 := rfl
  have h8 : (8 : Word).toNat = 8 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h16, h8]
  omega

/-- The coordinates, from `c` on. -/
theorem prInner (hBM : BaseMulSpec) (hMK : MulKSpec) (hM : MulSpec) (hSq : KSquareSpec)
    {s v w : MachineState} {n cnt i : ℕ} {rs : List K} {xs : List E}
    {qs : List (BitVec 64)} {qw : List E} {total : E} (a0 : E × K) (hpre : VsoPre s)
    (hc : QC s v w n rs xs qs qw) : ∀ k c t, n - c = k →
      PrI s v w t n cnt i c total ((xs.zipIdx.take c).foldl (prG rs) a0) →
      ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨
        PrE s v w t' n cnt i total (xs.zipIdx.foldl (prG rs) a0).1) := by
  have hxl : xs.length = n := by rw [← hc.xs, eListAt_length]
  intro k
  induction k with
  | zero => intro c t hk h; have := h.clt; omega
  | succ k ih =>
    intro c t hk h
    have hcn := h.clt
    have hz : xs.zipIdx[c]'(by rw [List.length_zipIdx]; omega) = (xs.getD c 0, c) := by
      rw [List.getElem_zipIdx, List.getD_eq_getElem _ _ (by omega)]
      simp
    obtain ⟨t', r, h'⟩ := prCoord hBM hMK hM hSq hpre hc h
    have e := pr_foldl_take_succ (prG rs) a0 xs.zipIdx (i := c) (by rw [List.length_zipIdx]; omega)
    rw [hz] at e
    rw [← e] at h'
    rcases h' with hd | ⟨hlt, h'⟩ | ⟨heq, h'⟩
    · exact ⟨t', r, Or.inl hd⟩
    · obtain ⟨t'', r', h''⟩ := ih (c + 1) t' (by omega) h'
      exact ⟨t'', r.trans r', h''⟩
    · rw [List.take_of_length_le (by rw [List.length_zipIdx]; omega)] at h'
      exact ⟨t', r, Or.inr h'⟩

/-- **One query's product**, from `0x8000bea8` to `0x8000be84`. -/
theorem prQuery (hBM : BaseMulSpec) (hMK : MulKSpec) (hM : MulSpec) (hSq : KSquareSpec)
    {s v w t : MachineState} {n cnt i : ℕ} {rs : List K} {xs : List E}
    {qs : List (BitVec 64)} {qw : List E} {total : E} (hpre : VsoPre s)
    (hc : QC s v w n rs xs qs qw)
    (hcnt : cnt ≤ (w.getReg .x19).toNat ∧ cnt ≤ (w.getReg .x23).toNat)
    (h : PrQ s v w t n cnt i total) :
    ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨
      PrE s v w t' n cnt i total (prProd rs xs (qw.getD i 0) (qs.getD i 0))) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.gs.sp
  have hab := hst.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  have hhs := hpre.heap.lo
  have hsw := hc.gs.su
  have hhw := hc.gs.heap.hi
  simp only [heapEnd] at hhw
  have hil := h.ilt
  have hxl : xs.length = n := by rw [← hc.xs, eListAt_length]
  obtain ⟨wp8, wpb⟩ := hc.wp
  obtain ⟨qp8, qpb⟩ := hc.qp
  have wpb' := wpb.resolve_left (by omega)
  have qpb' := qpb.resolve_left (by omega)
  have hqw := hc.qw
  have hqs := hc.qs
  have hplen := hc.plen
  generalize hwpd : w.getMem (s.getReg .x2 - 824) = wp at wp8 wpb' hqw
  generalize hqpd : w.getMem (s.getReg .x2 - 856) = qp at qp8 qpb' hqs
  simp only [heapStart, heapNext] at hhs hsw
  have hRw : Region wp (24 * (w.getReg .x19).toNat) := heap_region
    (by simp only [heapNext] at wpb'; omega) (by simp only [heapEnd]; omega) wp8
  have hRq : Region qp (8 * (w.getReg .x23).toNat) := heap_region
    (by simp only [heapNext] at qpb'; omega) (by simp only [heapEnd]; omega) qp8
  have kS (y : Word) (hy : PrK s y) : t.getMem y = w.getMem y := h.keep hpre hy
  have m824 : t.getMem (s.getReg .x2 - 824) = wp := by
    rw [kS _ (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)))]; exact hwpd
  have m856 : t.getMem (s.getReg .x2 - 856) = qp := by
    rw [kS _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))]; exact hqpd
  have hx8 := h.x8
  have hm24 : t.getReg .x8 * 16 + t.getReg .x8 * 8 = BitVec.ofNat 64 (24 * i) := by
    rw [pr_mul24, hx8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hw24 : (wp + BitVec.ofNat 64 (24 * i)).toNat = wp.toNat + 24 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by simp only [heapNext] at wpb'; omega)]
  -- `0x8000bea8`: the query's weight to `S - 128`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bea8_spec h.pc (by
    rv_eval [hsp, m824, hm24]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hRw (by addr_omega [hw24, wpb', hhw, hcnt, hil])
          (by addr_omega [hw24, wpb', hhw, hcnt, hil]) (by addr_omega [hw24, wp8, wpb', hhw, hcnt, hil]))
  have k₁ := b8000bea8_keeps h₁
  have F₁ : DFrame t t₁ fun y ↦ Within y (s.getReg .x2 - 128) 24 := by
    have := DFrame.of_memFrame (b8000bea8_frame h₁ (by rw [hsp]; addr_omega [hb]))
    rw [hsp] at this
    exact this.mono fun y hy ↦ by addr_omega [hy, hb]
  have P₁ := h.toPrX.step hpre F₁ (fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb])))
    (k₁ .x2 (by decide)) (k₁ .x22 (by decide))
  have kH (y : Word) (hy : y.toNat + 8 ≤ heapEnd) : t.getMem y = w.getMem y := kS y (Or.inl hy)
  have kH₁ (y : Word) (hy : y.toNat + 8 ≤ heapEnd) : t₁.getMem y = w.getMem y :=
    P₁.keep hpre (Or.inl hy)
  have e128 : eAt t₁ (s.getReg .x2 - 128) = qw.getD i 0 := by
    have m0 := b8000bea8_m_x2_912 h₁
    have m1 := b8000bea8_m_x2_920 h₁
    have m2 := b8000bea8_m_x2_928 h₁
    rw [hsp] at m0 m1 m2
    rv_eval [m824, hm24] at m0 m1 m2
    rw [← hqw, pr_eListAt_getD _ _ (by omega : i < (w.getReg .x19).toNat)]
    refine eAt_congr ?_ ?_ ?_
    · rw [m0]; exact kH _ (by simp only [heapEnd]; addr_omega [hw24, wpb', hhw, hcnt, hil])
    · rv_eval [m1]; exact kH _ (by simp only [heapEnd]; addr_omega [hw24, wpb', hhw, hcnt, hil])
    · rv_eval [m2]; exact kH _ (by simp only [heapEnd]; addr_omega [hw24, wpb', hhw, hcnt, hil])
  have m816 : t.getMem (s.getReg .x2 - 816) = w.getMem (s.getReg .x2 - 816) :=
    kS _ (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)))
  have m808 : t.getMem (s.getReg .x2 - 808) = w.getMem (s.getReg .x2 - 808) :=
    kS _ (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)))
  have x8₁ : t₁.getReg .x8 = BitVec.ofNat 64 i := (k₁ .x8 (by decide)).trans hx8
  have tot₁ : E.ofLimbs (BF64.ofBitVec (t₁.getReg .x23)) (BF64.ofBitVec (t₁.getReg .x25))
      (BF64.ofBitVec (t₁.getReg .x24)) = total := by
    rw [k₁ .x23 (by decide), k₁ .x24 (by decide), k₁ .x25 (by decide)]; exact h.tot
  by_cases hn0 : n = 0
  · -- an empty point: the product is the weight
    have pc₁ := b8000bea8_pc_taken h₁ (by
      rw [hsp]; rv_eval []; rw [m816, m808]; apply BitVec.eq_of_toNat_eq; omega)
    have hx0 : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨t₁, r₁, Or.inr {
      toPrX := P₁
      pc := pc₁
      ilt := hil
      x8 := x8₁
      tot := tot₁
      prod := by rw [e128, hx0]; rfl }⟩
  have pc₁ := b8000bea8_pc_not_taken h₁ (by
    rw [hsp]; rv_eval []; rw [m816, m808]; intro he
    have := congrArg BitVec.toNat he; omega)
  -- `0x8000bee0`: the query, the counters, the pointers
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₁.gs.sp
  have x10₁ : t₁.getReg .x10 = BitVec.ofNat 64 (8 * i) := by
    rw [b8000bea8_x10 h₁, hx8]
    apply BitVec.eq_of_toNat_eq
    have h8 : (8 : Word).toNat = 8 := rfl
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h8, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have kS₁ (y : Word) (hy : PrK s y) : t₁.getMem y = w.getMem y := P₁.keep hpre hy
  have m856₁ : t₁.getMem (s.getReg .x2 - 856) = qp := by
    rw [kS₁ _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))]; exact hqpd
  have hq8 : (qp + BitVec.ofNat 64 (8 * i)).toNat = qp.toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by simp only [heapNext] at qpb'; omega)]
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b8000bee0_spec pc₁ (by
    rv_eval [sp₁, m856₁, x10₁]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hRq (by addr_omega [hq8, qpb', hhw, hcnt, hil])
          (by addr_omega [hq8, qpb', hhw, hcnt, hil]) (by addr_omega [hq8, qp8, qpb', hhw, hcnt, hil]))
  have k₂ := b8000bee0_keeps h₂
  have P₂ := P₁.same hpre (b8000bee0_mem_same h₂) (k₂ .x2 (by decide)) (k₂ .x22 (by decide))
  have hqv : t₂.getReg .x19 = qs.getD i 0 := by
    rw [b8000bee0_x19 h₂, sp₁]
    rv_eval [m856₁, x10₁]
    rw [kH₁ _ (by simp only [heapEnd]; addr_omega [hq8, qpb', hhw, hcnt, hil]), ← hqs,
      readWords_getD _ _ _ _ (by omega)]
  have hI : PrI s v w t₂ n cnt i 0 total ((xs.zipIdx.take 0).foldl (prG rs)
      (qw.getD i 0, BF64.ofBitVec (qs.getD i 0))) := {
    toPrX := P₂
    pc := b8000bee0_pc h₂
    ilt := hil
    clt := by omega
    x8 := (k₂ .x8 (by decide)).trans x8₁
    tot := by rw [k₂ .x23 (by decide), k₂ .x24 (by decide), k₂ .x25 (by decide)]; exact tot₁
    x9 := by
      rw [b8000bee0_x9 h₂, sp₁, Nat.sub_zero]; rv_eval []; exact P₁.m832
    x18 := by
      rw [b8000bee0_x18 h₂, sp₁, Nat.mul_zero, add_ofNat_zero]; rv_eval []
      exact kS₁ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))))
    x20 := by
      rw [b8000bee0_x20 h₂, sp₁, Nat.mul_zero, add_ofNat_zero]; rv_eval []
      exact kS₁ _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))
    x21 := by
      rw [b8000bee0_x21 h₂, sp₁, Nat.mul_zero, add_ofNat_zero]; rv_eval []; exact P₁.m792
    x27 := by
      rw [b8000bee0_x27 h₂, sp₁, Nat.sub_zero]; rv_eval []; exact P₁.m840
    prod := by
      rw [show eAt t₂ (s.getReg .x2 - 128) = eAt t₁ (s.getReg .x2 - 128) by
        simp only [eAt, b8000bee0_mem_same h₂], e128]
      rfl
    basis := by rw [hqv]; rfl }
  obtain ⟨t₃, r₃, h₃⟩ := prInner hBM hMK hM hSq _ hpre hc n 0 t₂ (by omega) hI
  exact ⟨t₃, r₁.trans (r₂.trans r₃), h₃⟩

/-- **The next query**: `0x8000be84` adds the product to the sum. -/
theorem prNext {s v w t : MachineState} {n cnt i : ℕ} {total p : E} (hpre : VsoPre s)
    (hcnt : cnt < 2 ^ 64) (h : PrE s v w t n cnt i total p) :
    ∃ t', Reaches Image.code t t' ∧ ((i + 1 < cnt ∧ PrQ s v w t' n cnt (i + 1) (total + p)) ∨
      (i + 1 = cnt ∧ t'.pc = 0x8000baf8 ∧ PrX s v w t' n cnt ∧
        E.ofLimbs (BF64.ofBitVec (t'.getReg .x23)) (BF64.ofBitVec (t'.getReg .x25))
          (BF64.ofBitVec (t'.getReg .x24)) = total + p)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.gs.sp
  have hil := h.ilt
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000be84_spec h.pc (by
    rv_eval [hsp]
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000be84_keeps h₁
  have P₁ := h.toPrX.same hpre (b8000be84_mem_same h₁) (k₁ .x2 (by decide)) (k₁ .x22 (by decide))
  have tot₁ : E.ofLimbs (BF64.ofBitVec (t₁.getReg .x23)) (BF64.ofBitVec (t₁.getReg .x25))
      (BF64.ofBitVec (t₁.getReg .x24)) = total + p := by
    rw [b8000be84_x23 h₁, b8000be84_x24 h₁, b8000be84_x25 h₁, hsp, ← h.tot, ← h.prod]
    have e := pr_ofLimbs_add (t := t) (p := s.getReg .x2 - 128) (a := t.getReg .x23)
      (b := t.getReg .x25) (c := t.getReg .x24)
    rv_eval [] at e ⊢
    exact e
  have x8₁ : t₁.getReg .x8 = BitVec.ofNat 64 (i + 1) := by
    rw [b8000be84_x8 h₁, h.x8]
    exact (BitVec.ofNat_add i 1).symm
  have hc : (t.getReg .x8 + 1 = t.getMem (t.getReg .x2 + 240)) ↔ i + 1 = cnt := by
    rw [hsp, h.x8, show s.getReg .x2 - BitVec.ofNat 64 1040 + 240 = s.getReg .x2 - 800 by
      rv_eval [], h.m800, show (1 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt hcnt] at this
      exact this
    · intro he; rw [he]
  by_cases he : i + 1 = cnt
  · exact ⟨t₁, r₁, Or.inr ⟨he, b8000be84_pc_taken h₁ (hc.mpr he), P₁, tot₁⟩⟩
  · exact ⟨t₁, r₁, Or.inl ⟨by omega, {
      toPrX := P₁
      pc := b8000be84_pc_not_taken h₁ (fun h' ↦ he (hc.mp h'))
      ilt := by omega
      x8 := x8₁
      tot := tot₁ }⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
