import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Blocks.F53

/-!
# `verifier::multilinear::poly_eval`

```rust
pub fn poly_eval(coefficients: &[E], point: E) -> E {
    coefficients.iter().rev().fold(ZERO, |acc, &c| acc * point + c)
}
```

compiled at `0x8000cef4` (`Blocks/F53.lean`): `a3` points at `point`. `0x8000cef4` zeroes the
result and returns (`0x8000cfc0`) for no coefficients; `0x8000cf04` makes a 96-byte frame, `s2`
points at the last coefficient's `c2` and `s3 = -24 len` counts up to zero; the loop loads the
coefficient into `s4`..`s6`, calls `mul(sp + 8, result, point)` (`0x8000cf4c`), and writes the
product plus the coefficient to the result (`0x8000cf6c`); `0x8000cf9c` restores and returns.
-/

namespace Rv64Verifier.Proofs.Multilinear.PolyEval
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Contracts
  Rv64Verifier.MultilinearContracts Rv64Verifier.MultilinearWords Rv64Verifier.Blocks.F53
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

@[rv_addr] def len (s : MachineState) : Nat := (s.getReg .x12).toNat

def coeffs (s : MachineState) : List E := eListAt s (s.getReg .x11) (len s)

def pt (s : MachineState) : E := eAt s (s.getReg .x13)

/-- The accumulator after `k` coefficients, from the last. -/
def acc (s : MachineState) (k : Nat) : E :=
  ((coeffs s).reverse.take k).foldl (fun a c ↦ a * pt s + c) 0

def kept : List Reg := [.x23, .x24, .x25, .x26, .x27]

theorem mem_of_kept {r : Reg} (h : r ∈ kept) (l : List Reg)
    (hl : ∀ r ∈ kept, r ∈ l := by decide) : r ∈ l :=
  hl r h

def Frame (s t : MachineState) : Prop :=
  ∀ a, ¬ Within a (s.getReg .x10) 24 → ¬ Within a (stackLo s polyEvalStack) polyEvalStack →
    t.getMem a = s.getMem a

structure FrameInv (s t : MachineState) : Prop where
  sp : t.getReg .x2 = s.getReg .x2 - 96
  point : t.getReg .x8 = s.getReg .x13
  ret : t.getReg .x9 = s.getReg .x10
  kept : ∀ r ∈ kept, t.getReg r = s.getReg r
  ra : t.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : t.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : t.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : t.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : t.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : t.getMem (s.getReg .x2 - 48) = s.getReg .x20
  s5 : t.getMem (s.getReg .x2 - 56) = s.getReg .x21
  s6 : t.getMem (s.getReg .x2 - 64) = s.getReg .x22
  mem : Frame s t

/-- At the loop head, before the `k`-th coefficient from the last: `s2` at its `c2`, `s3` at
`-24 (len - k)`. -/
structure LoopInv (s t : MachineState) (k : Nat) : Prop extends FrameInv s t where
  acc : eAt t (s.getReg .x10) = acc s k
  lt : k < len s
  pc : t.pc = 0x8000cf4c
  x18 : t.getReg .x18 = s.getReg .x11 + BitVec.ofNat 64 (24 * (len s - 1 - k)) + 16
  x19 : t.getReg .x19 = negW (24 * (len s - k))

structure ExitInv (s t : MachineState) : Prop extends FrameInv s t where
  pc : t.pc = 0x8000cf9c
  value : eAt t (s.getReg .x10) = Model.polyEvalRust (coeffs s) (pt s)

theorem sp_bounds {s : MachineState} (h : PolyEvalPre s) :
    1152 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 := by
  have := h.stack.bounds (by decide) (by decide)
  simp only [polyEvalStack, mulStack] at this
  omega

theorem acc_zero (s : MachineState) : acc s 0 = 0 := by simp [acc]

theorem acc_succ {s : MachineState} {k : Nat} (hk : k < len s) :
    acc s (k + 1) = acc s k * pt s + eAt s (s.getReg .x11 + BitVec.ofNat 64 (24 * (len s - 1 - k))) := by
  have hl : (coeffs s).reverse.length = len s := by simp [coeffs, eListAt_length]
  unfold acc
  rw [List.take_succ_eq_append_getElem (by rw [hl]; exact hk), List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, List.getElem_reverse, coeffs, eListAt_getElem,
    eListAt_length]

theorem acc_len (s : MachineState) : acc s (len s) = Model.polyEvalRust (coeffs s) (pt s) := by
  rw [acc, List.take_of_length_le (by simp [coeffs, eListAt_length])]
  rfl

/-! ## Entry -/

/-- Some coefficients: the result zeroed, the frame, the loop head. -/
theorem setup {s : MachineState} (hpc : s.pc = 0x8000cef4) (hpre : PolyEvalPre s)
    (h0 : s.getReg .x12 ≠ 0) :
    ∃ t, Reaches Image.code s t ∧ LoopInv s t 0 := by
  have hsp := sp_bounds hpre
  have hret := ValidMemRange.bounds hpre.ret (by decide)
  have hC := ValidMemRange.bounds hpre.coeffs (by bv_omega)
  have hrs := hpre.retStack
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000cef4_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.ret [hret])
  have k₀ := b8000cef4_keeps h₀
  have z₀ := b8000cef4_m_x10_0 h₀
  have z₁ := b8000cef4_m_x10_8 h₀
  have z₂ := b8000cef4_m_x10_16 h₀
  have hm₀ := b8000cef4_frame h₀ (by addr_omega [hret])
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000cf04_spec (b8000cef4_pc_not_taken h₀ h0) (by
    rv_eval [k₀ .x2 (by decide)]
    and_intros <;> valid_access hpre.stack.valid [hsp])
  have k₁ := b8000cf04_keeps h₁
  have hm₁ := b8000cf04_frame h₁ (by rw [k₀ .x2 (by decide)]; addr_omega [hsp])
  rw [k₀ .x2 (by decide)] at hm₁
  have ra := b8000cf04_m_x2_n8 h₁
  have s0 := b8000cf04_m_x2_n16 h₁
  have s1 := b8000cf04_m_x2_n24 h₁
  have s2 := b8000cf04_m_x2_n32 h₁
  have s3 := b8000cf04_m_x2_n40 h₁
  have s4 := b8000cf04_m_x2_n48 h₁
  have s5 := b8000cf04_m_x2_n56 h₁
  have s6 := b8000cf04_m_x2_n64 h₁
  simp only [k₀ .x2 (by decide), k₀ .x1 (by decide), k₀ .x8 (by decide), k₀ .x9 (by decide),
    k₀ .x18 (by decide), k₀ .x19 (by decide), k₀ .x20 (by decide), k₀ .x21 (by decide),
    k₀ .x22 (by decide)] at ra s0 s1 s2 s3 s4 s5 s6
  have hx19 := b8000cf04_x19 h₁
  have hx18 := b8000cf04_x18 h₁
  rw [k₀ .x12 (by decide)] at hx19 hx18
  rw [k₀ .x11 (by decide)] at hx18
  refine ⟨t₁, hr₀.trans hr₁, {
    sp := by rw [b8000cf04_x2 h₁, k₀ .x2 (by decide)]
    point := by rw [b8000cf04_x8 h₁, k₀ .x13 (by decide)]
    ret := by rw [b8000cf04_x9 h₁, k₀ .x10 (by decide)]
    kept := fun r hr ↦ by rw [k₁ r (mem_of_kept hr _), k₀ r (mem_of_kept hr _)]
    ra, s0, s1, s2, s3, s4, s5, s6
    mem := fun a h₁ h₂ ↦ (hm₁ a (by addr_omega [h₂, hsp])).trans (hm₀ a h₁)
    acc := by
      rw [acc_zero]
      apply eAt_eq_of_limbs
      rw [hm₁ (s.getReg .x10) (by addr_omega [hret, hrs, hsp]),
        hm₁ (s.getReg .x10 + 8) (by addr_omega [hret, hrs, hsp]),
        hm₁ (s.getReg .x10 + 16) (by addr_omega [hret, hrs, hsp]), z₀, z₁, z₂, Model.limbs_zero]
      rfl
    lt := by addr_omega [h0]
    pc := b8000cf04_pc h₁
    x18 := by rw [hx18]; addr_omega [hC, h0]
    x19 := by
      rw [hx19, mul_negW _ (by omega)]
      rfl }⟩

/-! ## The loop -/

def measure (t : MachineState) : Nat := (0 - t.getReg .x19).toNat

def Done (s t : MachineState) : Prop := ExitInv s t ∨ Dead Image.code t

theorem body (hMul : MulSpec) {s : MachineState} (hpre : PolyEvalPre s) (t : MachineState)
    (hinv : ∃ k, LoopInv s t k) :
    (∃ u, Reaches Image.code t u ∧ Done s u) ∨
      (∃ u, Reaches Image.code t u ∧ (∃ k, LoopInv s u k) ∧ measure u < measure t) := by
  obtain ⟨k, ht⟩ := hinv
  have hsp := sp_bounds hpre
  have hk := ht.lt
  have hret := ValidMemRange.bounds hpre.ret (by decide)
  have hP := ValidMemRange.bounds hpre.point (by decide)
  have hC := ValidMemRange.bounds hpre.coeffs (by simp only [len] at hk; omega)
  have hlen : len s = (s.getReg .x12).toNat := rfl
  have hrs := hpre.retStack
  have hrc := hpre.retCoeffs
  have hrp := hpre.retPoint
  have hcs := hpre.coeffsStack
  have hps := hpre.pointStack
  obtain ⟨pC, hpC⟩ : ∃ p, p = s.getReg .x11 + BitVec.ofNat 64 (24 * (len s - 1 - k)) :=
    ⟨_, rfl⟩
  have hx18 : t.getReg .x18 = pC + 16 := by rw [ht.x18, hpC]
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000cf4c_spec ht.pc (by
    rv_eval [hx18]
    and_intros <;> valid_access hpre.coeffs [hpC, hk, hC])
  have k₁ := b8000cf4c_keeps h₁
  have hum := b8000cf4c_mem_same h₁
  have hu2 : u.getReg .x2 = s.getReg .x2 - 96 := (k₁ .x2 (by decide)).trans ht.sp
  have hu10 := b8000cf4c_x10 h₁
  have hu11 := b8000cf4c_x11 h₁
  have hu12 := b8000cf4c_x12 h₁
  have hu20 := b8000cf4c_x20 h₁
  have hu21 := b8000cf4c_x21 h₁
  have hu22 := b8000cf4c_x22 h₁
  rv_eval [ht.sp, ht.point, ht.ret, hx18] at hu10 hu11 hu12 hu20 hu21 hu22
  have hts (a : Word) (h₁ : ¬ Within a (s.getReg .x10) 24)
      (h₂ : ¬ Within a (stackLo s polyEvalStack) polyEvalStack) : t.getMem a = s.getMem a :=
    ht.mem a h₁ h₂
  rw [hts _ (by addr_omega [hpC, hk, hC, hrc]) (by addr_omega [hpC, hk, hC, hcs, hsp])] at hu20
  rw [hts _ (by addr_omega [hpC, hk, hC, hrc]) (by addr_omega [hpC, hk, hC, hcs, hsp])] at hu21
  rw [hts _ (by addr_omega [hpC, hk, hC, hrc]) (by addr_omega [hpC, hk, hC, hcs, hsp])] at hu22
  have ePt : eAt u (s.getReg .x13) = pt s := by
    unfold pt eAt
    rw [hum, hum, hum, hts _ (by addr_omega [hP, hrp]) (by addr_omega [hP, hps, hsp]),
      hts (s.getReg .x13 + 8) (by addr_omega [hP, hrp]) (by addr_omega [hP, hps, hsp]),
      hts (s.getReg .x13 + 16) (by addr_omega [hP, hrp]) (by addr_omega [hP, hps, hsp])]
  have eAcc : eAt u (s.getReg .x10) = acc s k := by
    rw [← ht.acc]; unfold eAt; rw [hum, hum, hum]
  have hpre' : MulPre u := {
    out := by rw [hu10]; valid_sub hpre.stack.valid [hsp]
    lhs := by rw [hu11]; exact hpre.ret
    rhs := by rw [hu12]; exact hpre.point
    stack := ⟨by valid_sub hpre.stack.valid [hsp, hu2], by addr_omega [hsp, hu2]⟩
    outLhs := by rw [hu10, hu11]; addr_omega [hsp, hret, hrs]
    outRhs := by rw [hu10, hu12]; addr_omega [hsp, hP, hps]
    outStack := by addr_omega [hsp, hu10, hu2]
    lhsStack := by rw [hu11]; addr_omega [hsp, hu2, hret, hrs]
    rhsStack := by rw [hu12]; addr_omega [hsp, hu2, hP, hps]
    rodata := hpre.rodata.frame_two (fun a h₁ h₂ ↦ (hum a).trans (ht.mem a h₁ h₂))
      hpre.retRodata hpre.stackRodata
    stackRodata := by addr_omega [hsp, hu2, hpre.stackRodata] }
  obtain ⟨v, hr₂, ⟨hvpc, hpres, hpost⟩ | hdead⟩ :=
    hMul.call hr₁ (b8000cf4c_pc h₁) hpre'
  swap
  · exact Or.inl ⟨v, hr₂, Or.inr hdead⟩
  have hv2 : v.getReg .x2 = s.getReg .x2 - 96 := (hpres.reg .x2).trans hu2
  have hv9 : v.getReg .x9 = s.getReg .x10 := by
    rw [hpres.reg .x9, k₁ .x9 (by decide), ht.ret]
  have hprod := hpost.value
  rw [hu10, hu11, hu12, ePt, eAcc] at hprod
  obtain ⟨w, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000cf6c_spec
    (by rw [hvpc, returnAddress_eq, b8000cf4c_x1 h₁]; decide +kernel) (by
      rv_eval [hv2, hv9]
      and_intros <;> first
        | valid_access hpre.stack.valid [hsp]
        | valid_access hpre.ret [hret])
  have k₃ := b8000cf6c_keeps h₃
  have w₀ := b8000cf6c_m_x9_0 h₃
  have w₁ := b8000cf6c_m_x9_8 h₃
  have w₂ := b8000cf6c_m_x9_16 h₃
  have hm₃ := b8000cf6c_frame h₃ (by rw [hv9]; addr_omega [hret])
  rv_eval [hv2, hv9, hpres.reg .x20, hpres.reg .x21, hpres.reg .x22, hu20, hu21, hu22]
    at w₀ w₁ w₂ hm₃
  have hacc : eAt w (s.getReg .x10) = acc s (k + 1) := by
    rw [acc_succ hk, ← hpC, ← hprod]
    apply eAt_eq_of_limbs
    rw [limbs_add, limbs_eAt, limbs_eAt, w₀, w₁, w₂]
    rv_eval []
  have hold (a : Word) (ha₁ : (s.getReg .x2).toNat - 64 ≤ a.toNat)
      (ha₂ : a.toNat < (s.getReg .x2).toNat) : w.getMem a = t.getMem a :=
    (hm₃ a (by addr_omega [ha₁, ha₂, hsp, hret, hrs])).trans
      ((hpost.frame a (by addr_omega [ha₁, ha₂, hsp, hu10])
        (by addr_omega [ha₁, ha₂, hsp, hu2])).trans (hum a))
  have hfw : FrameInv s w := {
    sp := (k₃ .x2 (by decide)).trans hv2
    point := by rw [k₃ .x8 (by decide), hpres.reg .x8, k₁ .x8 (by decide), ht.point]
    ret := (k₃ .x9 (by decide)).trans hv9
    kept := fun r hr ↦ by
      rw [k₃ r (mem_of_kept hr _), hpres r (mem_of_kept hr _), k₁ r (mem_of_kept hr _),
        ht.kept r hr]
    ra := (hold _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans ht.ra
    s0 := (hold _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans ht.s0
    s1 := (hold _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans ht.s1
    s2 := (hold _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans ht.s2
    s3 := (hold _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans ht.s3
    s4 := (hold _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans ht.s4
    s5 := (hold _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans ht.s5
    s6 := (hold _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans ht.s6
    mem := fun a h₁ h₂ ↦ (hm₃ a h₁).trans ((hpost.frame a
      (by rw [hu10]; addr_omega [h₂, hsp]) (by addr_omega [h₂, hsp, hu2])).trans
      ((hum a).trans (ht.mem a h₁ h₂))) }
  have hv18 : v.getReg .x18 = pC + 16 := by rw [hpres.reg .x18, k₁ .x18 (by decide), hx18]
  have hv19 : v.getReg .x19 = negW (24 * (len s - k)) := by
    rw [hpres.reg .x19, k₁ .x19 (by decide), ht.x19]
  by_cases hlast : k + 1 = len s
  · refine Or.inl ⟨w, hr₂.trans hr₃, Or.inl {
      toFrameInv := hfw
      pc := b8000cf6c_pc_not_taken h₃ (by rw [hv19, show len s - k = 1 by omega]; exact negW_last)
      value := by rw [hacc, hlast, acc_len] }⟩
  · have hk1 : k + 1 < len s := by omega
    have hsplit : len s - k = len s - (k + 1) + 1 := by omega
    refine Or.inr ⟨w, hr₂.trans hr₃, ⟨k + 1, {
      toFrameInv := hfw
      acc := hacc
      lt := hk1
      pc := b8000cf6c_pc_taken h₃ (by rw [hv19, hsplit]; exact negW_add_ne (by omega) (by omega))
      x18 := by rw [b8000cf6c_x18 h₃, hv18]; addr_omega [hpC, hk1, hC]
      x19 := by rw [b8000cf6c_x19 h₃, hv19, hsplit, negW_add (by omega) (by omega)] }⟩, ?_⟩
    simp only [measure]
    rw [b8000cf6c_x19 h₃, hv19, ht.x19, hsplit, negW_add (by omega) (by omega),
      neg_negW (by omega), neg_negW (by omega)]
    omega

/-! ## The epilogue -/

theorem exit {s t : MachineState} (hpre : PolyEvalPre s) (ht : ExitInv s t) :
    ∃ u, Reaches Image.code t u ∧ u.pc = returnAddress s ∧ Preserves s u ∧
      eAt u (s.getReg .x10) = Model.polyEvalRust (coeffs s) (pt s) ∧ Frame s u := by
  have hsp := sp_bounds hpre
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b8000cf9c_spec ht.pc (by
    rv_eval [ht.sp]
    and_intros <;> valid_access hpre.stack.valid [hsp])
  have k := b8000cf9c_keeps h
  have x1 := b8000cf9c_x1 h
  have x2 := b8000cf9c_x2 h
  have x8 := b8000cf9c_x8 h
  have x9 := b8000cf9c_x9 h
  have x18 := b8000cf9c_x18 h
  have x19 := b8000cf9c_x19 h
  have x20 := b8000cf9c_x20 h
  have x21 := b8000cf9c_x21 h
  have x22 := b8000cf9c_x22 h
  rv_eval [ht.sp, ht.ra, ht.s0, ht.s1, ht.s2, ht.s3, ht.s4, ht.s5, ht.s6]
    at x1 x2 x8 x9 x18 x19 x20 x21 x22
  have hum := b8000cf9c_mem_same h
  obtain ⟨v, hr', h'⟩ := Sym.BlockSpec.reaches b8000cfc0_spec (b8000cf9c_pc h) trivial
  have k' := b8000cfc0_keeps h'
  have hvm := b8000cfc0_mem_same h'
  have kk (r : Reg) (hr : r ∈ calleeSaved) : v.getReg r = u.getReg r := k' r (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h])
  refine ⟨v, hr.trans hr', ?_, ?_, ?_, fun a h₁ h₂ ↦ (hvm a).trans ((hum a).trans (ht.mem a h₁ h₂))⟩
  · rw [b8000cfc0_pc h', x1, returnAddress_eq]
  · refine preserves_of ((kk .x2 (by decide)).trans x2) ((kk .x8 (by decide)).trans x8)
      ((kk .x9 (by decide)).trans x9) ((kk .x18 (by decide)).trans x18)
      ((kk .x19 (by decide)).trans x19) fun r hr ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (kk .x20 (by decide)).trans x20
    · exact (kk .x21 (by decide)).trans x21
    · exact (kk .x22 (by decide)).trans x22
    all_goals exact (kk _ (by decide)).trans ((k _ (by decide)).trans (ht.kept _ (by decide)))
  · rw [← ht.value]; unfold eAt; rw [hvm, hvm, hvm, hum, hum, hum]

/-! ## `poly_eval` -/

/-- **`poly_eval` meets its contract**, given `mul`'s. -/
theorem poly_eval_spec (hMul : MulSpec) : PolyEvalSpec := by
  intro s hpc hpre
  by_cases h0 : s.getReg .x12 = 0
  · have hret := ValidMemRange.bounds hpre.ret (by decide)
    obtain ⟨t, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000cef4_spec hpc (by
      rv_eval []
      and_intros <;> valid_access hpre.ret [hret])
    have k₀ := b8000cef4_keeps h₀
    obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000cfc0_spec (b8000cef4_pc_taken h₀ h0) trivial
    have hm := b8000cef4_frame h₀ (by addr_omega [hret])
    have hum := b8000cfc0_mem_same h₁
    refine ⟨u, hr₀.trans hr₁, Or.inl ⟨?_, fun r hr ↦ ?_, ?_, fun a h _ ↦ (hum a).trans (hm a h)⟩⟩
    · rw [b8000cfc0_pc h₁, k₀ .x1 (by decide), returnAddress_eq]
    · rw [b8000cfc0_keeps h₁ r (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]),
        k₀ r (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h])]
    · have hz : (s.getReg .x12).toNat = 0 := by rw [h0]; rfl
      rw [hz]
      apply eAt_eq_of_limbs
      rw [hum, hum, hum, b8000cef4_m_x10_0 h₀, b8000cef4_m_x10_8 h₀, b8000cef4_m_x10_16 h₀]
      rfl
  · obtain ⟨t, hst, ht⟩ := setup hpc hpre h0
    obtain ⟨u, htu, hu⟩ := Reaches.loop (fun t ↦ ∃ k, LoopInv s t k) measure (Done s)
      (body hMul hpre) t ⟨0, ht⟩
    rcases hu with hu | hdead
    · obtain ⟨v, huv, hvpc, hpres, hval, hframe⟩ := exit hpre hu
      exact ⟨v, hst.trans (htu.trans huv), Or.inl ⟨hvpc, hpres, hval, hframe⟩⟩
    · exact ⟨u, hst.trans htu, Or.inr hdead⟩

end Rv64Verifier.Proofs.Multilinear.PolyEval
