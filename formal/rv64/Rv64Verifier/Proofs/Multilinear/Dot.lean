import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Blocks.F29

/-!
# `verifier::multilinear::dot`

```rust
pub fn dot(left: &[E], right: &[E]) -> E {
    assert_eq!(left.len(), right.len());
    let mut result = ZERO;
    for (&x, &y) in left.iter().zip(right) {
        result += x * y;
    }
    result
}
```

compiled at `0x80007f3c` (`Blocks/F29.lean`): `0x80007f3c` traps if the lengths differ;
`0x80007f40` makes a 96-byte frame and zeroes the result's `c1`, `c2`; `0x80007f74` sets `s1`, `s2`
to `right`, `left`, `s6` to `right`'s end and the accumulator (`s3`, `s5`, `s4`: `c0`, `c1`, `c2`)
to zero; the loop calls `mul` into `sp + 8` (`0x80007f98`) and adds the product into the
accumulator (`0x80007fac`); `0x80007fd0` stores `c1`, `c2`, `0x80007fdc` zeroes `s3` for empty
slices, `0x80007fe0` stores `c0` and returns. The proof follows `Proofs/EqEval.lean`.
-/

namespace Rv64Verifier.Proofs.Multilinear.Dot
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Contracts
  Rv64Verifier.MultilinearContracts Rv64Verifier.Blocks.F29
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

@[rv_addr] def len (s : MachineState) : Nat := (s.getReg .x12).toNat

def left (s : MachineState) : List E := eListAt s (s.getReg .x11) (len s)
def right (s : MachineState) : List E := eListAt s (s.getReg .x13) (len s)

/-- `result` after `k` elements. -/
def acc (s : MachineState) (k : Nat) : E :=
  (List.zipWith (· * ·) ((left s).take k) ((right s).take k)).foldl (· + ·) 0

def kept : List Reg := [.x23, .x24, .x25, .x26, .x27]

theorem mem_of_kept {r : Reg} (h : r ∈ kept) (l : List Reg)
    (hl : ∀ r ∈ kept, r ∈ l := by decide) : r ∈ l :=
  hl r h

/-- Memory changed only in the result and the stack. -/
def Frame (s t : MachineState) : Prop :=
  ∀ a, ¬ Within a (s.getReg .x10) 24 → ¬ Within a (stackLo s dotStack) dotStack →
    t.getMem a = s.getMem a

/-- Inside the frame: `sp`, the result's address in `s0`, the saved registers. -/
structure FrameInv (s t : MachineState) : Prop where
  sp : t.getReg .x2 = s.getReg .x2 - 96
  ret : t.getReg .x8 = s.getReg .x10
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

/-- At the loop head, before element `k`: `s1` walks `right`, `s2` walks `left`. -/
structure LoopInv (s t : MachineState) (k : Nat) : Prop extends FrameInv s t where
  acc : Model.limbs (acc s k) = (t.getReg .x19, t.getReg .x21, t.getReg .x20)
  lt : k < len s
  pc : t.pc = 0x80007f98
  x9 : t.getReg .x9 = s.getReg .x13 + BitVec.ofNat 64 (24 * k)
  x18 : t.getReg .x18 = s.getReg .x11 + BitVec.ofNat 64 (24 * k)
  x22 : t.getReg .x22 = s.getReg .x13 + BitVec.ofNat 64 (24 * len s)

/-- At the epilogue: the result's `c1`, `c2` stored, `c0` in `s3`. -/
structure ExitInv (s t : MachineState) : Prop extends FrameInv s t where
  pc : t.pc = 0x80007fe0
  c0 : t.getReg .x19 = (Model.limbs (Model.dotRust (left s) (right s))).1
  c1 : t.getMem (s.getReg .x10 + 8) = (Model.limbs (Model.dotRust (left s) (right s))).2.1
  c2 : t.getMem (s.getReg .x10 + 16) = (Model.limbs (Model.dotRust (left s) (right s))).2.2

theorem FrameInv.of_same {s t u : MachineState} (h : FrameInv s t)
    (hm : ∀ a, u.getMem a = t.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x23, .x24, .x25, .x26, .x27], u.getReg r = t.getReg r) :
    FrameInv s u where
  sp := (hr _ (by decide)).trans h.sp
  ret := (hr _ (by decide)).trans h.ret
  kept r hr' := (hr r (mem_of_kept hr' _)).trans (h.kept r hr')
  ra := (hm _).trans h.ra
  s0 := (hm _).trans h.s0
  s1 := (hm _).trans h.s1
  s2 := (hm _).trans h.s2
  s3 := (hm _).trans h.s3
  s4 := (hm _).trans h.s4
  s5 := (hm _).trans h.s5
  s6 := (hm _).trans h.s6
  mem a h₁ h₂ := (hm a).trans (h.mem a h₁ h₂)

theorem sp_bounds {s : MachineState} (h : DotPre s) :
    1152 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 := by
  have := h.stack.bounds (by decide) (by decide)
  simp only [dotStack, mulStack] at this
  omega

theorem acc_zero (s : MachineState) : acc s 0 = 0 := by simp [acc]

theorem acc_succ {s : MachineState} {k : Nat} (hk : k < len s) :
    acc s (k + 1) = acc s k + eAt s (s.getReg .x11 + BitVec.ofNat 64 (24 * k)) *
      eAt s (s.getReg .x13 + BitVec.ofNat 64 (24 * k)) := by
  unfold acc
  rw [foldl_zipWith_take_succ _ _ _ _ _ _ (by rw [left, eListAt_length]; exact hk)
    (by rw [right, eListAt_length]; exact hk)]
  simp only [left, right, eListAt_getElem]

theorem acc_len (s : MachineState) : acc s (len s) = Model.dotRust (left s) (right s) := by
  rw [acc, List.take_of_length_le (by simp [left, eListAt_length]),
    List.take_of_length_le (by simp [right, eListAt_length]), Model.dotRust_eq]
  rfl

/-! ## Entry -/

theorem trap : Image.code.fetch 0x8000800c = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

theorem mismatch {s : MachineState} (hpc : s.pc = 0x80007f3c)
    (hne : s.getReg .x12 ≠ s.getReg .x14) :
    ∃ t, Reaches Image.code s t ∧ Dead Image.code t := by
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b80007f3c_spec hpc trivial
  exact ⟨t, hr, dead_of_fetch (by rw [b80007f3c_pc_taken h hne]; exact trap)⟩

/-- Lengths agree: the frame, then the loop head, or the epilogue for empty slices. -/
theorem setup {s : MachineState} (hpc : s.pc = 0x80007f3c) (hpre : DotPre s)
    (hlen : s.getReg .x12 = s.getReg .x14) :
    ∃ t, Reaches Image.code s t ∧ (ExitInv s t ∨ ∃ k, LoopInv s t k) := by
  have hsp := sp_bounds hpre
  have hret := ValidMemRange.bounds hpre.ret (by decide)
  have hrs := hpre.retStack
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b80007f3c_spec hpc trivial
  have k₀ := b80007f3c_keeps h₀
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007f40_spec
    (b80007f3c_pc_not_taken h₀ hlen) (by
      rv_eval [k₀ .x2 (by decide), k₀ .x10 (by decide)]
      and_intros <;> first
        | valid_access hpre.stack.valid [hsp]
        | valid_access hpre.ret [hret]
        | addr_omega [hsp, hret, hrs])
  have k₁ := b80007f40_keeps h₁
  have z₁ := b80007f40_m_x10_8 h₁
  have z₂ := b80007f40_m_x10_16 h₁
  have ra := b80007f40_m_x2_n8 h₁
  have s0 := b80007f40_m_x2_n16 h₁
  have s1 := b80007f40_m_x2_n24 h₁
  have s2 := b80007f40_m_x2_n32 h₁
  have s3 := b80007f40_m_x2_n40 h₁
  have s4 := b80007f40_m_x2_n48 h₁
  have s5 := b80007f40_m_x2_n56 h₁
  have s6 := b80007f40_m_x2_n64 h₁
  simp only [k₀ .x2 (by decide), k₀ .x10 (by decide), k₀ .x1 (by decide), k₀ .x8 (by decide),
    k₀ .x9 (by decide), k₀ .x18 (by decide), k₀ .x19 (by decide), k₀ .x20 (by decide),
    k₀ .x21 (by decide), k₀ .x22 (by decide)] at z₁ z₂ ra s0 s1 s2 s3 s4 s5 s6
  have hmem₁ : Frame s t₁ := fun a ha₁ ha₂ ↦ by
    rw [← b80007f3c_mem_same h₀ a]
    refine h₁.frame a ?_
    rv_eval [k₀ .x2 (by decide), k₀ .x10 (by decide)]
    and_intros <;> first | addr_omega [ha₁, hret] | addr_omega [ha₂, hsp]
  have hf₁ : FrameInv s t₁ := {
    sp := by rw [b80007f40_x2 h₁, k₀ .x2 (by decide)]
    ret := by rw [b80007f40_x8 h₁, k₀ .x10 (by decide)]
    kept := fun r hr ↦ by rw [k₁ r (mem_of_kept hr _), k₀ r (mem_of_kept hr _)]
    ra, s0, s1, s2, s3, s4, s5, s6
    mem := hmem₁ }
  by_cases h0 : s.getReg .x12 = 0
  · have hl0 : len s = 0 := by simp [len, h0]
    have hv : Model.limbs (Model.dotRust (left s) (right s)) = (0, 0, 0) := by
      rw [← acc_len, hl0, acc_zero]; rfl
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007fdc_spec
      (b80007f40_pc_taken h₁ (by rw [k₀ .x12 (by decide)]; exact h0)) trivial
    refine ⟨t₂, hr₀.trans (hr₁.trans hr₂), Or.inl {
      toFrameInv := hf₁.of_same (b80007fdc_mem_same h₂) (h₂.keeps rfl)
      pc := b80007fdc_pc h₂
      c0 := by rw [b80007fdc_x19 h₂, hv]
      c1 := by rw [b80007fdc_mem_same h₂, z₁, hv]
      c2 := by rw [b80007fdc_mem_same h₂, z₂, hv] }⟩
  · obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007f74_spec
      (b80007f40_pc_not_taken h₁ (by rw [k₀ .x12 (by decide)]; exact h0)) trivial
    have hright : ValidMemRange (s.getReg .x13) (3 * (s.getReg .x12).toNat) := hlen ▸ hpre.right
    have hR := ValidMemRange.bounds hright (by bv_omega)
    have hL := ValidMemRange.bounds hpre.left (by bv_omega)
    have k₂ := b80007f74_keeps h₂
    refine ⟨t₂, hr₀.trans (hr₁.trans hr₂), Or.inr ⟨0, {
      toFrameInv := hf₁.of_same (b80007f74_mem_same h₂) (h₂.keeps rfl)
      acc := by rw [acc_zero, b80007f74_x19 h₂, b80007f74_x20 h₂, b80007f74_x21 h₂]; try rfl
      lt := by addr_omega [h0]
      pc := b80007f74_pc h₂
      x9 := by rw [b80007f74_x9 h₂, k₁ .x13 (by decide), k₀ .x13 (by decide)]; simp
      x18 := by rw [b80007f74_x18 h₂, k₁ .x11 (by decide), k₀ .x11 (by decide)]; simp
      x22 := by
        rw [b80007f74_x22 h₂, k₁ .x13 (by decide), k₀ .x13 (by decide), k₁ .x12 (by decide),
          k₀ .x12 (by decide)]
        addr_omega [hR] }⟩⟩

/-! ## The loop -/

def measure (t : MachineState) : Nat := (t.getReg .x22).toNat - (t.getReg .x9).toNat

def Done (s t : MachineState) : Prop := ExitInv s t ∨ Dead Image.code t

/-- One iteration: element `k`'s product added in, then the loop head or the epilogue. -/
theorem body (hMul : MulSpec) {s : MachineState} (hpre : DotPre s)
    (hlen : s.getReg .x12 = s.getReg .x14) (t : MachineState) (hinv : ∃ k, LoopInv s t k) :
    (∃ u, Reaches Image.code t u ∧ Done s u) ∨
      (∃ u, Reaches Image.code t u ∧ (∃ k, LoopInv s u k) ∧ measure u < measure t) := by
  obtain ⟨k, ht⟩ := hinv
  have hsp := sp_bounds hpre
  have hk := ht.lt
  have hret := ValidMemRange.bounds hpre.ret (by decide)
  have hright : ValidMemRange (s.getReg .x13) (3 * (s.getReg .x12).toNat) := hlen ▸ hpre.right
  have hL := ValidMemRange.bounds hpre.left (by simp only [len] at hk; omega)
  have hR := ValidMemRange.bounds hright (by simp only [len] at hk; omega)
  have hLs := hpre.leftStack
  have hRs := hpre.rightStack
  have hLr := hpre.retLeft
  have hRr := hpre.retRight
  have hrs := hpre.retStack
  rw [← hlen] at hRs hRr
  obtain ⟨pL, hpL⟩ : ∃ p, p = s.getReg .x11 + BitVec.ofNat 64 (24 * k) := ⟨_, rfl⟩
  obtain ⟨pR, hpR⟩ : ∃ p, p = s.getReg .x13 + BitVec.ofNat 64 (24 * k) := ⟨_, rfl⟩
  have hx18 : t.getReg .x18 = pL := by rw [ht.x18, hpL]
  have hx9 : t.getReg .x9 = pR := by rw [ht.x9, hpR]
  -- the call
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007f98_spec ht.pc trivial
  have k₁ := b80007f98_keeps h₁
  have hu2 : u.getReg .x2 = s.getReg .x2 - 96 := (k₁ .x2 (by decide)).trans ht.sp
  have hu10 := b80007f98_x10 h₁
  have hu11 := b80007f98_x11 h₁
  have hu12 := b80007f98_x12 h₁
  rv_eval [ht.sp, hx9, hx18] at hu10 hu11 hu12
  have hum := b80007f98_mem_same h₁
  have hmem (p : Word) (hp₁ : Apart p 24 (s.getReg .x10) 24)
      (hp₂ : Apart p 24 (stackLo s dotStack) dotStack) (hw : p.toNat + 24 ≤ 2 ^ 64) :
      eAt u p = eAt s p := by
    unfold eAt
    rw [hum, hum, hum, ht.mem p (by addr_omega [hp₁, hw]) (by addr_omega [hp₂, hw]),
      ht.mem (p + 8) (by addr_omega [hp₁, hw]) (by addr_omega [hp₂, hw]),
      ht.mem (p + 16) (by addr_omega [hp₁, hw]) (by addr_omega [hp₂, hw])]
  have eL := hmem pL (by addr_omega [hpL, hk, hL, hLr]) (by addr_omega [hpL, hk, hL, hLs, hsp])
    (by addr_omega [hpL, hk, hL])
  have eR := hmem pR (by addr_omega [hpR, hk, hR, hRr]) (by addr_omega [hpR, hk, hR, hRs, hsp])
    (by addr_omega [hpR, hk, hR])
  have hpre' : MulPre u := {
    out := by rw [hu10]; valid_sub hpre.stack.valid [hsp]
    lhs := by rw [hu11]; valid_sub hpre.left [hpL, hk, hL]
    rhs := by rw [hu12]; valid_sub hright [hpR, hk, hR]
    stack := ⟨by valid_sub hpre.stack.valid [hsp, hu2], by addr_omega [hsp, hu2]⟩
    outLhs := by rw [hu10, hu11]; addr_omega [hsp, hpL, hk, hL, hLs]
    outRhs := by rw [hu10, hu12]; addr_omega [hsp, hpR, hk, hR, hRs]
    outStack := by addr_omega [hsp, hu10, hu2]
    lhsStack := by rw [hu11]; addr_omega [hsp, hu2, hpL, hk, hL, hLs]
    rhsStack := by rw [hu12]; addr_omega [hsp, hu2, hpR, hk, hR, hRs]
    rodata := hpre.rodata.frame_two (fun a h₁ h₂ ↦ (hum a).trans (ht.mem a h₁ h₂))
      hpre.retRodata hpre.stackRodata
    stackRodata := by addr_omega [hsp, hu2, hpre.stackRodata] }
  obtain ⟨v, hr₂, ⟨hvpc, hpres, hpost⟩ | hdead⟩ :=
    hMul.call hr₁ (b80007f98_pc h₁) hpre'
  swap
  · exact Or.inl ⟨v, hr₂, Or.inr hdead⟩
  have hv2 : v.getReg .x2 = s.getReg .x2 - 96 := (hpres.reg .x2).trans hu2
  have hprod := hpost.value
  rw [hu10, hu11, hu12, eL, eR] at hprod
  -- back from `mul`: add the product, advance
  obtain ⟨w, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80007fac_spec
    (by rw [hvpc, returnAddress_eq, b80007f98_x1 h₁]; decide +kernel) (by
      rv_eval [hv2]
      and_intros <;> valid_access hpre.stack.valid [hsp])
  have k₃ := b80007fac_keeps h₃
  have w19 := b80007fac_x19 h₃
  have w20 := b80007fac_x20 h₃
  have w21 := b80007fac_x21 h₃
  rv_eval [hv2, hpres.reg .x19, hpres.reg .x20, hpres.reg .x21, k₁ .x19 (by decide),
    k₁ .x20 (by decide), k₁ .x21 (by decide)] at w19 w20 w21
  have hacc : Model.limbs (acc s (k + 1)) = (w.getReg .x19, w.getReg .x21, w.getReg .x20) := by
    rw [acc_succ ht.lt, ← hpL, ← hpR, ← hprod, limbs_add, ht.acc, limbs_eAt, w19, w20, w21]
    rv_eval [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ac_rfl
  have hold (a : Word) (ha₁ : (s.getReg .x2).toNat - 64 ≤ a.toNat)
      (ha₂ : a.toNat < (s.getReg .x2).toNat) : w.getMem a = t.getMem a :=
    (b80007fac_mem_same h₃ a).trans ((hpost.frame a (by addr_omega [ha₁, ha₂, hsp, hu10])
      (by addr_omega [ha₁, ha₂, hsp, hu2])).trans (hum a))
  have hfw : FrameInv s w := {
    sp := (k₃ .x2 (by decide)).trans hv2
    ret := by rw [k₃ .x8 (by decide), hpres.reg .x8, k₁ .x8 (by decide), ht.ret]
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
    mem := fun a h₁ h₂ ↦ (b80007fac_mem_same h₃ a).trans ((hpost.frame a
      (by rw [hu10]; addr_omega [h₂, hsp]) (by addr_omega [h₂, hsp, hu2])).trans
      ((hum a).trans (ht.mem a h₁ h₂))) }
  have hv9 : v.getReg .x9 = pR := by rw [hpres.reg .x9, k₁ .x9 (by decide), hx9]
  have hv18 : v.getReg .x18 = pL := by rw [hpres.reg .x18, k₁ .x18 (by decide), hx18]
  have hv22 : v.getReg .x22 = s.getReg .x13 + BitVec.ofNat 64 (24 * len s) := by
    rw [hpres.reg .x22, k₁ .x22 (by decide), ht.x22]
  by_cases hlast : k + 1 = len s
  · -- the last element: store `c1`, `c2`
    have hw8 : w.getReg .x8 = s.getReg .x10 := hfw.ret
    obtain ⟨x, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80007fd0_spec
      (b80007fac_pc_not_taken h₃ (by rw [hv9, hv22]; addr_omega [hpR, hlast, hR])) (by
        rv_eval [hw8]
        and_intros <;> valid_access hpre.ret [hret])
    have hacc' := hacc
    rw [hlast, acc_len] at hacc'
    have m₁ := b80007fd0_m_x8_8 h₄
    have m₂ := b80007fd0_m_x8_16 h₄
    rw [hw8] at m₁ m₂
    have k₄ := b80007fd0_keeps h₄
    have hfm := b80007fd0_frame h₄ (by rw [hw8]; addr_omega [hret])
    rw [hw8] at hfm
    refine Or.inl ⟨x, hr₂.trans (hr₃.trans hr₄), Or.inl {
      sp := (k₄ .x2 (by decide)).trans hfw.sp
      ret := (k₄ .x8 (by decide)).trans hfw.ret
      kept := fun r hr ↦ (k₄ r (mem_of_kept hr _)).trans (hfw.kept r hr)
      ra := (hfm _ (by addr_omega [hsp, hret, hrs])).trans hfw.ra
      s0 := (hfm _ (by addr_omega [hsp, hret, hrs])).trans hfw.s0
      s1 := (hfm _ (by addr_omega [hsp, hret, hrs])).trans hfw.s1
      s2 := (hfm _ (by addr_omega [hsp, hret, hrs])).trans hfw.s2
      s3 := (hfm _ (by addr_omega [hsp, hret, hrs])).trans hfw.s3
      s4 := (hfm _ (by addr_omega [hsp, hret, hrs])).trans hfw.s4
      s5 := (hfm _ (by addr_omega [hsp, hret, hrs])).trans hfw.s5
      s6 := (hfm _ (by addr_omega [hsp, hret, hrs])).trans hfw.s6
      mem := fun a h₁ h₂ ↦ (hfm a (by addr_omega [h₁, hret])).trans (hfw.mem a h₁ h₂)
      pc := b80007fd0_pc h₄
      c0 := by rw [k₄ .x19 (by decide), hacc']
      c1 := by rw [m₁, hacc']
      c2 := by rw [m₂, hacc'] }⟩
  · have hk1 : k + 1 < len s := by omega
    refine Or.inr ⟨w, hr₂.trans hr₃, ⟨k + 1, {
      toFrameInv := hfw
      acc := hacc
      lt := hk1
      pc := b80007fac_pc_taken h₃ (by rw [hv9, hv22]; addr_omega [hpR, hk1, hR])
      x9 := by rw [b80007fac_x9 h₃, hv9]; addr_omega [hpR, hk1, hR]
      x18 := by rw [b80007fac_x18 h₃, hv18]; addr_omega [hpL, hk1, hL]
      x22 := (k₃ .x22 (by decide)).trans hv22 }⟩, ?_⟩
    simp only [measure]
    rw [b80007fac_x9 h₃, k₃ .x22 (by decide), hv9, hv22, ht.x22, hx9]
    addr_omega [hpR, hk1, hR]

/-! ## The epilogue -/

theorem exit {s t : MachineState} (hpre : DotPre s) (ht : ExitInv s t) :
    ∃ u, Reaches Image.code t u ∧ u.pc = returnAddress s ∧ Preserves s u ∧
      eAt u (s.getReg .x10) = Model.dotRust (left s) (right s) ∧ Frame s u := by
  have hsp := sp_bounds hpre
  have hret := ValidMemRange.bounds hpre.ret (by decide)
  have hrs := hpre.retStack
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b80007fe0_spec ht.pc (by
    rv_eval [ht.sp, ht.ret]
    and_intros <;> first
      | addr_omega [hsp, hret, hrs]
      | valid_access hpre.stack.valid [hsp]
      | valid_access hpre.ret [hret])
  have k := b80007fe0_keeps h
  have pc := b80007fe0_pc h
  have x2 := b80007fe0_x2 h
  have x8 := b80007fe0_x8 h
  have x9 := b80007fe0_x9 h
  have x18 := b80007fe0_x18 h
  have x19 := b80007fe0_x19 h
  have x20 := b80007fe0_x20 h
  have x21 := b80007fe0_x21 h
  have x22 := b80007fe0_x22 h
  have m₀ := b80007fe0_m_x8_0 h
  have hm := b80007fe0_frame h (by rw [ht.ret]; addr_omega [hret])
  rv_eval [ht.sp, ht.ret, ht.ra, ht.s0, ht.s1, ht.s2, ht.s3, ht.s4, ht.s5, ht.s6]
    at pc x2 x8 x9 x18 x19 x20 x21 x22 m₀ hm
  refine ⟨u, hr, pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 x19 fun r hr ↦ ?_, ?_,
    fun a h₁ h₂ ↦ (hm a (by addr_omega [h₁, hret])).trans (ht.mem a h₁ h₂)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact x20
    · exact x21
    · exact x22
    all_goals exact (k _ (by decide)).trans (ht.kept _ (by decide))
  · apply eAt_eq_of_limbs
    rw [m₀, ht.c0, hm (s.getReg .x10 + 8) (by addr_omega [hret]),
      hm (s.getReg .x10 + 16) (by addr_omega [hret]), ht.c1, ht.c2]

/-! ## `dot` -/

/-- **`dot` meets its contract**, given `mul`'s. -/
theorem dot_spec (hMul : MulSpec) : DotSpec := by
  intro s hpc hpre
  by_cases hlen : s.getReg .x12 = s.getReg .x14
  · obtain ⟨t, hst, ht⟩ := setup hpc hpre hlen
    obtain ⟨u, hsu, hu⟩ : ∃ u, Reaches Image.code s u ∧ Done s u := by
      rcases ht with ht | ht
      · exact ⟨t, hst, Or.inl ht⟩
      · obtain ⟨u, htu, hu⟩ := Reaches.loop (fun t ↦ ∃ k, LoopInv s t k) measure (Done s)
          (body hMul hpre hlen) t ht
        exact ⟨u, hst.trans htu, hu⟩
    rcases hu with hu | hdead
    · obtain ⟨v, huv, hvpc, hpres, hval, hframe⟩ := exit hpre hu
      exact ⟨v, hsu.trans huv, Or.inl ⟨hvpc, hpres, hlen, hval, hframe⟩⟩
    · exact ⟨u, hsu, Or.inr hdead⟩
  · obtain ⟨t, hst, hdead⟩ := mismatch hpc hlen
    exact ⟨t, hst, Or.inr hdead⟩

end Rv64Verifier.Proofs.Multilinear.Dot
