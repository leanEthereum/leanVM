import Rv64Verifier.Proofs.Contracts
import Rv64Verifier.Blocks.F62
import Statement.LeanVmVerifier

/-!
# `verifier::multilinear::eq_eval`

```rust
pub fn eq_eval(left: &[E], right: &[E]) -> E {
    assert_eq!(left.len(), right.len());
    let mut result = ONE;
    for (&x, &y) in left.iter().zip(right) {
        result *= ONE + x + y;
    }
    result
}
```

compiled at `0x8000da88` (`Blocks/F62.lean`, whose comments summarize each block): `a0` is where
the result goes, `a1`/`a2` and `a3`/`a4` the slices. `0x8000da88` traps (`0x8000db74`, `unimp`)
if the lengths differ; `0x8000da8c` makes a 112-byte frame and sets `result` (at `sp - 112`, `sp`
the entry's) to one; `0x8000dabc` sets `s1`, `s2` to the third limbs of `right` and `left` and
`s3` to `s1`'s end; the loop body (`0x8000dad4`) writes `ONE + x + y` at `sp - 88` and calls
`<E as Mul>::mul` into `sp - 64`; `0x8000db1c` copies the product to `result` and advances;
`0x8000db40` copies `result` out and returns.

The proof: `mismatch` or `setup`; the loop by `Reaches.loop` with `LoopInv` (`body`); `exit` from
`FrameInv` with every element folded in. Every block fact comes from a generated lemma
(`b<pc>_x<n>`, `b<pc>_m_..`, `b<pc>_keeps`, `b<pc>_frame`, `b<pc>_pc..`), put in terms of the
entry state by `rv_eval [invariant] at`; every address fact is `addr_omega`'s.
-/

namespace Rv64Verifier.Proofs.EqEval
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Contracts
  Rv64Verifier.Blocks.F62
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The 112-byte frame and `mul`'s stack below it. -/
@[rv_addr] def stackSize : Nat := 112 + mulStack

/-- `left.len()`. -/
@[rv_addr] def len (s : MachineState) : Nat := (s.getReg .x12).toNat

def left (s : MachineState) : List E := eListAt s (s.getReg .x11) (len s)
def right (s : MachineState) : List E := eListAt s (s.getReg .x13) (len s)

/-- `a0` is a valid `E` for the result, `a1`/`a2` and `a3`/`a4` valid slices, the stack below
`sp` valid, all three apart from the stack. -/
structure Pre (s : MachineState) : Prop where
  ret : ValidMemRange (s.getReg .x10) 3
  left : ValidMemRange (s.getReg .x11) (3 * (s.getReg .x12).toNat)
  right : ValidMemRange (s.getReg .x13) (3 * (s.getReg .x14).toNat)
  stack : StackOk s stackSize
  retStack : Apart (s.getReg .x10) 24 (stackLo s stackSize) stackSize
  leftStack : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (stackLo s stackSize) stackSize
  rightStack : Apart (s.getReg .x13) (24 * (s.getReg .x14).toNat) (stackLo s stackSize) stackSize

/-- The lengths agree, the result is `eqEval` of the slices, and memory changes only in the
result and the stack. -/
structure Post (s t : MachineState) : Prop where
  len : s.getReg .x12 = s.getReg .x14
  value : eAt t (s.getReg .x10) = eqEval (left s) (right s)
  frame : ∀ a, ¬ Within a (s.getReg .x10) 24 → ¬ Within a (stackLo s stackSize) stackSize →
    t.getMem a = s.getMem a

/-! ## The invariants -/

/-- `result` after `k` elements. -/
def acc (s : MachineState) (k : Nat) : E :=
  (List.zipWith (fun x z ↦ 1 + x + z) ((left s).take k) ((right s).take k)).foldl (· * ·) 1

/-- The callee-saved registers the function never touches. -/
def kept : List Reg := [.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

theorem mem_of_kept {r : Reg} (h : r ∈ kept) (l : List Reg)
    (hl : ∀ r ∈ kept, r ∈ l := by decide) : r ∈ l :=
  hl r h

/-- From after `result = ONE` to the epilogue, `k` elements folded in. Addresses are the entry's
`sp` minus a constant. -/
structure FrameInv (s t : MachineState) (k : Nat) : Prop where
  sp : t.getReg .x2 = s.getReg .x2 - 112
  ret : t.getReg .x8 = s.getReg .x10
  kept : ∀ r ∈ kept, t.getReg r = s.getReg r
  ra : t.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : t.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : t.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : t.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : t.getMem (s.getReg .x2 - 40) = s.getReg .x19
  acc : eAt t (s.getReg .x2 - 112) = acc s k
  mem : MemFrame s t (stackLo s stackSize) stackSize

/-- At the loop head, before element `k`: `s1` walks `right`, `s2` walks `left`. -/
structure LoopInv (s t : MachineState) (k : Nat) : Prop extends FrameInv s t k where
  lt : k < len s
  pc : t.pc = 0x8000dad4
  x9 : t.getReg .x9 = s.getReg .x13 + BitVec.ofNat 64 (24 * k) + 16
  x18 : t.getReg .x18 = s.getReg .x11 + BitVec.ofNat 64 (24 * k) + 16
  x19 : t.getReg .x19 = s.getReg .x13 + BitVec.ofNat 64 (24 * len s) + 16

/-- A frame invariant carries over a step that changes no memory and none of its registers. -/
theorem FrameInv.of_same {s t u : MachineState} {k : Nat} (h : FrameInv s t k)
    (hm : ∀ a, u.getMem a = t.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
      u.getReg r = t.getReg r) : FrameInv s u k where
  sp := (hr _ (by decide)).trans h.sp
  ret := (hr _ (by decide)).trans h.ret
  kept r hr' := (hr r (mem_of_kept hr' _)).trans (h.kept r hr')
  ra := (hm _).trans h.ra
  s0 := (hm _).trans h.s0
  s1 := (hm _).trans h.s1
  s2 := (hm _).trans h.s2
  s3 := (hm _).trans h.s3
  acc := by rw [← h.acc]; simp only [eAt, hm]
  mem a ha := (hm a).trans (h.mem a ha)

/-- `sp` as a number. -/
theorem Pre.sp {s : MachineState} (h : Pre s) :
    1168 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 := by
  have := h.stack.bounds (by decide) (by decide)
  simp only [stackSize, mulStack] at this
  omega

theorem acc_zero (s : MachineState) : acc s 0 = 1 := by simp [acc]

theorem acc_succ {s : MachineState} {k : Nat} (hk : k < len s) :
    acc s (k + 1) = acc s k * (1 + eAt s (s.getReg .x11 + BitVec.ofNat 64 (24 * k)) +
      eAt s (s.getReg .x13 + BitVec.ofNat 64 (24 * k))) := by
  unfold acc
  rw [foldl_zipWith_take_succ _ _ _ _ _ _ (by rw [left, eListAt_length]; exact hk)
    (by rw [right, eListAt_length]; exact hk)]
  simp only [left, right, eListAt_getElem]

theorem acc_len (s : MachineState) : acc s (len s) = eqEval (left s) (right s) := by
  rw [acc, List.take_of_length_le (by simp [left, eListAt_length]),
    List.take_of_length_le (by simp [right, eListAt_length])]
  rfl

/-! ## Entry -/

theorem trap : Image.code.fetch 0x8000db74 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

/-- Lengths differ: the trap. -/
theorem mismatch {s : MachineState} (hpc : s.pc = 0x8000da88)
    (hne : s.getReg .x12 ≠ s.getReg .x14) :
    ∃ t, Reaches Image.code s t ∧ Dead Image.code t := by
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b8000da88_spec hpc trivial
  exact ⟨t, hr, dead_of_fetch (by rw [b8000da88_pc_taken h hne]; exact trap)⟩

/-- Lengths agree: `result = ONE`, then the loop head, or the epilogue for empty slices. -/
theorem setup {s : MachineState} (hpc : s.pc = 0x8000da88) (hpre : Pre s)
    (hlen : s.getReg .x12 = s.getReg .x14) :
    ∃ t, Reaches Image.code s t ∧
      ((t.pc = 0x8000db40 ∧ FrameInv s t (len s)) ∨ ∃ k, LoopInv s t k) := by
  have hsp := hpre.sp
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000da88_spec hpc trivial
  have k₀ := b8000da88_keeps h₀
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000da8c_spec
    (b8000da88_pc_not_taken h₀ hlen) (by
      rv_eval [k₀ .x2 (by decide)]
      and_intros <;> valid_access hpre.stack.valid [hsp])
  have k₁ := b8000da8c_keeps h₁
  have m₀ := b8000da8c_m_x2_n112 h₁
  have m₁ := b8000da8c_m_x2_n104 h₁
  have m₂ := b8000da8c_m_x2_n96 h₁
  have ra := b8000da8c_m_x2_n8 h₁
  have s0 := b8000da8c_m_x2_n16 h₁
  have s1 := b8000da8c_m_x2_n24 h₁
  have s2 := b8000da8c_m_x2_n32 h₁
  have s3 := b8000da8c_m_x2_n40 h₁
  have hm₁ := b8000da8c_frame h₁ (by rw [k₀ .x2 (by decide)]; addr_omega [hsp])
  rw [k₀ .x2 (by decide)] at m₀ m₁ m₂ ra s0 s1 s2 s3 hm₁
  rw [k₀ .x1 (by decide)] at ra
  rw [k₀ .x8 (by decide)] at s0
  rw [k₀ .x9 (by decide)] at s1
  rw [k₀ .x18 (by decide)] at s2
  rw [k₀ .x19 (by decide)] at s3
  have hf₁ : FrameInv s t₁ 0 := {
    sp := by rw [b8000da8c_x2 h₁, k₀ .x2 (by decide)]
    ret := by rw [b8000da8c_x8 h₁, k₀ .x10 (by decide)]
    kept := fun r hr ↦ by rw [k₁ r (mem_of_kept hr _), k₀ r (mem_of_kept hr _)]
    ra, s0, s1, s2, s3
    acc := by
      rw [acc_zero]
      apply eAt_eq_of_limbs
      rv_eval [limbs_one, m₀, m₁, m₂]
    mem := (MemFrame.of_same (b8000da88_mem_same h₀) _ _).trans hm₁ fun a ha ↦
      by addr_omega [ha, hsp] }
  by_cases h0 : s.getReg .x12 = 0
  · refine ⟨t₁, hr₀.trans hr₁,
      Or.inl ⟨b8000da8c_pc_taken h₁ (by rw [k₀ .x12 (by decide)]; exact h0), ?_⟩⟩
    rw [show len s = 0 by simp [len, h0]]
    exact hf₁
  · obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000dabc_spec
      (b8000da8c_pc_not_taken h₁ (by rw [k₀ .x12 (by decide)]; exact h0)) trivial
    have hright : ValidMemRange (s.getReg .x13) (3 * (s.getReg .x12).toNat) := hlen ▸ hpre.right
    have hR := ValidMemRange.bounds hright (by bv_omega)
    have hL := ValidMemRange.bounds hpre.left (by bv_omega)
    refine ⟨t₂, hr₀.trans (hr₁.trans hr₂), Or.inr ⟨0, {
      toFrameInv := hf₁.of_same (b8000dabc_mem_same h₂) (h₂.keeps rfl)
      lt := by addr_omega [h0]
      pc := b8000dabc_pc h₂
      x9 := by
        rw [b8000dabc_x9 h₂, k₁ .x13 (by decide), k₀ .x13 (by decide)]; addr_omega [hR]
      x18 := by
        rw [b8000dabc_x18 h₂, k₁ .x11 (by decide), k₀ .x11 (by decide)]; addr_omega [hL]
      x19 := by
        rw [b8000dabc_x19 h₂, k₁ .x13 (by decide), k₀ .x13 (by decide), k₁ .x12 (by decide),
          k₀ .x12 (by decide)]
        addr_omega [hR] }⟩⟩

/-! ## The loop -/

/-- The bytes of `right` still to go. -/
def measure (t : MachineState) : Nat := (t.getReg .x19).toNat - (t.getReg .x9).toNat

/-- The loop is over: at the epilogue with every element folded in, or at a dead end. -/
def Done (s t : MachineState) : Prop :=
  (t.pc = 0x8000db40 ∧ FrameInv s t (len s)) ∨ Dead Image.code t

/-- One iteration: element `k` folded in by `mul`, then the loop head or the epilogue. -/
theorem body (hMul : MulSpec) {s : MachineState} (hpre : Pre s)
    (hlen : s.getReg .x12 = s.getReg .x14) (t : MachineState) (hinv : ∃ k, LoopInv s t k) :
    (∃ u, Reaches Image.code t u ∧ Done s u) ∨
      (∃ u, Reaches Image.code t u ∧ (∃ k, LoopInv s u k) ∧ measure u < measure t) := by
  obtain ⟨k, ht⟩ := hinv
  have hsp := hpre.sp
  have hk := ht.lt
  have hright : ValidMemRange (s.getReg .x13) (3 * (s.getReg .x12).toNat) := hlen ▸ hpre.right
  have hL := ValidMemRange.bounds hpre.left (by simp only [len] at hk; omega)
  have hR := ValidMemRange.bounds hright (by simp only [len] at hk; omega)
  have hLs := hpre.leftStack
  have hRs := hpre.rightStack
  rw [← hlen] at hRs
  obtain ⟨pL, hpL⟩ : ∃ p, p = s.getReg .x11 + BitVec.ofNat 64 (24 * k) := ⟨_, rfl⟩
  obtain ⟨pR, hpR⟩ : ∃ p, p = s.getReg .x13 + BitVec.ofNat 64 (24 * k) := ⟨_, rfl⟩
  have hx18 : t.getReg .x18 = pL + 16 := by rw [ht.x18, hpL]
  have hx9 : t.getReg .x9 = pR + 16 := by rw [ht.x9, hpR]
  -- `ONE + x + y` at `sp - 88`, and the call
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000dad4_spec ht.pc (by
    rv_eval [ht.sp, hx9, hx18]
    and_intros <;> first
      | valid_access hpre.stack.valid [hsp]
      | valid_access hpre.left [hpL, hk, hL]
      | valid_access hright [hpR, hk, hR])
  have k₁ := b8000dad4_keeps h₁
  have hu2 : u.getReg .x2 = s.getReg .x2 - 112 := (k₁ .x2 (by decide)).trans ht.sp
  have hu10 := b8000dad4_x10 h₁
  have hu11 := b8000dad4_x11 h₁
  have hu12 := b8000dad4_x12 h₁
  have m₀ := b8000dad4_m_x2_24 h₁
  have m₁ := b8000dad4_m_x2_32 h₁
  have m₂ := b8000dad4_m_x2_40 h₁
  have hm₁ := b8000dad4_frame h₁ (by rw [ht.sp]; addr_omega [hsp])
  rv_eval [ht.sp, hx9, hx18] at hu10 hu11 hu12 m₀ m₁ m₂ hm₁
  have hmem (p : Word) (hp : Apart p 24 (stackLo s stackSize) stackSize)
      (hw : p.toNat + 24 ≤ 2 ^ 64) : eAt t p = eAt s p := ht.mem.eAt hp hw
  have helem : eAt u (s.getReg .x2 - 88) = 1 + eAt s pL + eAt s pR := by
    apply eAt_eq_of_limbs
    have hl := hmem pL (by addr_omega [hpL, hk, hL, hLs, hsp]) (by addr_omega [hpL, hk, hL])
    have hr := hmem pR (by addr_omega [hpR, hk, hR, hRs, hsp]) (by addr_omega [hpR, hk, hR])
    rw [limbs_add, limbs_add, limbs_one, ← hl, ← hr, limbs_eAt, limbs_eAt]
    rv_eval [m₀, m₁, m₂, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ac_rfl
  have hpre' : MulPre u := {
    out := by rw [hu10]; valid_sub hpre.stack.valid [hsp]
    lhs := by rw [hu11]; valid_sub hpre.stack.valid [hsp]
    rhs := by rw [hu12]; valid_sub hpre.stack.valid [hsp]
    stack := ⟨by valid_sub hpre.stack.valid [hsp, hu2], by addr_omega [hsp, hu2]⟩
    outLhs := by addr_omega [hsp, hu10, hu11]
    outRhs := by addr_omega [hsp, hu10, hu12]
    outStack := by addr_omega [hsp, hu10, hu2]
    lhsStack := by addr_omega [hsp, hu11, hu2]
    rhsStack := by addr_omega [hsp, hu12, hu2] }
  obtain ⟨v, hr₂, ⟨hvpc, hpres, hpost⟩ | hdead⟩ :=
    hMul.call hr₁ (b8000dad4_pc h₁) hpre'
  swap
  · exact Or.inl ⟨v, hr₂, Or.inr hdead⟩
  -- back from `mul`: the product to `result`, and advance
  have hv2 : v.getReg .x2 = s.getReg .x2 - 112 := (hpres.reg .x2).trans hu2
  have hprod := hpost.value
  rw [hu10, hu11, hu12] at hprod
  obtain ⟨w, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000db1c_spec
    (by rw [hvpc, returnAddress_eq, b8000dad4_x1 h₁]; decide +kernel) (by
      rv_eval [hv2]
      and_intros <;> valid_access hpre.stack.valid [hsp])
  have k₃ := b8000db1c_keeps h₃
  have w₀ := b8000db1c_m_x2_0 h₃
  have w₁ := b8000db1c_m_x2_8 h₃
  have w₂ := b8000db1c_m_x2_16 h₃
  have hm₃ := b8000db1c_frame h₃ (by rw [hv2]; addr_omega [hsp])
  rv_eval [hv2] at w₀ w₁ w₂ hm₃
  have hvmem : MemFrame u v (stackLo s stackSize) stackSize :=
    MemFrame.of_two hpost.frame (fun a ha ↦ by addr_omega [ha, hsp, hu10])
      (fun a ha ↦ by addr_omega [ha, hsp, hu2])
  have hold (a : Word) (ha₁ : (s.getReg .x2).toNat - 40 ≤ a.toNat)
      (ha₂ : a.toNat < (s.getReg .x2).toNat) : w.getMem a = t.getMem a :=
    (hm₃ a (by addr_omega [ha₁, ha₂, hsp])).trans
      ((hpost.frame a (by addr_omega [ha₁, ha₂, hsp, hu10])
        (by addr_omega [ha₁, ha₂, hsp, hu2])).trans
        (hm₁ a (by addr_omega [ha₁, ha₂, hsp])))
  have hfw : FrameInv s w (k + 1) := {
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
    acc := by
      have hw : eAt w (s.getReg .x2 - 112) = eAt v (s.getReg .x2 - 64) := by
        unfold eAt; rv_eval [w₀, w₁, w₂]
      rw [hw, hprod, helem, hm₁.eAt (p := s.getReg .x2 - 112) (by addr_omega [hsp])
        (by addr_omega [hsp]), ht.acc, acc_succ ht.lt, ← hpL, ← hpR]
    mem := (((ht.mem.trans hm₁ fun a ha ↦ by addr_omega [ha, hsp]).trans hvmem
      fun _ h ↦ h).trans hm₃ fun a ha ↦ by addr_omega [ha, hsp]) }
  have hv9 : v.getReg .x9 = pR + 16 := by rw [hpres.reg .x9, k₁ .x9 (by decide), hx9]
  have hv18 : v.getReg .x18 = pL + 16 := by rw [hpres.reg .x18, k₁ .x18 (by decide), hx18]
  have hv19 : v.getReg .x19 = s.getReg .x13 + BitVec.ofNat 64 (24 * len s) + 16 := by
    rw [hpres.reg .x19, k₁ .x19 (by decide), ht.x19]
  by_cases hlast : k + 1 = len s
  · exact Or.inl ⟨w, hr₂.trans hr₃, Or.inl ⟨b8000db1c_pc_not_taken h₃
      (by rw [hv9, hv19]; addr_omega [hpR, hlast, hR]), hlast ▸ hfw⟩⟩
  · have hk1 : k + 1 < len s := by omega
    refine Or.inr ⟨w, hr₂.trans hr₃, ⟨k + 1, {
      toFrameInv := hfw
      lt := hk1
      pc := b8000db1c_pc_taken h₃ (by rw [hv9, hv19]; addr_omega [hpR, hk1, hR])
      x9 := by rw [b8000db1c_x9 h₃, hv9]; addr_omega [hpR, hk1, hR]
      x18 := by rw [b8000db1c_x18 h₃, hv18]; addr_omega [hpL, hk1, hL]
      x19 := (k₃ .x19 (by decide)).trans hv19 }⟩, ?_⟩
    simp only [measure]
    rw [b8000db1c_x9 h₃, k₃ .x19 (by decide), hv9, hv19, hx9, ht.x19]
    addr_omega [hpR, hk1, hR]

/-! ## The epilogue -/

/-- `result` copied out, the callee-saved registers restored, return. -/
theorem exit {s t : MachineState} (hpre : Pre s) (hpc : t.pc = 0x8000db40)
    (ht : FrameInv s t (len s)) :
    ∃ u, Reaches Image.code t u ∧ u.pc = returnAddress s ∧ Preserves s u ∧
      eAt u (s.getReg .x10) = eqEval (left s) (right s) ∧ MemFrame t u (s.getReg .x10) 24 := by
  have hsp := hpre.sp
  have hret := ValidMemRange.bounds hpre.ret (by decide)
  have hrs := hpre.retStack
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b8000db40_spec hpc (by
    rv_eval [ht.sp, ht.ret]
    and_intros <;> first
      | addr_omega [hsp, hret, hrs]
      | valid_access hpre.stack.valid [hsp]
      | valid_access hpre.ret [hret])
  have k := b8000db40_keeps h
  have pc := b8000db40_pc h
  have x2 := b8000db40_x2 h
  have x8 := b8000db40_x8 h
  have x9 := b8000db40_x9 h
  have x18 := b8000db40_x18 h
  have x19 := b8000db40_x19 h
  have m₀ := b8000db40_m_x8_0 h
  have m₁ := b8000db40_m_x8_8 h
  have m₂ := b8000db40_m_x8_16 h
  have hm := b8000db40_frame h (by rw [ht.ret]; addr_omega [hret])
  rv_eval [ht.sp, ht.ret, ht.ra, ht.s0, ht.s1, ht.s2, ht.s3]
    at pc x2 x8 x9 x18 x19 m₀ m₁ m₂ hm
  refine ⟨u, hr, pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 x19 fun r hr ↦ (k r (mem_of_kept hr _)).trans (ht.kept r hr),
    ?_, hm⟩
  rw [← acc_len, ← ht.acc]
  unfold eAt
  rv_eval [m₀, m₁, m₂]

/-! ## `eq_eval` -/

/-- **`eq_eval` meets its contract**, given `mul`'s. -/
theorem eq_eval_spec (hMul : MulSpec) : FunSpec Image.code 0x8000da88 Pre Post := by
  intro s hpc hpre
  by_cases hlen : s.getReg .x12 = s.getReg .x14
  · obtain ⟨t, hst, ht⟩ := setup hpc hpre hlen
    obtain ⟨u, hsu, hu⟩ : ∃ u, Reaches Image.code s u ∧ Done s u := by
      rcases ht with ht | ht
      · exact ⟨t, hst, Or.inl ht⟩
      · obtain ⟨u, htu, hu⟩ := Reaches.loop (fun t ↦ ∃ k, LoopInv s t k) measure (Done s)
          (body hMul hpre hlen) t ht
        exact ⟨u, hst.trans htu, hu⟩
    rcases hu with ⟨hpc', hu⟩ | hdead
    · obtain ⟨v, huv, hvpc, hpres, hval, hframe⟩ := exit hpre hpc' hu
      exact ⟨v, hsu.trans huv, Or.inl ⟨hvpc, hpres, hlen, hval,
        fun a h₁ h₂ ↦ (hframe a h₁).trans (hu.mem a h₂)⟩⟩
    · exact ⟨u, hsu, Or.inr hdead⟩
  · obtain ⟨t, hst, hdead⟩ := mismatch hpc hlen
    exact ⟨t, hst, Or.inr hdead⟩

end Rv64Verifier.Proofs.EqEval
