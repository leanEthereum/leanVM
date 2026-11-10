import Rv64Verifier.Proofs.Field.Contracts
import Rv64Verifier.Blocks.F79

/-!
# `E::sum` over a slice

```rust
pub fn sum(values: impl IntoIterator<Item = E>) -> E {
    values.into_iter().fold(ZERO, |acc, value| acc + value)
}
```

compiled at `0x800108b4` for a slice's bounds `a1`..`a2` (`Blocks/F79.lean`): `0x800108b4` zeroes
the three running limbs `a5`, `a4`, `a3` and returns them for an empty slice; `0x800108c4` sets
`a1` to the first element's third limb and `a2` to the end's, dividing the byte length by 24 with
a `mulhu` (`mulhu_div`); the loop body `0x800108f4` adds one element; `0x80010914` writes the
limbs out and returns. The loop is `Reaches.loop` over `LoopInv`.
-/

namespace Rv64Verifier.Proofs.Field.Sum
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.FieldContracts Rv64Verifier.Blocks.F79
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The slice. -/
def elems (s : MachineState) : List E := eListAt s (s.getReg .x11) (sumLen s)

/-- The sum of the first `k` elements. -/
def acc (s : MachineState) (k : Nat) : E := ((elems s).take k).sum

/-- The registers `sum` never writes, `ra` and `a0` among them. -/
def kept : List Reg :=
  [.x1, .x2, .x8, .x9, .x10, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

theorem mem_of_kept {r : Reg} (h : r ∈ kept) (l : List Reg)
    (hl : ∀ r ∈ kept, r ∈ l := by decide) : r ∈ l :=
  hl r h

/-- After `k` elements: the running limbs, the kept registers, the memory untouched. -/
structure AccInv (s t : MachineState) (k : Nat) : Prop where
  c0 : t.getReg .x15 = (Model.limbs (acc s k)).1
  c1 : t.getReg .x14 = (Model.limbs (acc s k)).2.1
  c2 : t.getReg .x13 = (Model.limbs (acc s k)).2.2
  kept : ∀ r ∈ kept, t.getReg r = s.getReg r
  mem : ∀ a, t.getMem a = s.getMem a

/-- At the loop head, before element `k`: `a1` is its third limb, `a2` the end's. -/
structure LoopInv (s t : MachineState) (k : Nat) : Prop extends AccInv s t k where
  lt : k < sumLen s
  pc : t.pc = 0x800108f4
  x11 : t.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 (24 * k) + 16
  x12 : t.getReg .x12 = s.getReg .x11 + BitVec.ofNat 64 (24 * sumLen s) + 16

/-! ## Arithmetic -/

theorem mulhu_nat (m : Nat) (h : 24 * m < 18446744073709551616) :
    24 * m * 12297829382473034411 % 340282366920938463463374607431768211456 /
      18446744073709551616 = 16 * m := by
  rw [show 24 * m * 12297829382473034411 = 18446744073709551616 * (16 * m) + 8 * m by ring,
    Nat.mod_eq_of_lt (by omega), Nat.mul_add_div (by norm_num),
    Nat.div_eq_of_lt (by omega : 8 * m < 18446744073709551616), Nat.add_zero]

/-- `0xaaaaaaaaaaaaaaab` is `(2^65 + 1) / 3`: the high word of `24 m` times it is `16 m`. -/
theorem mulhu_div (m : Nat) (h : 24 * m < 2 ^ 64) :
    rv64_mulhu (BitVec.ofNat 64 (24 * m)) 0xaaaaaaaaaaaaaaab = BitVec.ofNat 64 (16 * m) := by
  have h' : 24 * m < 18446744073709551616 := h
  have hM : (0xaaaaaaaaaaaaaaab : Word).toNat = 12297829382473034411 := rfl
  have p64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  have p128 : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  apply BitVec.eq_of_toNat_eq
  unfold rv64_mulhu
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_mul, BitVec.zeroExtend_eq_setWidth, BitVec.zeroExtend_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hM,
    Nat.shiftRight_eq_div_pow, p64, p128, Nat.mod_eq_of_lt h',
    Nat.mod_eq_of_lt (by omega : 24 * m < 340282366920938463463374607431768211456),
    Nat.mod_eq_of_lt (by norm_num : 12297829382473034411 < 340282366920938463463374607431768211456),
    mulhu_nat m h', Nat.mod_eq_of_lt (by omega : 16 * m < 18446744073709551616)]

theorem and_mask (m : Nat) :
    BitVec.ofNat 64 (16 * m) &&& 0xfffffffffffffff0 = BitVec.ofNat 64 (16 * m) := by
  have hx : BitVec.ofNat 64 (16 * m) = BitVec.ofNat 64 m <<< 4 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  rw [hx]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem acc_zero (s : MachineState) : acc s 0 = 0 := by simp [acc]

theorem acc_succ {s : MachineState} {k : Nat} (hk : k < sumLen s) :
    acc s (k + 1) = acc s k + eAt s (s.getReg .x11 + BitVec.ofNat 64 (24 * k)) := by
  have hl : k < (elems s).length := by rw [elems, eListAt_length]; exact hk
  rw [acc, List.take_succ_eq_append_getElem hl, List.sum_append, List.sum_singleton]
  simp only [elems, eListAt_getElem]
  rfl

theorem acc_len (s : MachineState) : acc s (sumLen s) = (elems s).sum := by
  rw [acc, List.take_of_length_le (by simp [elems, eListAt_length])]

/-- The bounds as numbers. -/
theorem len_eq {s : MachineState} (h : SumPre s) :
    (s.getReg .x12).toNat = (s.getReg .x11).toNat + 24 * sumLen s := by
  have := h.bounds
  have := h.whole
  simp only [sumLen]
  omega

/-! ## The steps -/

/-- The empty slice: zero out. -/
theorem empty {s : MachineState} (hpc : s.pc = 0x800108b4)
    (heq : s.getReg .x11 = s.getReg .x12) :
    ∃ t, Reaches Image.code s t ∧ t.pc = 0x80010914 ∧ AccInv s t (sumLen s) := by
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b800108b4_spec hpc trivial
  have hn : sumLen s = 0 := by simp [sumLen, heq]
  have k := b800108b4_keeps h
  refine ⟨t, hr, b800108b4_pc_taken h heq, ?_⟩
  rw [hn]
  exact {
    c0 := by rw [b800108b4_x15 h, acc_zero]; rfl
    c1 := by rw [b800108b4_x14 h, acc_zero]; rfl
    c2 := by rw [b800108b4_x13 h, acc_zero]; rfl
    kept := fun r hr ↦ k r (mem_of_kept hr _)
    mem := b800108b4_mem_same h }

/-- A nonempty slice: the loop head before element 0. -/
theorem setup {s : MachineState} (hpc : s.pc = 0x800108b4) (hpre : SumPre s)
    (hne : s.getReg .x11 ≠ s.getReg .x12) :
    ∃ t, Reaches Image.code s t ∧ LoopInv s t 0 := by
  have hlen := len_eq hpre
  have hn : 0 < sumLen s := by
    rcases Nat.eq_zero_or_pos (sumLen s) with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq (by omega)) hne
    · exact h0
  have hS := ValidMemRange.bounds hpre.slice (by omega)
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b800108b4_spec hpc trivial
  have k₀ := b800108b4_keeps h₀
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800108c4_spec (b800108b4_pc_not_taken h₀ hne)
    trivial
  have k₁ := b800108c4_keeps h₁
  have h12 := h₁.reg .x12 rfl
  rv_eval [k₀ .x11 (by decide), k₀ .x12 (by decide)] at h12
  have hd : s.getReg .x12 - s.getReg .x11 = BitVec.ofNat 64 (24 * sumLen s) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsh : BitVec.ofNat 64 (16 * sumLen s) >>> 4 = BitVec.ofNat 64 (sumLen s) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  rw [hd, mulhu_div _ (by omega), and_mask, hsh] at h12
  refine ⟨t₁, hr₀.trans hr₁, {
    c0 := by rw [k₁ .x15 (by decide), b800108b4_x15 h₀, acc_zero]; rfl
    c1 := by rw [k₁ .x14 (by decide), b800108b4_x14 h₀, acc_zero]; rfl
    c2 := by rw [k₁ .x13 (by decide), b800108b4_x13 h₀, acc_zero]; rfl
    kept := fun r hr ↦ by rw [k₁ r (mem_of_kept hr _), k₀ r (mem_of_kept hr _)]
    mem := fun a ↦ by rw [b800108c4_mem_same h₁, b800108b4_mem_same h₀]
    lt := hn
    pc := b800108c4_pc h₁
    x11 := by rw [b800108c4_x11 h₁, k₀ .x11 (by decide)]; simp
    x12 := by rw [h12]; addr_omega [hS] }⟩

/-- The bytes still to go. -/
def measure (t : MachineState) : Nat := (t.getReg .x12).toNat - (t.getReg .x11).toNat

/-- One element added: the loop head again, or the epilogue with all added. -/
theorem body {s : MachineState} (hpre : SumPre s) (t : MachineState) (hinv : ∃ k, LoopInv s t k) :
    (∃ u, Reaches Image.code t u ∧ u.pc = 0x80010914 ∧ AccInv s u (sumLen s)) ∨
      (∃ u, Reaches Image.code t u ∧ (∃ k, LoopInv s u k) ∧ measure u < measure t) := by
  obtain ⟨k, ht⟩ := hinv
  have hk := ht.lt
  have hlen := len_eq hpre
  have hS := ValidMemRange.bounds hpre.slice (by omega)
  obtain ⟨p, hp⟩ : ∃ p, p = s.getReg .x11 + BitVec.ofNat 64 (24 * k) := ⟨_, rfl⟩
  have hx11 : t.getReg .x11 = p + 16 := by rw [ht.x11, hp]
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b800108f4_spec ht.pc (by
    rv_eval [hx11]
    and_intros <;> valid_access hpre.slice [hp, hk, hS])
  have k₁ := b800108f4_keeps h
  have hp8 : p + 16 - 8 = p + 8 := by bv_omega
  have hp16 : p + 16 - 16 = p := by bv_omega
  have he : Model.limbs (eAt s p) = (t.getMem p, t.getMem (p + 8), t.getMem (p + 16)) := by
    rw [limbs_eAt, ht.mem, ht.mem, ht.mem]
  have hacc : AccInv s u (k + 1) := {
    c0 := by
      rw [b800108f4_x15 h, hx11, hp16, ht.c0, acc_succ hk, ← hp, limbs_add, he]
      exact BitVec.xor_comm _ _
    c1 := by
      rw [b800108f4_x14 h, hx11, hp8, ht.c1, acc_succ hk, ← hp, limbs_add, he]
      exact BitVec.xor_comm _ _
    c2 := by
      rw [b800108f4_x13 h, hx11, ht.c2, acc_succ hk, ← hp, limbs_add, he]
      exact BitVec.xor_comm _ _
    kept := fun r hr ↦ by rw [k₁ r (mem_of_kept hr _), ht.kept r hr]
    mem := fun a ↦ by rw [b800108f4_mem_same h, ht.mem] }
  by_cases hlast : k + 1 = sumLen s
  · refine Or.inl ⟨u, hr, b800108f4_pc_not_taken h ?_, hlast ▸ hacc⟩
    rw [hx11, ht.x12, hp]
    addr_omega [hlast, hS]
  · have hk1 : k + 1 < sumLen s := by omega
    have hpc' : u.pc = 0x800108f4 := by
      apply b800108f4_pc_taken h
      rw [hx11, ht.x12, hp]
      addr_omega [hk1, hS]
    have hu11 : u.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 (24 * (k + 1)) + 16 := by
      rw [b800108f4_x11 h, hx11, hp]; addr_omega [hk1, hS]
    have hu12 : u.getReg .x12 = s.getReg .x11 + BitVec.ofNat 64 (24 * sumLen s) + 16 := by
      rw [k₁ .x12 (by decide), ht.x12]
    refine Or.inr ⟨u, hr, ⟨k + 1, ⟨hacc, hk1, hpc', hu11, hu12⟩⟩, ?_⟩
    · simp only [measure]
      rw [b800108f4_x11 h, k₁ .x12 (by decide), hx11, ht.x12, hp]
      addr_omega [hk1, hS]

/-- The limbs written out, return. -/
theorem exit {s t : MachineState} (hpre : SumPre s) (hpc : t.pc = 0x80010914)
    (ht : AccInv s t (sumLen s)) :
    ∃ u, Reaches Image.code t u ∧ u.pc = returnAddress s ∧ Preserves s u ∧ SumPost s u := by
  have hO := ValidMemRange.bounds hpre.out (by decide)
  have h10 := ht.kept .x10 (by decide)
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b80010914_spec hpc (by
    rv_eval [h10]
    and_intros <;> valid_access hpre.out [hO])
  have k := b80010914_keeps h
  have m₀ := b80010914_m_x10_0 h
  have m₁ := b80010914_m_x10_8 h
  have m₂ := b80010914_m_x10_16 h
  have hm := b80010914_frame h (by rw [h10]; addr_omega [hO])
  rw [h10] at m₀ m₁ m₂ hm
  refine ⟨u, hr, ?_, fun r hr ↦ ?_, ?_, fun a ha ↦ ?_⟩
  · rw [b80010914_pc h, ht.kept .x1 (by decide)]; rfl
  · rw [k r (by simp only [Rv64Verifier.calleeSaved, List.mem_cons] at hr ⊢; tauto)]
    exact ht.kept r (by simp only [Rv64Verifier.calleeSaved, kept, List.mem_cons] at hr ⊢; tauto)
  · show eAt u (s.getReg .x10) = (elems s).sum
    rw [← acc_len]
    apply eAt_eq_of_limbs
    rw [m₀, m₁, m₂, ht.c0, ht.c1, ht.c2]
  · rw [hm a ha, ht.mem]

/-- **`E::sum` sums the slice.** -/
theorem sum_spec : SumSpec := by
  intro s hpc hpre
  obtain ⟨t, hst, htpc, ht⟩ : ∃ t, Reaches Image.code s t ∧ t.pc = 0x80010914 ∧
      AccInv s t (sumLen s) := by
    by_cases heq : s.getReg .x11 = s.getReg .x12
    · exact empty hpc heq
    · obtain ⟨t, hst, ht⟩ := setup hpc hpre heq
      obtain ⟨u, htu, hu⟩ := Reaches.loop (fun t ↦ ∃ k, LoopInv s t k) measure
        (fun u ↦ u.pc = 0x80010914 ∧ AccInv s u (sumLen s))
        (fun t h ↦ (body hpre t h).imp (fun ⟨u, hr, hu⟩ ↦ ⟨u, hr, hu⟩) id) t ⟨0, ht⟩
      exact ⟨u, hst.trans htu, hu⟩
  obtain ⟨u, htu, hpc', hpres, hpost⟩ := exit hpre htpc ht
  exact ⟨u, hst.trans htu, Or.inl ⟨hpc', hpres, hpost⟩⟩

end Rv64Verifier.Proofs.Field.Sum
