import Rv64Verifier.Proofs.Bytecode.EvalWords

/-!
# `Bytecode::evaluate`: `monomial_sum`

`0x80011650`..`0x800116d8`, one `bit_sums` entry per iteration: each limb of entry `k`, shifted
left by `k` as a `u128`, XORed into that limb's accumulator (`macc`), whose low and high words
the registers hold (`MInv`). `mbody` is one iteration, `mloop` all 64.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `monomial_sum`'s step `k`. -/
def mstep (S : List E) (c : BitVec 128 × BitVec 128 × BitVec 128) (k : Nat) :
    BitVec 128 × BitVec 128 × BitVec 128 :=
  (c.1 ^^^ (limbs (S.getD k 0)).1.setWidth 128 <<< k,
    c.2.1 ^^^ (limbs (S.getD k 0)).2.1.setWidth 128 <<< k,
    c.2.2 ^^^ (limbs (S.getD k 0)).2.2.setWidth 128 <<< k)

/-- The three accumulators after `k` steps. -/
def macc (S : List E) (k : Nat) : BitVec 128 × BitVec 128 × BitVec 128 :=
  (List.range k).foldl (mstep S) (0#128, 0#128, 0#128)

theorem macc_succ (S : List E) (k : Nat) : macc S (k + 1) = mstep S (macc S k) k := by
  simp only [macc, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem macc_zero (S : List E) : macc S 0 = (0#128, 0#128, 0#128) := rfl

theorem monomialSumRust_macc (S : List E) : monomialSumRust S =
    eOfLimbs (reduce128 (macc S 64).1, reduce128 (macc S 64).2.1, reduce128 (macc S 64).2.2) := by
  simp only [monomialSumRust, macc]
  congr

/-! ## One limb's step, as the code computes it -/

theorem mul_pow_shift (x : Word) {k : Nat} (hk : k < 64) :
    x * BitVec.ofNat 64 (2 ^ ((BitVec.ofNat 64 k).toNat % 64)) = x <<< k := by
  have hk' : (BitVec.ofNat 64 k).toNat % 64 = k := by rw [BitVec.toNat_ofNat]; omega
  rw [hk']
  apply BitVec.eq_of_toNat_eq
  have hp : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt hp]

theorem allOnes_and' (x : Word) : (0xffffffffffffffff : Word) &&& x = x := by
  rw [show (0xffffffffffffffff : Word) = BitVec.allOnes 64 by decide, BitVec.allOnes_and]

theorem step_lo (c : BitVec 128) (x : Word) {k : Nat} (hk : k < 64) :
    (BitVec.ofNat 64 k - 64).sshiftRight 63 &&&
        x * BitVec.ofNat 64 (2 ^ ((BitVec.ofNat 64 k).toNat % 64)) ^^^ c.extractLsb' 0 64 =
      (c ^^^ x.setWidth 128 <<< k).extractLsb' 0 64 := by
  rw [sshift_neg k hk, allOnes_and', mul_pow_shift x hk, extractLsb'_xor128, shl128_lo,
    BitVec.xor_comm]

theorem step_hi (c : BitVec 128) (x : Word) {k : Nat} (hk : k < 64) :
    x >>> 1 >>> ((BitVec.ofNat 64 k ^^^ 0xffffffffffffffff).toNat % 64) ^^^ c.extractLsb' 64 64 =
      (c ^^^ x.setWidth 128 <<< k).extractLsb' 64 64 := by
  rw [notK_mod k hk, extractLsb'_xor128, shl128_hi x hk, BitVec.xor_comm]

/-! ## The loop -/

variable {e : Env}

/-- In `monomial_sum` after `k` entries: memory and the loop's registers as at `t₀`, `a6` the
block's index `ix`, `t0` past entry `k - 1`, `a7 = k`, the accumulators' words. -/
structure MInv (e : Env) (t₀ t : MachineState) (ix : Word) (S : List E) (k : Nat) : Prop where
  le : k ≤ 64
  mem : ∀ a, t.getMem a = t₀.getMem a
  keep : ∀ r ∈ [Reg.x2, .x9, .x18, .x19, .x20, .x21, .x23], t.getReg r = t₀.getReg r
  x16 : t.getReg .x16 = ix
  x5 : t.getReg .x5 = e.s.getReg .x2 - 1672 + BitVec.ofNat 64 (24 * k)
  x17 : t.getReg .x17 = BitVec.ofNat 64 k
  x12 : t.getReg .x12 = (macc S k).1.extractLsb' 0 64
  x15 : t.getReg .x15 = (macc S k).1.extractLsb' 64 64
  x11 : t.getReg .x11 = (macc S k).2.1.extractLsb' 0 64
  x14 : t.getReg .x14 = (macc S k).2.1.extractLsb' 64 64
  x10 : t.getReg .x10 = (macc S k).2.2.extractLsb' 0 64
  x13 : t.getReg .x13 = (macc S k).2.2.extractLsb' 64 64

set_option maxHeartbeats 4000000 in
/-- Entry `k`, then the next or, after the last, the reduction. -/
theorem mbody (he : EnvOk e) {t₀ t : MachineState} {ix : Word} {S : List E} {k : Nat}
    (h23 : t₀.getReg .x23 = e.s.getReg .x2 - 136)
    (hS : eListAt t₀ (e.s.getReg .x2 - 1688) 64 = S)
    (hk : k < 64) (hm : MInv e t₀ t ix S k) (hpc : t.pc = 0x80011684) :
    ∃ u, Reaches Image.code t u ∧ MInv e t₀ u ix S (k + 1) ∧
      ((k + 1 < 64 ∧ u.pc = 0x80011684) ∨ (k + 1 = 64 ∧ u.pc = 0x80010f88)) := by
  have hsp := he.sp
  have hst := he.pre.stack.valid
  have x5 := hm.x5
  have x17 := hm.x17
  have hP0 : e.s.getReg .x2 - 1672 + BitVec.ofNat 64 (24 * k) - 16 =
      e.s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * k) := by addr_omega [hsp, hk]
  have hP1 : e.s.getReg .x2 - 1672 + BitVec.ofNat 64 (24 * k) - 8 =
      e.s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * k) + 8 := by addr_omega [hsp, hk]
  have hP2 : e.s.getReg .x2 - 1672 + BitVec.ofNat 64 (24 * k) =
      e.s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * k) + 16 := by addr_omega [hsp, hk]
  generalize hP : e.s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * k) = P at hP0 hP1 hP2
  have hSk : limbs (S.getD k 0) = (t₀.getMem P, t₀.getMem (P + 8), t₀.getMem (P + 16)) := by
    rw [← hS, List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hk), eListAt_getElem,
      limbs_eAt, hP]
  have hneg : BitVec.slt (BitVec.ofNat 64 k - 64) 0 = true := slt_neg k hk
  -- `t3 = bit_sums[k].0`, its two shifts
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011684_spec hpc (by
    rv_eval [x5]; valid_access hst [hsp, hk])
  have k₁ := b80011684_keeps h₁
  have x7₁ := b80011684_x7 h₁
  have x28₁ := b80011684_x28 h₁
  have x30₁ := b80011684_x30 h₁
  have x6₁ := h₁.reg .x6 rfl
  rv_eval [] at x6₁
  rw [x17] at x7₁ x30₁ x6₁
  rw [x5, hP0, hm.mem] at x28₁ x6₁
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800116a0_spec
    (b80011684_pc_taken h₁ (by rw [x17]; exact hneg)) trivial
  have k₂ := b800116a0_keeps h₂
  have x29₂ := h₂.reg .x29 rfl
  rv_eval [] at x29₂
  rw [x28₁, x30₁] at x29₂
  -- `t6 = bit_sums[k].1`
  have x5₂ : t₂.getReg .x5 = t.getReg .x5 := by rw [k₂ .x5 (by decide), k₁ .x5 (by decide)]
  have x17₂ : t₂.getReg .x17 = t.getReg .x17 := by rw [k₂ .x17 (by decide), k₁ .x17 (by decide)]
  have x7₂ : t₂.getReg .x7 = BitVec.ofNat 64 k - 64 := by rw [k₂ .x7 (by decide), x7₁]
  have hm₂ : ∀ a, t₂.getMem a = t₀.getMem a := fun a ↦ by
    rw [b800116a0_mem_same h₂, b80011684_mem_same h₁, hm.mem]
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800116a8_spec (b800116a0_pc h₂) (by
    rv_eval [x5₂, x5]; valid_access hst [hsp, hk])
  have k₃ := b800116a8_keeps h₃
  have x31₃ := b800116a8_x31 h₃
  have x28₃ := h₃.reg .x28 rfl
  rv_eval [] at x28₃
  rw [x5₂, x5, hP1, hm₂] at x31₃ x28₃
  rw [x17₂, x17] at x28₃
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800116bc_spec
    (b800116a8_pc_taken h₃ (by rw [x7₂]; exact hneg)) trivial
  have k₄ := b800116bc_keeps h₄
  have x1₄ := h₄.reg .x1 rfl
  rv_eval [] at x1₄
  rw [x31₃, k₃ .x30 (by decide), k₂ .x30 (by decide), x30₁] at x1₄
  -- `s6 = bit_sums[k].2`
  have x5₄ : t₄.getReg .x5 = t.getReg .x5 := by rw [k₄ .x5 (by decide), k₃ .x5 (by decide), x5₂]
  have x17₄ : t₄.getReg .x17 = t.getReg .x17 := by
    rw [k₄ .x17 (by decide), k₃ .x17 (by decide), x17₂]
  have x7₄ : t₄.getReg .x7 = BitVec.ofNat 64 k - 64 := by
    rw [k₄ .x7 (by decide), k₃ .x7 (by decide), x7₂]
  have hm₄ : ∀ a, t₄.getMem a = t₀.getMem a := fun a ↦ by
    rw [b800116bc_mem_same h₄, b800116a8_mem_same h₃, hm₂]
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800116c4_spec (b800116bc_pc h₄) (by
    rv_eval [x5₄, x5]; valid_access hst [hsp, hk])
  have k₅ := b800116c4_keeps h₅
  have x22₅ := b800116c4_x22 h₅
  have x31₅ := h₅.reg .x31 rfl
  rv_eval [] at x31₅
  rw [x5₄, x5, hP2, hm₄] at x22₅ x31₅
  rw [x17₄, x17] at x31₅
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800116d0_spec
    (b800116c4_pc_not_taken h₅ (by rw [x7₄]; exact hneg)) trivial
  have k₆ := b800116d0_keeps h₆
  have x30₆ := h₆.reg .x30 rfl
  rv_eval [] at x30₆
  rw [x22₅, k₅ .x30 (by decide), k₄ .x30 (by decide), k₃ .x30 (by decide), k₂ .x30 (by decide),
    x30₁] at x30₆
  -- the accumulators
  have K : ∀ r ∈ [Reg.x2, .x5, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19,
      .x20, .x21, .x23], t₆.getReg r = t.getReg r := fun r hr ↦ by
    rw [k₆ r (mem_of_mem hr _), k₅ r (mem_of_mem hr _), k₄ r (mem_of_mem hr _),
      k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have y7 : t₆.getReg .x7 = BitVec.ofNat 64 k - 64 := by
    rw [k₆ .x7 (by decide), k₅ .x7 (by decide), x7₄]
  have y6 : t₆.getReg .x6 = t₁.getReg .x6 := by
    rw [k₆ .x6 (by decide), k₅ .x6 (by decide), k₄ .x6 (by decide), k₃ .x6 (by decide),
      k₂ .x6 (by decide)]
  have y29 : t₆.getReg .x29 = t₂.getReg .x29 := by
    rw [k₆ .x29 (by decide), k₅ .x29 (by decide), k₄ .x29 (by decide), k₃ .x29 (by decide)]
  have y28 : t₆.getReg .x28 = t₃.getReg .x28 := by
    rw [k₆ .x28 (by decide), k₅ .x28 (by decide), k₄ .x28 (by decide)]
  have y1 : t₆.getReg .x1 = t₄.getReg .x1 := by rw [k₆ .x1 (by decide), k₅ .x1 (by decide)]
  have y31 : t₆.getReg .x31 = t₅.getReg .x31 := k₆ .x31 (by decide)
  obtain ⟨u, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80011650_spec (b800116d0_pc h₆) trivial
  have k₇ := b80011650_keeps h₇
  have r12 := h₇.reg .x12 rfl
  have r11 := h₇.reg .x11 rfl
  have r10 := h₇.reg .x10 rfl
  rv_eval [] at r12 r11 r10
  have hr := hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans hr₇)))))
  have hinv : MInv e t₀ u ix S (k + 1) := {
    le := hk
    mem := fun a ↦ by
      rw [b80011650_mem_same h₇, b800116d0_mem_same h₆, b800116c4_mem_same h₅, hm₄]
    keep := fun r hr ↦ by
      rw [k₇ r (mem_of_mem hr _), K r (mem_of_mem hr _), hm.keep r hr]
    x16 := by rw [k₇ .x16 (by decide), K .x16 (by decide), hm.x16]
    x5 := by
      rw [b80011650_x5 h₇, K .x5 (by decide), x5]
      addr_omega [hsp, hk]
    x17 := by
      rw [b80011650_x17 h₇, K .x17 (by decide), x17]
      addr_omega [hk]
    x12 := by
      rw [r12, y7, y6, x6₁, K .x12 (by decide), hm.x12, step_lo _ _ hk, macc_succ, mstep, hSk]
    x15 := by
      rw [b80011650_x15 h₇, y29, x29₂, K .x15 (by decide), hm.x15, step_hi _ _ hk, macc_succ,
        mstep, hSk]
    x11 := by
      rw [r11, y7, y28, x28₃, K .x11 (by decide), hm.x11, step_lo _ _ hk, macc_succ, mstep, hSk]
    x14 := by
      rw [b80011650_x14 h₇, y1, x1₄, K .x14 (by decide), hm.x14, step_hi _ _ hk, macc_succ,
        mstep, hSk]
    x10 := by
      rw [r10, y7, y31, x31₅, K .x10 (by decide), hm.x10, step_lo _ _ hk, macc_succ, mstep, hSk]
    x13 := by
      rw [b80011650_x13 h₇, x30₆, K .x13 (by decide), hm.x13, step_hi _ _ hk, macc_succ,
        mstep, hSk] }
  have x5₆ : t₆.getReg .x5 = e.s.getReg .x2 - 1672 + BitVec.ofNat 64 (24 * k) :=
    (K .x5 (by decide)).trans x5
  have x23₆ : t₆.getReg .x23 = e.s.getReg .x2 - 136 := by
    rw [K .x23 (by decide), hm.keep .x23 (by decide), h23]
  refine ⟨u, hr, hinv, ?_⟩
  by_cases hend : k + 1 = 64
  · refine Or.inr ⟨hend, b80011650_pc_taken h₇ ?_⟩
    rw [x5₆, x23₆]
    addr_omega [hsp, hend]
  · refine Or.inl ⟨by omega, b80011650_pc_not_taken h₇ ?_⟩
    rw [x5₆, x23₆]
    addr_omega [hsp, hend, hk]

/-- All 64 entries, from entry `k` on. -/
theorem mloop (he : EnvOk e) {t₀ t : MachineState} {ix : Word} {S : List E} {k : Nat}
    (h23 : t₀.getReg .x23 = e.s.getReg .x2 - 136)
    (hS : eListAt t₀ (e.s.getReg .x2 - 1688) 64 = S)
    (hk : k < 64) (hm : MInv e t₀ t ix S k) (hpc : t.pc = 0x80011684) :
    ∃ u, Reaches Image.code t u ∧ u.pc = 0x80010f88 ∧ MInv e t₀ u ix S 64 := by
  refine Reaches.loop (fun t ↦ ∃ k, k < 64 ∧ t.pc = 0x80011684 ∧ MInv e t₀ t ix S k)
    (fun t ↦ 64 - (t.getReg .x17).toNat) _ (fun t ⟨k, hk, hpc, hm⟩ ↦ ?_) t ⟨k, hk, hpc, hm⟩
  obtain ⟨u, hr, hu, hl | hl⟩ := mbody he h23 hS hk hm hpc
  · refine Or.inr ⟨u, hr, ⟨k + 1, hl.1, hl.2, hu⟩, ?_⟩
    rw [hu.x17, hm.x17, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · exact Or.inl ⟨u, hr, hl.2, hl.1 ▸ hu⟩

end Rv64Verifier.Proofs.Bytecode.Eval
