import Rv64Verifier.Proofs.Bytecode.EvalWords

/-!
# `Bytecode::evaluate`: one bucket credited to the bit sums

`0x80011408` adds the taken bucket's sum `s` (in `a3`, `a4`, `a5`), masked by bit `b` of the
bucket's byte value, to `bit_sums[8 * byte + b]` for each `b < 8`, reading all 24 doublewords
before writing them: `creditBits` (`credit`). The masks are `bitMask_eq`'s.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The mask of bit `b` of a bucket's value. -/
def bmask (c : BitVec 16) (b : Nat) : Word := 0#64 - ((c.setWidth 64 % 256#64) >>> b &&& 1#64)

theorem limbs_emasked (x : E) (m : Word) :
    limbs (emasked x m) = ((limbs x).1 &&& m, (limbs x).2.1 &&& m, (limbs x).2.2 &&& m) := by
  rw [emasked, limbs_eOfLimbs]

theorem mask0 (c : BitVec 16) :
    (c.setWidth 64 * 9223372036854775808).sshiftRight 63 = bmask c 0 := by
  rw [bmask, ← bitMask_eq c (by decide : 0 < 8), Sym.shiftLeft_eq_mul]
  rfl

theorem mask1 (c : BitVec 16) :
    (c.setWidth 64 * 4611686018427387904).sshiftRight 63 = bmask c 1 := by
  rw [bmask, ← bitMask_eq c (by decide : 1 < 8), Sym.shiftLeft_eq_mul]
  rfl

theorem mask2 (c : BitVec 16) :
    (c.setWidth 64 * 2305843009213693952).sshiftRight 63 = bmask c 2 := by
  rw [bmask, ← bitMask_eq c (by decide : 2 < 8), Sym.shiftLeft_eq_mul]
  rfl

theorem mask3 (c : BitVec 16) :
    (c.setWidth 64 * 1152921504606846976).sshiftRight 63 = bmask c 3 := by
  rw [bmask, ← bitMask_eq c (by decide : 3 < 8), Sym.shiftLeft_eq_mul]
  rfl

theorem mask4 (c : BitVec 16) :
    (c.setWidth 64 * 576460752303423488).sshiftRight 63 = bmask c 4 := by
  rw [bmask, ← bitMask_eq c (by decide : 4 < 8), Sym.shiftLeft_eq_mul]
  rfl

theorem mask5 (c : BitVec 16) :
    (c.setWidth 64 * 288230376151711744).sshiftRight 63 = bmask c 5 := by
  rw [bmask, ← bitMask_eq c (by decide : 5 < 8), Sym.shiftLeft_eq_mul]
  rfl

theorem mask6 (c : BitVec 16) :
    (c.setWidth 64 * 144115188075855872).sshiftRight 63 = bmask c 6 := by
  rw [bmask, ← bitMask_eq c (by decide : 6 < 8), Sym.shiftLeft_eq_mul]
  rfl

theorem mask7 (c : BitVec 16) :
    (c.setWidth 64 * 72057594037927936).sshiftRight 63 = bmask c 7 := by
  rw [bmask, ← bitMask_eq c (by decide : 7 < 8), Sym.shiftLeft_eq_mul]
  rfl

/-- The doubleword frame of a bucket's credit: the 24 bit sums it updates, one spill slot. -/
theorem credit_entries {u u' : MachineState} (h : b80011408.Holds u u') {c : BitVec 16}
    (h16 : u.getReg .x16 = c.setWidth 64) {sum : E}
    (hsum : (u.getReg .x13, u.getReg .x14, u.getReg .x15) = limbs sum) :
    eAt u' ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 0)) =
      eAt u ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 0)) + emasked sum (bmask c 0) ∧
    eAt u' ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 1)) =
      eAt u ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 1)) + emasked sum (bmask c 1) ∧
    eAt u' ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 2)) =
      eAt u ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 2)) + emasked sum (bmask c 2) ∧
    eAt u' ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 3)) =
      eAt u ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 3)) + emasked sum (bmask c 3) ∧
    eAt u' ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 4)) =
      eAt u ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 4)) + emasked sum (bmask c 4) ∧
    eAt u' ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 5)) =
      eAt u ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 5)) + emasked sum (bmask c 5) ∧
    eAt u' ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 6)) =
      eAt u ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 6)) + emasked sum (bmask c 6) ∧
    eAt u' ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 7)) =
      eAt u ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * 7)) + emasked sum (bmask c 7) := by
  have l0 : u.getReg .x13 = (limbs sum).1 := by rw [← hsum]
  have l1 : u.getReg .x14 = (limbs sum).2.1 := by rw [← hsum]
  have l2 : u.getReg .x15 = (limbs sum).2.2 := by rw [← hsum]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply eAt_eq_of_limbs
    have w0 := h.memAt 23 (by decide)
    have w1 := h.memAt 22 (by decide)
    have w2 := h.memAt 21 (by decide)
    rv_eval [] at w0 w1 w2
    rw [limbs_add, limbs_emasked, limbs_eAt, ← l0, ← l1, ← l2, ← mask0 c, ← h16]
    rv_eval [w0, w1, w2, Nat.reduceMul]
  · apply eAt_eq_of_limbs
    have w0 := h.memAt 20 (by decide)
    have w1 := h.memAt 19 (by decide)
    have w2 := h.memAt 18 (by decide)
    rv_eval [] at w0 w1 w2
    rw [limbs_add, limbs_emasked, limbs_eAt, ← l0, ← l1, ← l2, ← mask1 c, ← h16]
    rv_eval [w0, w1, w2, Nat.reduceMul]
  · apply eAt_eq_of_limbs
    have w0 := h.memAt 17 (by decide)
    have w1 := h.memAt 16 (by decide)
    have w2 := h.memAt 15 (by decide)
    rv_eval [] at w0 w1 w2
    rw [limbs_add, limbs_emasked, limbs_eAt, ← l0, ← l1, ← l2, ← mask2 c, ← h16]
    rv_eval [w0, w1, w2, Nat.reduceMul]
  · apply eAt_eq_of_limbs
    have w0 := h.memAt 14 (by decide)
    have w1 := h.memAt 13 (by decide)
    have w2 := h.memAt 12 (by decide)
    rv_eval [] at w0 w1 w2
    rw [limbs_add, limbs_emasked, limbs_eAt, ← l0, ← l1, ← l2, ← mask3 c, ← h16]
    rv_eval [w0, w1, w2, Nat.reduceMul]
  · apply eAt_eq_of_limbs
    have w0 := h.memAt 11 (by decide)
    have w1 := h.memAt 10 (by decide)
    have w2 := h.memAt 9 (by decide)
    rv_eval [] at w0 w1 w2
    rw [limbs_add, limbs_emasked, limbs_eAt, ← l0, ← l1, ← l2, ← mask4 c, ← h16]
    rv_eval [w0, w1, w2, Nat.reduceMul]
  · apply eAt_eq_of_limbs
    have w0 := h.memAt 8 (by decide)
    have w1 := h.memAt 7 (by decide)
    have w2 := h.memAt 6 (by decide)
    rv_eval [] at w0 w1 w2
    rw [limbs_add, limbs_emasked, limbs_eAt, ← l0, ← l1, ← l2, ← mask5 c, ← h16]
    rv_eval [w0, w1, w2, Nat.reduceMul]
  · apply eAt_eq_of_limbs
    have w0 := h.memAt 5 (by decide)
    have w1 := h.memAt 4 (by decide)
    have w2 := h.memAt 3 (by decide)
    rv_eval [] at w0 w1 w2
    rw [limbs_add, limbs_emasked, limbs_eAt, ← l0, ← l1, ← l2, ← mask6 c, ← h16]
    rv_eval [w0, w1, w2, Nat.reduceMul]
  · apply eAt_eq_of_limbs
    have w0 := h.memAt 2 (by decide)
    have w1 := h.memAt 1 (by decide)
    have w2 := h.memAt 0 (by decide)
    rv_eval [] at w0 w1 w2
    rw [limbs_add, limbs_emasked, limbs_eAt, ← l0, ← l1, ← l2, ← mask7 c, ← h16]
    rv_eval [w0, w1, w2, Nat.reduceMul]

theorem credit_entry {u u' : MachineState} (h : b80011408.Holds u u') {c : BitVec 16}
    (h16 : u.getReg .x16 = c.setWidth 64) {sum : E}
    (hsum : (u.getReg .x13, u.getReg .x14, u.getReg .x15) = limbs sum) {b : Nat} (hb : b < 8) :
    eAt u' ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * b)) =
      eAt u ((u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) * (16 : Word) +
        ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word))) + BitVec.ofNat 64 (24 * b)) +
        emasked sum (bmask c b) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := credit_entries h h16 hsum
  interval_cases b
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5
  · exact e6
  · exact e7

variable {e : Env}

set_option maxHeartbeats 2000000 in
/-- **One bucket credited**: the bit sums become `creditBits` of the bucket's byte, value and sum;
nothing else changes but one spill slot. -/
theorem credit (he : EnvOk e) {u u' : MachineState} (h : b80011408.Holds u u')
    (hsp : u.getReg .x2 = e.s.getReg .x2 - 1968) {c : BitVec 16}
    (h16 : u.getReg .x16 = c.setWidth 64) (hc : c.toNat < 2048) {sum : E}
    (hsum : (u.getReg .x13, u.getReg .x14, u.getReg .x15) = limbs sum) :
    eListAt u' (e.s.getReg .x2 - 1688) 64 = creditBits (c.toNat / 256) (c.setWidth 64 % 256#64) sum
      (eListAt u (e.s.getReg .x2 - 1688) 64) ∧
    ∀ a, ¬ Within a (e.s.getReg .x2 - 1688) 1536 → ¬ Within a (e.s.getReg .x2 - 1784) 8 →
      u'.getMem a = u.getMem a := by
  have hsp' := he.sp
  have hcb : (c.setWidth 64 : Word).toNat = c.toNat := by
    rw [BitVec.toNat_setWidth]; have := c.isLt; omega
  have hbyte := bucketByte (c.setWidth 64) (by rw [hcb]; exact hc)
  rw [hcb] at hbyte
  have hB : ∀ b < 8, u.getReg .x2 + (280 : Word) + (((u.getReg .x16 >>> 5) &&& (56 : Word)) *
      (16 : Word) + ((u.getReg .x16 >>> 5) &&& (56 : Word)) * (8 : Word)) +
      BitVec.ofNat 64 (24 * b) =
      e.s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * (8 * (c.toNat / 256) + b)) := by
    intro b hb
    rw [hsp, h16, mul24, hbyte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Sym.wordToNatLit]
    simp only [evalStack, eqKernelStack, mulStack, heapEnd] at hsp'
    omega
  have hW : ∀ a, (a.toNat < (e.s.getReg .x2).toNat - 1688 + 192 * (c.toNat / 256) ∨
      (e.s.getReg .x2).toNat - 1688 + 192 * (c.toNat / 256) + 192 ≤ a.toNat) →
      ¬ Within a (e.s.getReg .x2 - 1784) 8 → u'.getMem a = u.getMem a := fun a h1 h2 ↦
    h.frame a (by
      rv_eval [hsp, h16, mul24, hbyte]
      and_intros <;> addr_omega [h1, h2, hsp', hc])
  refine ⟨?_, fun a h1 h2 ↦ hW a (by addr_omega [h1, hsp', hc]) h2⟩
  have hS : (eListAt u (e.s.getReg .x2 - 1688) 64).length = 64 := eListAt_length _ _ _
  obtain ⟨cl, cv⟩ := creditBits_spec sum c (eListAt u (e.s.getReg .x2 - 1688) 64) hS
  apply List.ext_getElem (by rw [eListAt_length, cl])
  intro k h1 h2
  rw [eListAt_length] at h1
  rw [← List.getD_eq_getElem _ 0 h2, cv k h1, List.getD_eq_getElem _ _ (by rw [hS]; exact h1),
    eListAt_getElem, eListAt_getElem]
  by_cases hk : k / 8 = c.toNat / 256
  · have hk' : 8 * (c.toNat / 256) + k % 8 = k := by omega
    have he' := credit_entry h h16 hsum (b := k % 8) (by omega)
    rw [hB (k % 8) (by omega), hk'] at he'
    rw [he', bmask, emasked_bit, value_getLsbD]
    simp only [hk, true_and]
  · simp only [hk, false_and, ↓reduceIte, add_zero]
    unfold eAt
    rw [hW _ (by addr_omega [hk, h1, hsp', hc]) (by addr_omega [h1, hsp']),
      hW _ (by addr_omega [hk, h1, hsp', hc]) (by addr_omega [h1, hsp']),
      hW _ (by addr_omega [hk, h1, hsp', hc]) (by addr_omega [h1, hsp'])]

end Rv64Verifier.Proofs.Bytecode.Eval
