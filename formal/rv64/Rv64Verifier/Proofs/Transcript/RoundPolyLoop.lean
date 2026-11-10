import Rv64Verifier.Proofs.Transcript.RoundPoly

/-!
# `sumcheck_round_poly`'s two inlined `E::sum` loops

`0x8000c408` (the `Some` path) and `0x8000c554` (the `None` path): the XOR of the limbs of `n`
elements from `p`, in three registers, memory unchanged.
-/

namespace Rv64Verifier.Transcript.RoundPoly
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F44
  Rv64Verifier.Contracts LeanVM.Protocol.Verifier
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem eListAt_sum_succ (u : MachineState) (p : Word) (k : Nat) :
    Model.limbs (sumE (eListAt u p (k + 1))) =
      ((Model.limbs (sumE (eListAt u p k))).1 ^^^ u.getMem (p + BitVec.ofNat 64 (24 * k)),
       (Model.limbs (sumE (eListAt u p k))).2.1 ^^^ u.getMem (p + BitVec.ofNat 64 (24 * k) + 8),
       (Model.limbs (sumE (eListAt u p k))).2.2 ^^^ u.getMem (p + BitVec.ofNat 64 (24 * k) + 16)) := by
  rw [Samples.eListAt_succ, sumE_snoc, limbs_add, limbs_eAt]


theorem ofNat24_succ (k : Nat) :
    (BitVec.ofNat 64 (24 * (k + 1)) : Word) = BitVec.ofNat 64 (24 * k) + 24 := by
  rw [show 24 * (k + 1) = 24 * k + 24 by ring, BitVec.ofNat_add]
  rfl

theorem loop_step (p : Word) (k : Nat) :
    p + 16 + BitVec.ofNat 64 (24 * k) + 24 = p + 16 + BitVec.ofNat 64 (24 * (k + 1)) := by
  rw [ofNat24_succ]; ring

theorem loop_ne (p : Word) {k n : Nat} (hk : k < n) (hp : p.toNat + 16 + 24 * n < 2 ^ 64) :
    p + 16 + BitVec.ofNat 64 (24 * k) ≠ p + 16 + BitVec.ofNat 64 (24 * n) := by
  intro h
  have e1 : 24 * k < 2 ^ 64 := by omega
  have e2 : 24 * n < 2 ^ 64 := by omega
  have h2 : BitVec.ofNat 64 (24 * k) = BitVec.ofNat 64 (24 * n) := by
    have := congrArg (· - (p + 16)) h
    simpa only [add_sub_cancel_left] using this
  have h3 := congrArg BitVec.toNat h2
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt e1, Nat.mod_eq_of_lt e2] at h3
  omega

theorem loop_meas (p : Word) {a b : Nat} (hab : a ≤ b) (hb : b < 2 ^ 64) :
    (p + 16 + BitVec.ofNat 64 b - (p + 16 + BitVec.ofNat 64 a)).toNat = b - a := by
  have e : BitVec.ofNat 64 b = BitVec.ofNat 64 a + BitVec.ofNat 64 (b - a) := by
    rw [← BitVec.ofNat_add, Nat.add_sub_cancel' hab]
  have hlt : b - a < 2 ^ 64 := by omega
  rw [e, show p + 16 + (BitVec.ofNat 64 a + BitVec.ofNat 64 (b - a)) -
      (p + 16 + BitVec.ofNat 64 a) = BitVec.ofNat 64 (b - a) by ring, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt]

theorem off0 (p : Word) (k : Nat) :
    p + 16 + BitVec.ofNat 64 (24 * k) - 16 = p + BitVec.ofNat 64 (24 * k) := by ring

theorem off8 (p : Word) (k : Nat) :
    p + 16 + BitVec.ofNat 64 (24 * k) - 8 = p + BitVec.ofNat 64 (24 * k) + 8 := by ring

theorem off16 (p : Word) (k : Nat) :
    p + 16 + BitVec.ofNat 64 (24 * k) = p + BitVec.ofNat 64 (24 * k) + 16 := by ring

/-- The registers the first loop keeps. -/
def loop1Kept : List Reg :=
  [.x1, .x2, .x8, .x9, .x11, .x15, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

def loop2Kept : List Reg :=
  [.x1, .x2, .x5, .x8, .x9, .x10, .x11, .x12, .x13, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
    .x26, .x27]

/-- The loop's accumulator after `k` elements, the registers kept and memory unchanged. -/
structure Acc1 (u : MachineState) (p : Word) (k : Nat) (t : MachineState) : Prop where
  x13 : t.getReg .x13 = (Model.limbs (sumE (eListAt u p k))).1
  x12 : t.getReg .x12 = (Model.limbs (sumE (eListAt u p k))).2.1
  x10 : t.getReg .x10 = (Model.limbs (sumE (eListAt u p k))).2.2
  kept : ∀ r ∈ loop1Kept, t.getReg r = u.getReg r
  mem : ∀ a, t.getMem a = u.getMem a

theorem step1 {u t : MachineState} {p : Word} {n k : Nat} (hk : k < n)
    (hal : p.toNat % 8 = 0) (hlo : heapStart ≤ p.toNat) (hhi : p.toNat + 24 * n ≤ heapEnd)
    (hpc : t.pc = 0x8000c408) (x14 : t.getReg .x14 = p + 16 + BitVec.ofNat 64 (24 * k))
    (x15 : t.getReg .x15 = p + 16 + BitVec.ofNat 64 (24 * n)) (h : Acc1 u p k t) :
    ∃ t', Reaches Image.code t t' ∧ Acc1 u p (k + 1) t' ∧
      t'.getReg .x14 = p + 16 + BitVec.ofNat 64 (24 * (k + 1)) ∧
      t'.getReg .x15 = p + 16 + BitVec.ofNat 64 (24 * n) ∧
      t'.pc = if k + 1 < n then 0x8000c408 else 0x8000c428 := by
  obtain ⟨t', htt, h'⟩ := Sym.BlockSpec.reaches b8000c408_spec hpc (by
    rv_eval [x14]
    and_intros <;> (refine Samples.heap_valid ?_ ?_ ?_ <;> addr_omega [hal, hlo, hhi, hk]))
  have k' := b8000c408_keeps h'
  have hs := eListAt_sum_succ u p k
  have h24 : 24 * n < 2 ^ 64 := by simp only [heapEnd] at hhi; omega
  have hp24 : p.toNat + 16 + 24 * n < 2 ^ 64 := by simp only [heapEnd] at hhi; omega
  have n14 : t'.getReg .x14 = p + 16 + BitVec.ofNat 64 (24 * (k + 1)) := by
    rw [b8000c408_x14 h', x14, loop_step]
  refine ⟨t', htt, ⟨?_, ?_, ?_, fun r hr ↦ (k' r (mem_of_mem hr _)).trans (h.kept r hr),
    fun a ↦ (b8000c408_mem_same h' a).trans (h.mem a)⟩, n14, (k' .x15 (by decide)).trans x15, ?_⟩
  · rw [b8000c408_x13 h', x14, off0, h.mem, h.x13, hs, BitVec.xor_comm]
  · rw [b8000c408_x12 h', x14, off8, h.mem, h.x12, hs, BitVec.xor_comm]
  · rw [b8000c408_x10 h', x14, off16, h.mem, h.x10, hs, BitVec.xor_comm]
  · by_cases hl : k + 1 < n
    · rw [ite_eq_left hl]
      exact b8000c408_pc_taken h' (by rw [x14, x15, loop_step]; exact loop_ne p hl hp24)
    · rw [ite_eq_right hl]
      exact b8000c408_pc_not_taken h' (by rw [x14, x15, loop_step, show k + 1 = n by omega])

/-- The loop at `0x8000c408` over the `n` elements from `p`: their sum's limbs in `a3`, `a2`,
`a0`. -/
theorem sumLoop1 {u : MachineState} {p : Word} {n : Nat} (hpc : u.pc = 0x8000c408) (hn : 0 < n)
    (hal : p.toNat % 8 = 0) (hlo : heapStart ≤ p.toNat) (hhi : p.toNat + 24 * n ≤ heapEnd)
    (x14 : u.getReg .x14 = p + 16) (x15 : u.getReg .x15 = p + 16 + BitVec.ofNat 64 (24 * n))
    (x10 : u.getReg .x10 = 0) (x12 : u.getReg .x12 = 0) (x13 : u.getReg .x13 = 0) :
    ∃ v, Reaches Image.code u v ∧ v.pc = 0x8000c428 ∧ Acc1 u p n v := by
  have h0 : Model.limbs (sumE (eListAt u p 0)) = (0, 0, 0) := limbs_zero
  have h24 : 24 * n < 2 ^ 64 := by simp only [heapEnd] at hhi; omega
  refine Reaches.loop
    (fun t ↦ ∃ k, k < n ∧ t.pc = 0x8000c408 ∧ t.getReg .x14 = p + 16 + BitVec.ofNat 64 (24 * k) ∧
      t.getReg .x15 = p + 16 + BitVec.ofNat 64 (24 * n) ∧ Acc1 u p k t)
    (fun t ↦ (t.getReg .x15 - t.getReg .x14).toNat)
    (fun t ↦ t.pc = 0x8000c428 ∧ Acc1 u p n t) (fun t ⟨k, hk, hpct, h14, h15, hA⟩ ↦ ?_) u
    ⟨0, hn, hpc, by rw [x14]; simp, x15, ⟨by rw [x13, h0], by rw [x12, h0], by rw [x10, h0],
      fun _ _ ↦ rfl, fun _ ↦ rfl⟩⟩
  obtain ⟨t', htt, hA', n14, n15, npc⟩ := step1 hk hal hlo hhi hpct h14 h15 hA
  by_cases hl : k + 1 < n
  · rw [ite_eq_left hl] at npc
    refine Or.inr ⟨t', htt, ⟨k + 1, hl, npc, n14, n15, hA'⟩, ?_⟩
    rw [n14, n15, h14, h15, loop_meas p (by omega) h24, loop_meas p (by omega) h24]
    omega
  · rw [ite_eq_right hl] at npc
    rw [show k + 1 = n by omega] at hA'
    exact Or.inl ⟨t', htt, npc, hA'⟩

/-- `a + 16 + 24 b` through `24 b / 24` by `mulhu`, as both loops compute their end. -/
theorem end_ptr16 (a b : Word) (h2 : a.toNat + 16 + 24 * b.toNat < 2 ^ 64) :
    a + 16 + (rv64_mulhu (b * 16 + b * 8) (12297829382473034411 : Word) &&&
        (18446744073709551600 : Word)) +
      rv64_mulhu (b * 16 + b * 8) (12297829382473034411 : Word) >>> 4 * 8 =
    a + 16 + BitVec.ofNat 64 (24 * b.toNat) := by
  have hb : b * 16 + b * 8 = BitVec.ofNat 64 (24 * b.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul, BitVec.toNat_ofNat]
    simp only [Sym.wordToNatLit]
    rw [Nat.mod_eq_of_lt (a := b.toNat * 16) (by omega),
      Nat.mod_eq_of_lt (a := b.toNat * 8) (by omega),
      Nat.mod_eq_of_lt (a := b.toNat * 16 + b.toNat * 8) (by omega),
      Nat.mod_eq_of_lt (a := 24 * b.toNat) (by omega)]
    omega
  have hM : rv64_mulhu (b * 16 + b * 8) (12297829382473034411 : Word) =
      BitVec.ofNat 64 (16 * b.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [Runtime.toNat_mulhu, hb, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 24 * b.toNat) (by omega),
      Nat.mod_eq_of_lt (a := 16 * b.toNat) (by omega)]
    simp only [Sym.wordToNatLit]
    omega
  have hA : BitVec.ofNat 64 (16 * b.toNat) &&& (18446744073709551600 : Word) =
      BitVec.ofNat 64 (16 * b.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [MultilinearWords.toNat_and_f0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hS : BitVec.ofNat 64 (16 * b.toNat) >>> 4 * 8 = BitVec.ofNat 64 (8 * b.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 16 * b.toNat) (by omega), Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (a := 8 * b.toNat) (by omega)]
    simp only [Sym.wordToNatLit]
    omega
  rw [hM, hA, hS, BitVec.add_assoc (a + _), ← BitVec.ofNat_add,
    show 16 * b.toNat + 8 * b.toNat = 24 * b.toNat by omega]
  rfl

end Rv64Verifier.Transcript.RoundPoly
