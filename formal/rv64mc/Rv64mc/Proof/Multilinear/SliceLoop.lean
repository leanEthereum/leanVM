/-
  Rv64mc.Proof.Multilinear.SliceLoop

  The arithmetic of a loop over `E` slices, as `rv_sym` states its pointers: element `j` at `q + 16 j`, a pointer
  kept at `q + 16 j + 8`, the end at `q + 8 + len <<< 4`. Shared by the loops of `multilinear.rs`, each fact stated
  with only what it needs so that no program state is carried into `omega`.
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Field

namespace Rv64mc.Proof.Multilinear

open RiscvZkvm.Rv64

theorem step_ptr (q : Word) (j : Nat) :
    q + BitVec.ofNat 64 (16 * j) + 24#64 = q + BitVec.ofNat 64 (16 * (j + 1)) + 8#64 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem start_ptr (q : Word) : q + 8#64 = q + BitVec.ofNat 64 (16 * 0) + 8#64 := by simp

/-- A live slice ends below the stack, with room for the end pointer. -/
theorem live_bound {env : Env} {m : MachineState} {q : Word} {n : Nat} (hl : env.Live m q n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) : q.toNat + n + 8 < 2 ^ 64 := by
  have := env.layout; have := env.stackLimit.isLt; unfold Env.Live at hl; omega

/-- The loop's exit test: past the last element. -/
theorem end_iff {q : Word} {j len : Nat} (hq : q.toNat + 16 * len + 8 < 2 ^ 64) (hj : j < len) :
    q + BitVec.ofNat 64 (16 * j) + 24#64 = q + 8#64 + BitVec.ofNat 64 len <<< 4 ↔ j + 1 = len := by
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_right_inj, ← BitVec.toNat_inj]
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem len_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) :
    a = b := by
  rw [← BitVec.toNat_inj] at h; simp at h; omega

theorem len_zero {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a = 0#64 ↔ a = 0 := by
  rw [← BitVec.toNat_inj]; simp; omega

/-! ## A pointer at the element itself: `q + 16 j`, the end `q + len <<< 4` -/

theorem step_ptr0 (q : Word) (j : Nat) :
    q + BitVec.ofNat 64 (16 * j) + 16#64 = q + BitVec.ofNat 64 (16 * (j + 1)) := by
  rw [show 16 * (j + 1) = 16 * j + 16 by omega, BitVec.ofNat_add, BitVec.add_assoc]

theorem start_ptr0 (q : Word) : q = q + BitVec.ofNat 64 (16 * 0) := by simp

theorem end_iff0 {q : Word} {j len : Nat} (hq : q.toNat + 16 * len < 2 ^ 64) (hj : j < len) :
    q + BitVec.ofNat 64 (16 * j) + 16#64 = q + BitVec.ofNat 64 len <<< 4 ↔ j + 1 = len := by
  rw [step_ptr0, BitVec.add_right_inj, ← BitVec.toNat_inj]
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

/-! ## Limbs -/

/-- `ONE + x` on limbs, as the code computes it: the low limb XORed with `1`. -/
theorem limbs_one_add (x : LeanVM.Parameters.E) :
    Model.limbs (1 + x) = ((Model.limbs x).1 ^^^ 1#64, (Model.limbs x).2) := by
  rw [← Model.eAdd_eq, Model.limbs_one, Model.eAdd, Model.eOne, BitVec.xor_comm, BitVec.zero_xor]

end Rv64mc.Proof.Multilinear
