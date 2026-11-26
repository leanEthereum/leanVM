/-
  Rv64mc.Proof.Whir.Arith

  The arithmetic of the WHIR family's loops over `E` slices, as `rv_sym` states their pointers: element `j` at
  `q + 16 j`, its second limb at `q + 16 j + 8`, the end at `q + len <<< 4`. Each fact is stated with only what it
  needs, so that no program state is carried into `omega`.
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Proof.Whir

open RiscvZkvm.Rv64

theorem ptr_start (q : Word) : q = q + BitVec.ofNat 64 (16 * 0) := by simp

theorem ptr_step (q : Word) (j : Nat) : q + BitVec.ofNat 64 (16 * j) + 16#64 = q + BitVec.ofNat 64 (16 * (j + 1)) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

/-- A live object ends below the stack. -/
theorem live_bound {env : Env} {m : MachineState} {q : Word} {n : Nat} (hl : env.Live m q n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) : q.toNat + n + 8 < 2 ^ 64 := by
  have := env.layout; have := env.stackLimit.isLt; unfold Env.Live at hl; omega

/-- The exit test of a loop whose pointer runs to `q + len <<< 4`: past the last element. -/
theorem end_iff {q : Word} {j len : Nat} (hq : q.toNat + 16 * len < 2 ^ 64) (hj : j < len) :
    q + BitVec.ofNat 64 (16 * j) + 16#64 = q + BitVec.ofNat 64 len <<< 4 ↔ j + 1 = len := by
  rw [BitVec.add_assoc, BitVec.add_right_inj, ← BitVec.toNat_inj]
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem len_zero {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a = 0#64 ↔ a = 0 := by
  rw [← BitVec.toNat_inj]; simp; omega

end Rv64mc.Proof.Whir
