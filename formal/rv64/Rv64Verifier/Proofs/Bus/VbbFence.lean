import Rv64Verifier.Proofs.Bus.VbbValues

/-!
# `verify_bus_balance`: `Kept`'s buffers below `values`'

The GKR loop pushes into `values`' buffer in place, so what the rest reads from buffers allocated
before it must lie below that buffer (`Fence`): they do, being allocated earlier.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Transcript

/-- The `n`-byte elements of the `Vec` at `a` lie below `P`. -/
def BufBelow (u : MachineState) (a : Word) (n : Nat) (P : Word) : Prop :=
  n * (vecCap u a).toNat = 0 ∨ (vecPtr u a).toNat + n * (vecCap u a).toNat ≤ P.toNat

/-- `Kept`'s buffers lie below `P`. -/
structure Fence (s u : MachineState) (P : Word) : Prop where
  push : BufBelow u (s.getReg .x2 - 1080) 16 P ∧ BufBelow u (s.getReg .x2 - 1080 + 24) 16 P
  pull : BufBelow u (s.getReg .x2 - 1024) 16 P ∧ BufBelow u (s.getReg .x2 - 1024 + 24) 16 P
  count : BufBelow u (s.getReg .x2 - 968) 16 P ∧ BufBelow u (s.getReg .x2 - 968 + 24) 16 P
  alphas : BufBelow u (s.getReg .x2 - 912) 24 P
  weights : BufBelow u (s.getReg .x2 - 888) 24 P

theorem BufBelow.of_newBuf {s u z : MachineState} {a P : Word} {n : Nat}
    (hb : NewBuf s u (vecPtr u a) (n * (vecCap u a).toNat) 8) (h0 : z.getMem a = u.getMem a)
    (h8 : z.getMem (a + 8) = u.getMem (a + 8)) (hP : heapNext u ≤ P.toNat) : BufBelow z a n P := by
  simp only [BufBelow, NewBuf, vecPtr, vecCap] at hb ⊢
  rw [h0, h8]
  rcases hb.2 with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

theorem BufBelow.of_newVecE {s u z : MachineState} {a P : Word} {xs : List E}
    (hv : NewVecE s u a xs) (h0 : z.getMem a = u.getMem a)
    (h8 : z.getMem (a + 8) = u.getMem (a + 8)) (hP : heapNext u ≤ P.toNat) : BufBelow z a 24 P :=
  BufBelow.of_newBuf (by rw [Nat.mul_comm]; exact hv.buf) h0 h8 hP

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
