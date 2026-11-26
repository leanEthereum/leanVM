/-
  Rv64mc.Proof.Runtime.VecHdrT

  What wave 5a's total proofs share about a returned vector: its header's accessors as words (`vecCap_eq`,
  `vecPtr_eq`, `vecLen_eq`; `GrowOne`'s `rvCapAt_eq` and `rvPtrAt_eq` give the `RawVecInner`'s), the result's
  `CloneT.ClonePostT` from its three header words (`post_ok`), and where `memcpy` writes into an aligned destination
  (`copyOut_in`). A light module, so that `Bytecode`, `Multilinear` and `Layout` proofs need not import each other
  for them.

  ## Main results

  * `vecCap_eq`, `vecPtr_eq`, `vecLen_eq`, `post_ok`, `copyOut_in`
-/

import Rv64mc.Proof.Runtime.CloneT
import Rv64mc.Proof.Runtime.GrowOne

namespace Rv64mc.Proof.Runtime.VecHdrT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.CloneT (ClonePostT)
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq)

theorem vecCap_eq (m : MachineState) (a : Word) : vecCap m a = m.getMem a := by
  simp only [vecCap, Layouts.Vec.cap]; exact congrArg _ (BitVec.add_zero a)

theorem vecPtr_eq (m : MachineState) (a : Word) : vecPtr m a = m.getMem (a + 8#64) := rfl

theorem vecLen_eq (m : MachineState) (a : Word) : vecLen m a = m.getMem (a + 16#64) := rfl

/-- **The result from its header's words**: capacity and length `n`, the buffer `P` of `n` elements of `s` bytes
    fresh since `m` unless `n = 0`. -/
theorem post_ok {env : Env} {regs : Reg → Word} {m M : MachineState} {P : Word} {s : Nat}
    (hwin : InWin env (regs .x10) 24) (hal : (regs .x10).toNat % 8 = 0)
    (h0 : M.getMem (regs .x10) = regs .x12) (h8 : M.getMem (regs .x10 + 8#64) = P)
    (h16 : M.getMem (regs .x10 + 16#64) = regs .x12)
    (hP : (regs .x12).toNat = 0 ∨ (0x10000000 ≤ P.toNat ∧ (env.next m).toNat ≤ P.toNat ∧
      P.toNat + (regs .x12).toNat * s ≤ (env.next M).toNat ∧ P.toNat % 8 = 0))
    (hn : (regs .x12).toNat * s < 2 ^ 63) {r : Reg → Word} : ClonePostT env s regs m r M := by
  have hc : rvCapAt (regs .x10) = regs .x10 := rvCapAt_eq _
  have hp : rvPtrAt (regs .x10) = regs .x10 + 8#64 := rfl
  refine ⟨⟨hwin, ⟨MemsetT.InWin.sub hwin (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega),
    hal, ?_, by rw [hc, h0]; exact hn⟩, by rw [vecLen_eq, vecCap_eq, h0, h16]⟩, by rw [vecLen_eq, h16], ?_⟩
  · rw [hc, hp, h0, h8]
    rcases hP with h | ⟨h1, -, h3, h4⟩
    · exact .inl h
    · exact .inr ⟨h1, by unfold Env.Live; omega, h4⟩
  · rw [vecPtr_eq, h8]
    rcases hP with h | ⟨-, h2, h3, -⟩
    · exact .inl h
    · exact .inr ⟨h2, by omega⟩

/-- A word `memcpy` may write, to `P` aligned, lies in `[P, P + n)`. -/
theorem copyOut_in {R : Reg → Word} {M : MachineState} {b P : Word} {n : Nat} (hR10 : R .x10 = P)
    (hR12 : (R .x12).toNat = n) (hP8 : P.toNat % 8 = 0) (hb : CopyOut R M b) : P.toNat ≤ b.toNat ∧ b.toNat < P.toNat + n := by
  unfold CopyOut DwordsOf InRange at hb
  rw [toNat_alignToDword, hR10, hR12] at hb
  omega

end Rv64mc.Proof.Runtime.VecHdrT
