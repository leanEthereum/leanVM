import Rv64Verifier.Proofs.Walk.R19E

/-!
# `walk` R19, the public input's claims: `r19pB`, the evaluation

From `0x80003bdc` (`AtA`): the two-element `Vec` at `S - 512` (`reserve` returns at once), the
limb's words `lo, hi` into the new buffer `Q`, `Scaler::new` (`Plain`: one use), the length checks,
`(hi + lo) * c` (`mul`, into `S - 224`), `lo + (hi + lo) * c` into `Q` (`0x80003ce0`), to
`0x80003e58` (`AtB`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Limb `i`'s claim's value: `lo + (lo + hi) * c`. -/
def pubVal (s : MachineState) (i : Nat) (c : E) : E :=
  ofK (BF64.ofBitVec (pubLo s i)) + (ofK (BF64.ofBitVec (pubLo s i)) +
    ofK (BF64.ofBitVec (pubHi s i))) * c

/-- At `0x80003e58`, the value computed. -/
structure AtB (s u y : MachineState) (i : Nat) (c : E) (n : Nat) (L Q : Word) : Prop where
  st : StepW s u y (IW s) False
  pc : y.pc = 0x80003e58
  qa : Q.toNat % 8 = 0
  q1 : (vecPtr y (s.getReg .x2 - 1488)).toNat + 24 * n ≤ Q.toNat
  q2 : Q.toNat + 48 ≤ heapNext y
  cpa : (vecPtr y (s.getReg .x2 - 1488)).toNat % 8 = 0
  cp1 : heapNext u ≤ (vecPtr y (s.getReg .x2 - 1488)).toNat
  cl : vecLen y (s.getReg .x2 - 1488) = BitVec.ofNat 64 n
  ce : vecEs y (s.getReg .x2 - 1488) = c :: List.replicate (n - 1) 0
  val : eAt y Q = pubVal s i c
  x25 : y.getReg .x25 = Q
  s160 : y.getMem (s.getReg .x2 - 2496) = L + BitVec.ofNat 64 i
  s152 : y.getMem (s.getReg .x2 - 2504) = BitVec.ofNat 64 i
  s192 : y.getMem (s.getReg .x2 - 2464) = BitVec.ofNat 64 i + 1

theorem eAt_ofK_word {t : MachineState} {a w : Word} (h0 : t.getMem a = w)
    (h1 : t.getMem (a + 8) = 0) (h2 : t.getMem (a + 16) = 0) : eAt t a = ofK (BF64.ofBitVec w) :=
  eAt_eq_of_limbs (by rw [h0, h1, h2, limbs_ofK]; rfl)

end Rv64Verifier.Proofs.Walk
