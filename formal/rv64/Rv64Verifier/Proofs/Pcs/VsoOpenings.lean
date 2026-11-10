import Rv64Verifier.Proofs.Pcs.VsoRound

/-!
# The proof's Merkle openings in memory, as the opening's Merkle checks read them

`Proof` (48 bytes) holds the stream (`Vec<E>`, at 0) and `merkle_openings`
(`Vec<Vec<MerklePath>>`, at 24); a phase is a `Vec<MerklePath>` (24 bytes); a `MerklePath` is 56
bytes: the leaf's words (`Vec<K>`, at 0), the siblings (`Vec<[u8; 32]>`, at 24, read as bytes),
`leaf_index` (at 48), as `0x8000aa28`..`0x8000aad4` read them. `VsoOpeningsAt` is what the Merkle block's proof
assumes of the openings, an instance of `VsoSpec`'s `OpeningsAt`: memory at the entry stands for
the transcript's openings (`count`, `phases`), in mapped aligned regions that the function never
writes (`VsoOpenMem`, which does not depend on the transcript).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol LeanVM.Protocol.Compile

/-- The `MerklePath` at `a`. -/
def openingAt (u : MachineState) (a : Word) : Opening :=
  ⟨(u.getMem (a + 48)).toNat, (vecWords u a).map BF64.ofBitVec,
    (List.range (vecLen u (a + 24)).toNat).map fun i ↦
      digestBytesAt u (vecPtr u (a + 24) + BitVec.ofNat 64 (32 * i))⟩

/-- Phase `i`'s header, of the proof at `P`. -/
@[rv_addr] def phaseHdr (u : MachineState) (P : Word) (i : ℕ) : Word :=
  vecPtr u (P + 24) + BitVec.ofNat 64 (24 * i)

/-- Path `j` of phase `i`. -/
@[rv_addr] def pathAddr (u : MachineState) (P : Word) (i j : ℕ) : Word :=
  vecPtr u (phaseHdr u P i) + BitVec.ofNat 64 (56 * j)

/-- Phase `i` of the proof at `P`. -/
def phaseAt (u : MachineState) (P : Word) (i : ℕ) : List Opening :=
  (List.range (vecLen u (phaseHdr u P i)).toNat).map fun j ↦ openingAt u (pathAddr u P i j)

/-- The bytes the openings of the proof at `P` occupy beyond the `Proof` itself: the siblings'
widened to the doublewords holding them. -/
def InOpenings (u : MachineState) (P : Word) (y : Word) : Prop :=
  Within y (vecPtr u (P + 24)) (24 * (vecLen u (P + 24)).toNat) ∨
    ∃ i < (vecLen u (P + 24)).toNat,
      Within y (vecPtr u (phaseHdr u P i)) (56 * (vecLen u (phaseHdr u P i)).toNat) ∨
      ∃ j < (vecLen u (phaseHdr u P i)).toNat,
        Within y (vecPtr u (pathAddr u P i j)) (8 * (vecLen u (pathAddr u P i j)).toNat) ∨
        Within y (alignToDword (vecPtr u (pathAddr u P i j + 24)))
          (sibSpan (vecPtr u (pathAddr u P i j + 24)) (vecLen u (pathAddr u P i j + 24)).toNat)

/-- The openings' memory at the entry `s`, whatever transcript they stand for. -/
structure VsoOpenMem (s : MachineState) (p : Word) : Prop where
  /-- The phase headers, the paths and the leaves mapped and 8-aligned, the siblings mapped. -/
  hdrs : (vecLen s (proofAt s p + 24)).toNat = 0 ∨
    Region (vecPtr s (proofAt s p + 24)) (24 * (vecLen s (proofAt s p + 24)).toNat)
  paths : ∀ i < (vecLen s (proofAt s p + 24)).toNat,
    (vecLen s (phaseHdr s (proofAt s p) i)).toNat = 0 ∨
      Region (vecPtr s (phaseHdr s (proofAt s p) i))
        (56 * (vecLen s (phaseHdr s (proofAt s p) i)).toNat)
  leaves : ∀ i < (vecLen s (proofAt s p + 24)).toNat,
    ∀ j < (vecLen s (phaseHdr s (proofAt s p) i)).toNat,
      ((vecLen s (pathAddr s (proofAt s p) i j)).toNat = 0 ∨
        Region (vecPtr s (pathAddr s (proofAt s p) i j))
          (8 * (vecLen s (pathAddr s (proofAt s p) i j)).toNat)) ∧
      ((vecLen s (pathAddr s (proofAt s p) i j + 24)).toNat = 0 ∨
        Mapped (vecPtr s (pathAddr s (proofAt s p) i j + 24))
          (32 * (vecLen s (pathAddr s (proofAt s p) i j + 24)).toNat))
  /-- Never written: apart from the stack, `NEXT`, the free heap, the sponge and the root. -/
  src : ∀ y, InOpenings s (proofAt s p) y →
    (y.toNat < heapNext s ∨ heapEnd ≤ y.toNat) ∧ ¬ Within y (stackLo s vsoStack) vsoStack ∧
      ¬ Within y nextAddr 8 ∧ ¬ Within y (s.getReg .x10 + 8) 352 ∧ ¬ Within y (s.getReg .x11) 32

/-- **The openings, at the entry `s`, of the transcript at `p` standing for `T`.** -/
structure VsoOpeningsAt (s : MachineState) (p : Word) (T : Model.TState) : Prop
    extends VsoOpenMem s p where
  count : (vecLen s (proofAt s p + 24)).toNat = T.proof.openings.length
  phases : ∀ i < T.proof.openings.length, phaseAt s (proofAt s p) i = T.proof.openings[i]!

end Rv64Verifier.Proofs.Pcs.Vso
