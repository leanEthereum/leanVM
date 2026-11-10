import Rv64Verifier.Proofs.Transcript.Repr
import Rv64Verifier.Proofs.Hash.Contracts

/-!
# The proof's Merkle openings in memory

`Proof.merkle_openings: Vec<Vec<MerklePath>>` at the proof's `24`; a phase is a `Vec<MerklePath>`,
a `MerklePath` (56 bytes) its leaf `Vec<K>` at `0`, its siblings `Vec<[u8; 32]>` at `24` (alignment
one: read as bytes, a digest's lanes little-endian) and `leaf_index` at `48`.

`OpeningsAt s p T` says the openings of the transcript at `p`'s proof are `T.proof.openings`, in
the shape `PcsContracts.VsoSpec` takes. `OpenFoot s p` is the bytes it reads: the `Vec` buffers
(the siblings' widened to whole doublewords, as `getByte` reads them), the headers inside them;
the outer header lies in the `Proof`'s 48 bytes.
-/

namespace Rv64Verifier.Transcript
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model

/-- A lane from its eight bytes, little-endian. -/
def laneOfBytes (bs : List (BitVec 8)) : UInt64 :=
  UInt64.ofBitVec (bs.foldr (fun b acc ↦ (acc <<< 8) ||| b.setWidth 64) 0)

/-- The digest whose 32 bytes start at `a`. -/
def digestBytesAt (s : MachineState) (a : Word) : Digest :=
  Vector.ofFn fun i : Fin 4 ↦ laneOfBytes (Contracts.bytesAt s (a + BitVec.ofNat 64 (8 * i.val)) 8)

/-- `n` words of `K` from `a`. -/
def kListAt (s : MachineState) (a : Word) (n : Nat) : List K :=
  (List.range n).map fun i ↦ BF64.ofBitVec (s.getMem (a + BitVec.ofNat 64 (8 * i)))

/-- The `MerklePath` at `a` is `o`. -/
structure PathAt (s : MachineState) (a : Word) (o : Opening) : Prop where
  leaf : kListAt s (vecPtr s a) (vecLen s a).toNat = o.leaf
  path : (List.range (vecLen s (a + 24)).toNat).map
    (fun i ↦ digestBytesAt s (vecPtr s (a + 24) + BitVec.ofNat 64 (32 * i))) = o.path
  leafIndex : (s.getMem (a + 48)).toNat = o.leafIndex

/-- The `Vec<MerklePath>` at `a` is the phase `ph`. -/
structure PhaseAt (s : MachineState) (a : Word) (ph : List Opening) : Prop where
  len : (vecLen s a).toNat = ph.length
  paths : ∀ j (h : j < ph.length), PathAt s (vecPtr s a + BitVec.ofNat 64 (56 * j)) ph[j]

/-- Where the openings' outer `Vec` is: the proof's `24`. -/
@[rv_addr] def openingsVec (s : MachineState) (p : Word) : Word := proofAt s p + 24

/-- The transcript at `p`'s proof holds `T`'s openings. -/
structure OpeningsAt (s : MachineState) (p : Word) (T : TState) : Prop where
  len : (vecLen s (openingsVec s p)).toNat = T.proof.openings.length
  phases : ∀ k (h : k < T.proof.openings.length),
    PhaseAt s (vecPtr s (openingsVec s p) + BitVec.ofNat 64 (24 * k)) T.proof.openings[k]

/-- The bytes a `MerklePath` at `a` reads beyond its header: the leaf's buffer, the siblings'
doublewords. -/
def PathFoot (s : MachineState) (a y : Word) : Prop :=
  Within y (vecPtr s a) (8 * (vecLen s a).toNat) ∨
    Within y (vecPtr s (a + 24) &&& ~~~7#64) (32 * (vecLen s (a + 24)).toNat + 8)

/-- The bytes a phase at `a` reads beyond its header: its buffer, its paths'. -/
def PhaseFoot (s : MachineState) (a y : Word) : Prop :=
  Within y (vecPtr s a) (56 * (vecLen s a).toNat) ∨
    ∃ j < (vecLen s a).toNat, PathFoot s (vecPtr s a + BitVec.ofNat 64 (56 * j)) y

/-- The bytes the openings of the transcript at `p` read beyond the `Proof`. -/
def OpenFoot (s : MachineState) (p y : Word) : Prop :=
  Within y (vecPtr s (openingsVec s p)) (24 * (vecLen s (openingsVec s p)).toNat) ∨
    ∃ k < (vecLen s (openingsVec s p)).toNat,
      PhaseFoot s (vecPtr s (openingsVec s p) + BitVec.ofNat 64 (24 * k)) y

end Rv64Verifier.Transcript
