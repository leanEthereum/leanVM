module

public import NativeRustcArm.SphincsVerify.SigMem
public import NativeRustcArm.SphincsVerify.Epilogue
public import NativeRustcArm.SphincsVerify.Calls
public import NativeRustc.Sphincs.EncodeFacts

/-!
# What the encoding reads, in the frame

Layer `l`'s counter at `5140 + 1028 l + 1024` (`Run.counter_at`), `PK.seed` at `448`
(`Run.seed_at`).
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs LeanVM.Protocol.KeccakHash

@[expose] public section

theorem bytesAt_take {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs)
    (n : Nat) :
    BytesAt d a (bs.take n) := fun i hi ↦ by
  simp only [List.length_take] at hi
  rw [h i (by omega), List.getElem_take]

namespace Run

variable (r : Run)

/-- **Layer `l`'s counter in the frame**: at `5140 + 1028 l + 1024`, little-endian. -/
theorem counter_at {m : MachineData} (hI : r.Inputs m) {l : Nat} (hl : l < 3) :
    BytesAt m.dmem (r.off (5140 + 1028 * l + 1024)) (le32 (r.layerSig l).counter) := by
  have h := bytesAt_slice hI.2.1 (4656 + 1028 * l + 1024) 4 (by rw [r.length_sigMem]; omega)
  rwa [r.sigMem_counter hl, off_add, show 484 + (4656 + 1028 * l + 1024) =
    5140 + 1028 * l + 1024 by omega] at h

/-- **`PK.seed` in the frame**: at `448`. -/
theorem seed_at {m : MachineData} (hI : r.Inputs m) : BytesAt m.dmem (r.off 448) r.seed :=
  bytesAt_take hI.1 16

theorem length_pkBytes : r.pkBytes.length = 32 := r.hpk

theorem length_seed : r.seed.length = 16 := by
  simp [seed, pk, PublicKey.fromBytes, r.hpk]

end Run

end

end NativeRustcArm.SphincsVerifyProof
