import Rv64Verifier.Proofs.Transcript.Repr
import Rv64Verifier.Proofs.Hash.Contracts

/-!
# `keccak_f`'s contract on `stateAt`

`Contracts.KeccakFSpec` is stated on doubleword lists (`readWords`) and `keccakFRust`; here it is
read on `stateAt` and `keccakF1600` (`stateAt_keccakF`), and its tables come from `.rodata`
(`keccakTables_of_rodata`).
-/

namespace Rv64Verifier.Transcript
open RiscvZkvm.Rv64 LeanVM.Semantics Rv64Verifier.Model Rv64Verifier.Contracts

theorem readWords_stateAt (s : MachineState) (a : Word) :
    s.readWords a 25 = stateBits (stateAt s a) := by
  apply List.ext_getElem
  · simp [stateBits]
  · intro i h1 h2
    rw [readWords_getElem _ _ _ _ (by rwa [readWords_length] at h1) h1]
    simp [stateBits, stateAt]

theorem stateBits_injective {a b : KeccakState} (h : stateBits a = stateBits b) : a = b := by
  apply Vector.toList_inj.mp
  exact List.map_injective_iff.mpr (fun x y hxy ↦ UInt64.toBitVec_inj.mp hxy) h

/-- `keccak_f`'s result as a state. -/
theorem stateAt_keccakF {s t : MachineState} {a : Word}
    (h : t.readWords a 25 = keccakFRust (s.readWords a 25)) :
    stateAt t a = keccakF1600 (stateAt s a) := by
  apply stateBits_injective
  rw [← readWords_stateAt, h, readWords_stateAt, keccakFRust_eq]

/-- `.rodata` holds Keccak's tables. -/
theorem keccakTables_of_rodata {s : MachineState} (h : RodataOk s) : KeccakTables s := by
  have hd : (List.range 62).all (fun i ↦ rodataWords.contains
      (keccakTablesAddr + BitVec.ofNat 64 (8 * i), keccakTableWords.getD i 0)) = true := by
    decide +kernel
  apply List.ext_getElem
  · rw [readWords_length]; rfl
  · intro i hi _
    rw [readWords_length] at hi
    have := List.all_eq_true.mp hd i (List.mem_range.mpr hi)
    rw [List.contains_iff_mem] at this
    rw [readWords_getElem _ _ _ _ hi (by rw [readWords_length]; exact hi), h _ this, List.getD_eq_getElem _ _ (by
      simp [keccakTableWords, keccakRhoWords, keccakRCRust, keccakPiRust]; omega)]

end Rv64Verifier.Transcript
