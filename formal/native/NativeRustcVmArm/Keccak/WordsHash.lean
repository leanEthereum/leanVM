module

public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Keccak.WordsHash.Entry
public import NativeRustcVmArm.Keccak.WordsHash.Tail
public import NativeRustcVmArm.Keccak.WordsHash.Epi

/-!
# `keccak256_words::<hash_words's closure>` meets its contract

`keccak256WordsHash_spec`: given `memset`'s and `keccak_f`'s contracts, from its entry in a state
satisfying `Keccak256WordsHashPre` the function inevitably returns with `hashWords` of the slice's
words at `out` (`Keccak256WordsHashPost`). The entry zeroes the lanes and reaches the first whole
block's head or the last block's (`entry_run`), the whole blocks' loop the last block's head
(`full_loop`), which loads the last block (`tail_head`, `tail_run`), pads and permutes it
(`pad_run`) and returns its first four lanes (`epi_run`).
-/

namespace NativeRustcVmArm

open NativeRustcArm

public section

variable [Host]

/-- **`keccak256_words::<hash_words's closure>` meets its contract.** -/
theorem keccak256WordsHash_spec {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k)
    (hmemset : Spec (label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hkf : Spec (label NativeRustcVmArm.Vm.KeccakF.entryLabel) KeccakFPre KeccakFPost) :
    Spec (label NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre Keccak256WordsHashPost := by
  intro m0 hpre
  obtain ⟨hstk, hrc, hx1, hx2, hmap, hnw, hmo, hnwo, hap, hapo, -⟩ := hpre
  have g : WordsHash.Geo m0 := ⟨hstk, hx2, hmap, hnw, hap⟩
  rw [show label NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b0Offset) from hp.label NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.entry_at]
  refine Eventually.bind (WordsHash.entry_run hmemset hp g hx1) fun st h => ?_
  have hts : Eventually (step1 Host.exe) (WordsHash.TailStart m0 k) st := by
    rcases h with h | h
    · exact WordsHash.full_loop hkf hp g hrc h
    · exact .done _ h
  refine Eventually.bind hts fun st h => ?_
  refine Eventually.bind (WordsHash.tail_head hp g h) fun st h => ?_
  refine Eventually.bind (WordsHash.tail_run hp g h) fun st h => ?_
  refine Eventually.bind (WordsHash.pad_run hkf hp g hrc h) fun st h => ?_
  exact WordsHash.epi_run hp g ⟨hmo, hnwo, hapo⟩ h

end

end NativeRustcVmArm
