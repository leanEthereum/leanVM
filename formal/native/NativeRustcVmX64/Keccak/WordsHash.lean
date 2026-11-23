module

public import NativeRustcVmX64.Keccak.WordsHash.Entry
public import NativeRustcVmX64.Keccak.WordsHash.Epi
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmX64.Code.Vm.KeccakF.Names
public import NativeRustcVmX64.Code.Vm.Memset.Names

/-!
# `keccak256_words::<hash_words's closure>` meets its contract (x86-64)

`keccak256WordsHash_spec`: given `memset`'s and `keccak_f`'s contracts, from its entry in a state
satisfying `Keccak256WordsHashPre` the function inevitably returns with `hashWords` of the slice's
words at `out` (`Keccak256WordsHashPost`). The entry zeroes the lanes and reaches the first whole
block's head or the last block's (`entry_run`), the whole blocks' loop the last block's head
(`full_loop`), which loads the last block (`tail_head`, `tail_run`), pads and permutes it
(`pad_run`) and returns its first four lanes (`epi_run`). Every lane of every block goes one of
two ways on whether its word is in the slice (`WordsHash.lane2_step`, `WordsHash.val2_step`).
-/

namespace NativeRustcVmX64

open NativeRustcX64

public section

variable [Host]

/-- **`keccak256_words::<hash_words's closure>` meets its contract.** -/
theorem keccak256WordsHash_spec {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k)
    (hmemset : Spec (label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hkf : Spec (label NativeRustcVmX64.Vm.KeccakF.entryLabel) KeccakFPre KeccakFPost) :
    Spec (label NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre Keccak256WordsHashPost := by
  intro m0 hpre
  obtain ⟨hstk, hrc, hcnt, hlen, hmap, hnw, hmo, hno, hap, hapo, -, hgot⟩ := hpre
  have g : WordsHash.Geo m0 := ⟨hstk, hrc, hcnt, hlen, hmap, hnw, hap, hgot⟩
  rw [show label NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b0Offset) from hp.label NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.entry_at]
  refine Eventually.bind (WordsHash.entry_run hmemset hp g) fun st h => ?_
  have hts : Eventually (step1 Host.exe) (WordsHash.TailStart m0 k) st := by
    rcases h with h | h
    · exact WordsHash.full_loop hkf hp g h
    · exact .done _ h
  refine Eventually.bind hts fun st h => ?_
  refine Eventually.bind (WordsHash.tail_head hp g h) fun st h => ?_
  refine Eventually.bind (WordsHash.tail_run hp g h) fun st h => ?_
  refine Eventually.bind (WordsHash.pad_run hkf hp g h) fun st h => ?_
  exact WordsHash.epi_run hp g hmo hno hapo h

end

end NativeRustcVmX64
