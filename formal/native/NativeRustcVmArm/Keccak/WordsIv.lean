module

public import NativeRustcVmArm.Code.Vm.IvWord.Names
public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfFiatShamirIv.Names
public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Keccak.WordsIv.Entry
public import NativeRustcVmArm.Keccak.WordsIv.Epi

/-!
# `keccak256_words::<fiat_shamir_iv's closure>` meets its contract

`keccak256WordsIv_spec`: given `memset`'s, `iv_word`'s and `keccak_f`'s contracts, from its entry
in a state satisfying `Keccak256WordsIvPre` the function inevitably returns with `fiatShamirIv`
of the bytecode at `out` (`Keccak256WordsIvPost`). The entry zeroes the lanes and reaches the
first whole block's head or the last block's (`entry_run`), the whole blocks' loop the last
block's head (`full_loop`), which takes the last block's words (`tail_run`), pads and permutes
(`pad_run`) and returns its first four lanes (`epi_run`). Every word is `iv_word`'s.
-/

namespace NativeRustcVmArm

open NativeRustcArm

public section

variable [Host]

/-- **`keccak256_words::<fiat_shamir_iv's closure>` meets its contract.** -/
theorem keccak256WordsIv_spec {k : Nat} (hp : Placed Vm.Keccak256WordsOfFiatShamirIv.code k)
    (hmemset : Spec (label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hiv : Spec (label NativeRustcVmArm.Vm.IvWord.entryLabel) IvWordPre IvWordPost)
    (hkf : Spec (label NativeRustcVmArm.Vm.KeccakF.entryLabel) KeccakFPre KeccakFPost) :
    Spec (label NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.entryLabel) Keccak256WordsIvPre Keccak256WordsIvPost := by
  intro m0 hpre
  obtain ⟨hstk, hrc, hx1, hx2, hsmall, hmap, hnw, hmo, hnwo, hap, hapo, -⟩ := hpre
  have g : WordsIv.Geo m0 := ⟨hstk, hx1, hx2, hsmall, hmap, hnw, hap⟩
  rw [show label NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b0Offset) from hp.label NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.entry_at]
  refine Eventually.bind (WordsIv.entry_run hmemset hp g) fun st h => ?_
  have hts : Eventually (step1 Host.exe) (WordsIv.TailStart m0 k) st := by
    rcases h with h | h
    · exact WordsIv.full_loop hkf hp hiv g hrc h
    · exact .done _ h
  refine Eventually.bind hts fun st h => ?_
  refine Eventually.bind (WordsIv.tail_run hp hiv g h) fun st h => ?_
  refine Eventually.bind (WordsIv.pad_run hkf hp g hrc h) fun st h => ?_
  exact WordsIv.epi_run hp g ⟨hmo, hnwo, hapo⟩ h

end

end NativeRustcVmArm
