module

public import NativeRustcVmX64.Keccak.WordsIv.Epi
public import NativeRustcVmX64.Code.Vm.IvWord.Names
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfFiatShamirIv.Names
public import NativeRustcVmX64.Code.Vm.KeccakF.Names
public import NativeRustcVmX64.Code.Vm.Memset.Names

/-!
# `keccak256_words::<fiat_shamir_iv's closure>` meets its contract (x86-64)

`keccak256WordsIv_spec`: given `memset`'s, `iv_word`'s and `keccak_f`'s contracts, from its entry
in a state satisfying `Keccak256WordsIvPre` the function inevitably returns with `fiatShamirIv` of
the bytecode at `out` (`Keccak256WordsIvPost`). The entry zeroes the lanes and reaches the first
whole block's head or the last block's (`entry_run`), the whole blocks' loop the last block's
head (`full_loop`), which takes the last block's words (`tail_head`, `tail_run`), pads and permutes
(`pad_run`) and returns its first four lanes (`epi_run`). Every word is `iv_word`'s, or zero from
the count (`WordsIv.lane2_step`).
-/

namespace NativeRustcVmX64

open NativeRustcX64

public section

variable [Host]

/-- **`keccak256_words::<fiat_shamir_iv's closure>` meets its contract.** -/
theorem keccak256WordsIv_spec {k : Nat} (hp : Placed Vm.Keccak256WordsOfFiatShamirIv.code k)
    (hmemset : Spec (label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hiv : Spec (label NativeRustcVmX64.Vm.IvWord.entryLabel) IvWordPre IvWordPost)
    (hkf : Spec (label NativeRustcVmX64.Vm.KeccakF.entryLabel) KeccakFPre KeccakFPost) :
    Spec (label NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.entryLabel) Keccak256WordsIvPre Keccak256WordsIvPost := by
  intro m0 hpre
  obtain ⟨hstk, hrc, hcnt, hlen, hsmall, hmap, hnw, hmo, hno, hap, hapo, -, hgot⟩ := hpre
  have g : WordsIv.Geo m0 := ⟨hstk, hrc, hcnt, hlen, hsmall, hmap, hnw, hap, hgot⟩
  rw [show label NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b0Offset) from hp.label NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.entry_at]
  refine Eventually.bind (WordsIv.entry_run hmemset hp g) fun st h => ?_
  have hts : Eventually (step1 Host.exe) (WordsIv.TailStart m0 k) st := by
    rcases h with h | h
    · exact WordsIv.full_loop hkf hiv hp g h
    · exact .done _ h
  refine Eventually.bind hts fun st h => ?_
  refine Eventually.bind (WordsIv.tail_head hp g h) fun st h => ?_
  refine Eventually.bind (WordsIv.tail_run hiv hp g h) fun st h => ?_
  refine Eventually.bind (WordsIv.pad_run hkf hp g h) fun st h => ?_
  exact WordsIv.epi_run hp g hmo hno hapo h

end

end NativeRustcVmX64
