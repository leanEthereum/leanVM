module

public import NativeRustcVmArm.Keccak.WordsIv.Blocks
public meta import NativeRustcVmArm.Keccak.WordsIv.Blocks

/-!
# `keccak256_words::<fiat_shamir_iv's closure>`'s whole blocks, run by the symbolic executor

From `startMain`: X25 zeroed (`fullInit`, `b21`); the head of whole block `b` (`fullHead`, `b25`,
X25 its first word `17 b`); lane `j`'s call of `iv_word` (`fullC j`: `b26`, `b45`, `b47`, …,
`b73`, `b22`) and its XOR (`fullX j`: `b27`, `b46`, …, `b74`); lane 16's XOR and the call of
`keccak_f` (`fullEnd`, `b23`); the next block (`fullNext`, `b24`). Every word of a whole block is
below the count, so the zero lanes (`b28` to `b44`, `b75`) are never run.
-/

namespace NativeRustcVmArm.WordsIv

open NativeRustcArm NativeRustcArm.Sym Vm.Keccak256WordsOfFiatShamirIv

set_option Elab.async false

sym_block fullInit := exec b21 startMain
sym_block fullHead := exec b25 startMain
sym_block fullC0 := exec b26 startMain
sym_block fullX0 := exec b27 startMain
sym_block fullC1 := exec b45 startMain
sym_block fullX1 := exec b46 startMain
sym_block fullC2 := exec b47 startMain
sym_block fullX2 := exec b48 startMain
sym_block fullC3 := exec b49 startMain
sym_block fullX3 := exec b50 startMain
sym_block fullC4 := exec b51 startMain
sym_block fullX4 := exec b52 startMain
sym_block fullC5 := exec b53 startMain
sym_block fullX5 := exec b54 startMain
sym_block fullC6 := exec b55 startMain
sym_block fullX6 := exec b56 startMain
sym_block fullC7 := exec b57 startMain
sym_block fullX7 := exec b58 startMain
sym_block fullC8 := exec b59 startMain
sym_block fullX8 := exec b60 startMain
sym_block fullC9 := exec b61 startMain
sym_block fullX9 := exec b62 startMain
sym_block fullC10 := exec b63 startMain
sym_block fullX10 := exec b64 startMain
sym_block fullC11 := exec b65 startMain
sym_block fullX11 := exec b66 startMain
sym_block fullC12 := exec b67 startMain
sym_block fullX12 := exec b68 startMain
sym_block fullC13 := exec b69 startMain
sym_block fullX13 := exec b70 startMain
sym_block fullC14 := exec b71 startMain
sym_block fullX14 := exec b72 startMain
sym_block fullC15 := exec b73 startMain
sym_block fullX15 := exec b74 startMain
sym_block fullC16 := exec b22 startMain
sym_block fullEnd := exec b23 startMain
sym_block fullNext := exec b24 startMain

end NativeRustcVmArm.WordsIv
