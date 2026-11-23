module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfFiatShamirIv
public meta import NativeRustcVmArm.Code.Vm.Keccak256WordsOfFiatShamirIv
public meta import NativeRustcArm.Sym

/-!
# `keccak256_words::<fiat_shamir_iv's closure>`'s blocks, run by the symbolic executor

The blocks of `NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv` outside the whole blocks' lanes,
each from a symbolic state whose region 0 is the 288-byte stack frame:

- `entry` (`b0`): saves the callee-saved registers, calls `memset` to zero the state at 8;
  `setup` (`b1`): the last block's first word `17 (len / 136)` in X24 (32-bit division);
- the last block: its head `tailHead` (`b2`); lane `j` of word `17 nb + j < count`, `iv_word`'s
  call `tailC j` (`b3`, `b77`, `b79`, …, `b107`) and its XOR `tailX j` (`b4`, `b78`, …, `b106`),
  or past it the zero lane `tailZ j` (`b76`, `b5` to `b19`); lane 16's word zero (`tailZ16`,
  `b20`);
- the epilogue `epi` (`b109`): the digest into region 1, the 32 bytes at X19.

The whole blocks' lanes are in `BlocksFull`, the padding in `BlocksPad`.
-/

namespace NativeRustcVmArm.WordsIv

open NativeRustcArm NativeRustcArm.Sym Vm.Keccak256WordsOfFiatShamirIv

set_option Elab.async false

@[expose] public section

/-- The entry's start: region 0 the frame below SP. -/
def startEntry : SState := init [(288, true)] (.ptr 0 288) []

/-- A start with region 0 the frame from SP. -/
def startMain : SState := init [(288, true)] (.ptr 0 0) []

/-- The epilogue's: region 1 the digest, X19 its address. -/
def startEpi : SState := init [(288, true), (32, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

sym_block entry := exec b0 startEntry
sym_block setup := exec b1 startMain
sym_block tailHead := exec b2 startMain
sym_block tailC0 := exec b3 startMain
sym_block tailX0 := exec b4 startMain
sym_block tailC1 := exec b77 startMain
sym_block tailX1 := exec b78 startMain
sym_block tailC2 := exec b79 startMain
sym_block tailX2 := exec b80 startMain
sym_block tailC3 := exec b81 startMain
sym_block tailX3 := exec b82 startMain
sym_block tailC4 := exec b83 startMain
sym_block tailX4 := exec b84 startMain
sym_block tailC5 := exec b85 startMain
sym_block tailX5 := exec b86 startMain
sym_block tailC6 := exec b87 startMain
sym_block tailX6 := exec b88 startMain
sym_block tailC7 := exec b89 startMain
sym_block tailX7 := exec b90 startMain
sym_block tailC8 := exec b91 startMain
sym_block tailX8 := exec b92 startMain
sym_block tailC9 := exec b93 startMain
sym_block tailX9 := exec b94 startMain
sym_block tailC10 := exec b95 startMain
sym_block tailX10 := exec b96 startMain
sym_block tailC11 := exec b97 startMain
sym_block tailX11 := exec b98 startMain
sym_block tailC12 := exec b99 startMain
sym_block tailX12 := exec b100 startMain
sym_block tailC13 := exec b101 startMain
sym_block tailX13 := exec b102 startMain
sym_block tailC14 := exec b103 startMain
sym_block tailX14 := exec b104 startMain
sym_block tailC15 := exec b105 startMain
sym_block tailX15 := exec b106 startMain
sym_block tailC16 := exec b107 startMain
sym_block tailZ0 := exec b76 startMain
sym_block tailZ1 := exec b5 startMain
sym_block tailZ2 := exec b6 startMain
sym_block tailZ3 := exec b7 startMain
sym_block tailZ4 := exec b8 startMain
sym_block tailZ5 := exec b9 startMain
sym_block tailZ6 := exec b10 startMain
sym_block tailZ7 := exec b11 startMain
sym_block tailZ8 := exec b12 startMain
sym_block tailZ9 := exec b13 startMain
sym_block tailZ10 := exec b14 startMain
sym_block tailZ11 := exec b15 startMain
sym_block tailZ12 := exec b16 startMain
sym_block tailZ13 := exec b17 startMain
sym_block tailZ14 := exec b18 startMain
sym_block tailZ15 := exec b19 startMain
sym_block tailZ16 := exec b20 startMain
sym_block epi := exec b109 startEpi

end NativeRustcVmArm.WordsIv
