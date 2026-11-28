module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfHashWords
public meta import NativeRustcVmArm.Code.Vm.Keccak256WordsOfHashWords
public meta import NativeRustcArm.Sym

/-!
# `keccak256_words::<hash_words's closure>`'s blocks, run by the symbolic executor

The blocks of `NativeRustcVmArm.Vm.Keccak256WordsOfHashWords` the function runs (block `b58`, the
whole blocks' unloaded last lane, is never reached), each from a symbolic state whose region 0 is
the 288-byte stack frame:

- `entry` (`b0`), from the entry: SP the frame's top; it saves the callee-saved registers and calls
  `memset` to zero the state at 8; `setup` (`b1`): the word bound `min(count, n)` in X22, the
  whole blocks' count in X24 and their words' in X23;
- the whole blocks' loop: `fullInit` (`b20`), its head `fullHead` (`b24`), the lanes `full j`
  (`b25`, `b43` to `b57`, `b21`; the block's 17 words region 1, X26 at its byte 64), the last
  lane's XOR and the call of `keccak_f` (`fullXor`, `b22`), the next block (`fullNext`, `b23`);
- the last block: `tailHead` (`b2`), lane `j` of word `base + j < min(count, n)`, loaded (`tailL j`:
  `b3`, `b60` to `b75`, the word region 1, at X21 plus X23 or X9 words), or past it, zero
  (`tailZ j`: `b59`, `b4` to `b19`); the padding at byte `8 t` and the call of `keccak_f`
  (`pad t`, `b76`, `t < 17`: the padded lane's address an alias of region 0 at `8 + 8 t`);
- the epilogue `epi` (`b77`): the digest into region 1, the 32 bytes at X19.
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym Vm.Keccak256WordsOfHashWords

set_option Elab.async false

@[expose] public section

/-- The entry's start: region 0 the frame below SP. -/
def startEntry : SState := init [(288, true)] (.ptr 0 288) []

/-- A start with region 0 the frame from SP. -/
def startMain : SState := init [(288, true)] (.ptr 0 0) []

/-- A whole block's lanes: region 1 its 17 words, X26 at their byte 64. -/
def startFull : SState := init [(288, true), (136, false)] (.ptr 0 0) [(.X26, .ptr 1 64)]

/-- The address of word X23 of the slice at X21. -/
def addrX23 : Sym := .bin .add .W64 (.reg .X21) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X23))

/-- The address of word X9 of the slice at X21. -/
def addrX9 : Sym := .bin .add .W64 (.reg .X21) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X9))

/-- The last block's first lane, loaded: region 1 the word at X21 plus X23 words. -/
def startTailL0 : SState := init [(288, true), (8, false)] (.ptr 0 0) [] [] [] [(addrX23, 1, 0)]

/-- The last block's lane, loaded: region 1 the word at X21 plus X9 words. -/
def startTailL : SState := init [(288, true), (8, false)] (.ptr 0 0) [] [] [] [(addrX9, 1, 0)]

/-- The byte offset of the padded lane in the state: `(len - 136 N) & !7`. -/
def padIdx : Sym :=
  .bin .and .W64 (.bin .sub .W64 (.reg .X20) (.bin .mul .W64 (.reg .X24) (.lit 136)))
    (.lit 18446744073709551608)

/-- The padding at lane `t`: the padded lane's address an alias of region 0 at `8 + 8 t`. -/
def startPad (t : Nat) : SState :=
  init [(288, true)] (.ptr 0 0) [] [] []
    [(.bin .add .W64 (.ptr 0 8) (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 padIdx), 0, 8 + 8 * t)]

/-- The epilogue's: region 1 the digest, X19 its address. -/
def startEpi : SState := init [(288, true), (32, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

sym_block entry := exec b0 startEntry
sym_block setup := exec b1 startMain
sym_block fullInit := exec b20 startMain
sym_block fullHead := exec b24 startMain
sym_block fullXor := exec b22 startMain
sym_block fullNext := exec b23 startMain
sym_block tailHead := exec b2 startMain
sym_block epi := exec b77 startEpi

sym_block full0 := exec b25 startFull
sym_block full1 := exec b43 startFull
sym_block full2 := exec b44 startFull
sym_block full3 := exec b45 startFull
sym_block full4 := exec b46 startFull
sym_block full5 := exec b47 startFull
sym_block full6 := exec b48 startFull
sym_block full7 := exec b49 startFull
sym_block full8 := exec b50 startFull
sym_block full9 := exec b51 startFull
sym_block full10 := exec b52 startFull
sym_block full11 := exec b53 startFull
sym_block full12 := exec b54 startFull
sym_block full13 := exec b55 startFull
sym_block full14 := exec b56 startFull
sym_block full15 := exec b57 startFull
sym_block full16 := exec b21 startFull
sym_block tailZ0 := exec b59 startMain
sym_block tailZ1 := exec b4 startMain
sym_block tailZ2 := exec b5 startMain
sym_block tailZ3 := exec b6 startMain
sym_block tailZ4 := exec b7 startMain
sym_block tailZ5 := exec b8 startMain
sym_block tailZ6 := exec b9 startMain
sym_block tailZ7 := exec b10 startMain
sym_block tailZ8 := exec b11 startMain
sym_block tailZ9 := exec b12 startMain
sym_block tailZ10 := exec b13 startMain
sym_block tailZ11 := exec b14 startMain
sym_block tailZ12 := exec b15 startMain
sym_block tailZ13 := exec b16 startMain
sym_block tailZ14 := exec b17 startMain
sym_block tailZ15 := exec b18 startMain
sym_block tailZ16 := exec b19 startMain
sym_block tailL0 := exec b3 startTailL0
sym_block tailL1 := exec b60 startTailL
sym_block tailL2 := exec b61 startTailL
sym_block tailL3 := exec b62 startTailL
sym_block tailL4 := exec b63 startTailL
sym_block tailL5 := exec b64 startTailL
sym_block tailL6 := exec b65 startTailL
sym_block tailL7 := exec b66 startTailL
sym_block tailL8 := exec b67 startTailL
sym_block tailL9 := exec b68 startTailL
sym_block tailL10 := exec b69 startTailL
sym_block tailL11 := exec b70 startTailL
sym_block tailL12 := exec b71 startTailL
sym_block tailL13 := exec b72 startTailL
sym_block tailL14 := exec b73 startTailL
sym_block tailL15 := exec b74 startTailL
sym_block tailL16 := exec b75 startTailL
sym_block pad0 := exec b76 (startPad 0)
sym_block pad1 := exec b76 (startPad 1)
sym_block pad2 := exec b76 (startPad 2)
sym_block pad3 := exec b76 (startPad 3)
sym_block pad4 := exec b76 (startPad 4)
sym_block pad5 := exec b76 (startPad 5)
sym_block pad6 := exec b76 (startPad 6)
sym_block pad7 := exec b76 (startPad 7)
sym_block pad8 := exec b76 (startPad 8)
sym_block pad9 := exec b76 (startPad 9)
sym_block pad10 := exec b76 (startPad 10)
sym_block pad11 := exec b76 (startPad 11)
sym_block pad12 := exec b76 (startPad 12)
sym_block pad13 := exec b76 (startPad 13)
sym_block pad14 := exec b76 (startPad 14)
sym_block pad15 := exec b76 (startPad 15)
sym_block pad16 := exec b76 (startPad 16)

end NativeRustcVmArm.WordsHash
