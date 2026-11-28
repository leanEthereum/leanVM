module

public import NativeRustcX64.Sym
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfHashWords
public meta import NativeRustcVmX64.Code.Vm.Keccak256WordsOfHashWords
public meta import NativeRustcX64.Sym

/-!
# `keccak256_words::<hash_words's closure>`'s blocks, run by the symbolic executor (x86-64)

The blocks of `NativeRustcVmX64.Vm.Keccak256WordsOfHashWords` the function runs, each from a
symbolic state whose region 0 is the 296-byte frame (`WordsHash.frame`), RSP at its offset 8 but
at the entry (offset 288). The whole blocks' unloaded lanes (`b12` to `b27`, `b29`, `b45`) are
never reached: a whole block's words are in the slice.

- `entry` (`b0`): the registers pushed, `out` saved at 32, `memset` called on the lanes; `setup`
  (`b1`): `len · 0xF0F0F0F0F0F0F0F1`'s high word `M` at 16, `nb = M >> 7` at 24, the bound
  `min(count, n)` in R12, the branch on `136 ≤ len`;
- the whole blocks: `fullInit` (`b5`), the head `fullHead` (`b10`), lane `j` (`fullL j`: `b11`,
  `b30` to `b44`; region 1 the block's 17 words, at R15 plus RBX words), lane 16's word
  (`full16`, `b7`), its XOR and the call of `keccak_f` (`fullXor`, `b8`), the next block
  (`fullNext`, `b9`);
- the last block: its head `tailHead` (`b2`); lane `j` loaded (`tailL j`; region 1 the words from
  R15 plus RAX words to lane `j`'s) or zero (`tailZ j`); lanes 1, 13 to 16 load their word into a
  register in one block and XOR it in another (`tailX j`); the padding: `padA` (`b82`'s first 6
  directives: lane 16's XOR, the padding word and the padded lane's offset), `padB t` (the next:
  the padding word's XOR, the padded lane `t` an alias at the frame's byte `8 + 8 t` plus 32) and
  `padC` (the rest: `0x80` into byte 135, the call of `keccak_f`);
- the epilogue `epi` (`b83`): the digest into region 1, the 32 bytes at `out` (the slot at 32).
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym Vm.Keccak256WordsOfHashWords

set_option Elab.async false

@[expose] public section

/-- The entry's start: RSP at the frame's offset 288. -/
def startEntry : SState :=
  (init [296, 8] [(.rsp, .ptr 0 288)] [] []
    [(.gotSlot "memset", 1, 0)]).withKnownBytes 1 0 8 (.label "memset")

/-- A start in the body: RSP at the frame's offset 8. -/
def startMain : SState := init [296] [(.rsp, .ptr 0 8)]

/-- The address of word `x` of the slice at R15. -/
def addrW (x : Reg64) : Sym := .bin .add .W64 (.reg .r15) (.bin .mul .W64 (.reg x) (.lit 8))

/-- A loaded lane: region 1 the `n` bytes from word `x` of the slice. -/
def startL (x : Reg64) (n : Nat) : SState :=
  init [296, n] [(.rsp, .ptr 0 8)] [] [] [(addrW x, 1, 0)]

/-- The padding at lane `t`: the padded lane's address an alias of the frame's byte `8 + 8 t`. -/
def startPad (t : Nat) : SState :=
  init [296] [(.rsp, .ptr 0 8)] [] [] [(.bin .add .W64 (.ptr 0 8) (.reg .r14), 0, 8 + 8 * t)]

/-- The epilogue's: region 1 the digest, at the slot at 32. -/
def startEpi : SState := init [296, 32] [(.rsp, .ptr 0 8)] [] [] [(.load 0 32 8, 1, 0)]

/-- `b82`'s first part: lane 16's XOR and the padding's word and offset. -/
def padACode : List Directive := b82.take 6

/-- `b82`'s second part: the padding word's XOR into the padded lane. -/
def padBCode : List Directive := (b82.drop 6).take 1

/-- `b82`'s third part: `PAD_LAST`'s XOR into byte 135 and the call of `keccak_f`. -/
def padCCode : List Directive := b82.drop 7

end

sym_block entry := exec b0 startEntry
sym_block setup := exec b1 startMain
sym_block fullInit := exec b5 startMain
sym_block fullHead := exec b10 startMain
sym_block full16 := exec b7 (startL .rbx 136)
sym_block fullXor := exec b8 startMain
sym_block fullNext := exec b9 startMain
sym_block tailHead := exec b2 startMain
sym_block padA := exec padACode startMain
sym_block padC := exec padCCode startMain
sym_block epi := exec b83 startEpi

sym_block fullL0 := exec b11 (startL .rbx 136)
sym_block fullL1 := exec b30 (startL .rbx 136)
sym_block fullL2 := exec b31 (startL .rbx 136)
sym_block fullL3 := exec b32 (startL .rbx 136)
sym_block fullL4 := exec b33 (startL .rbx 136)
sym_block fullL5 := exec b34 (startL .rbx 136)
sym_block fullL6 := exec b35 (startL .rbx 136)
sym_block fullL7 := exec b36 (startL .rbx 136)
sym_block fullL8 := exec b37 (startL .rbx 136)
sym_block fullL9 := exec b38 (startL .rbx 136)
sym_block fullL10 := exec b39 (startL .rbx 136)
sym_block fullL11 := exec b40 (startL .rbx 136)
sym_block fullL12 := exec b41 (startL .rbx 136)
sym_block fullL13 := exec b42 (startL .rbx 136)
sym_block fullL14 := exec b43 (startL .rbx 136)
sym_block fullL15 := exec b44 (startL .rbx 136)
sym_block tailL0 := exec b3 (startL .rax 8)
sym_block tailZ0 := exec b46 startMain
sym_block tailL1 := exec b47 (startL .rax 16)
sym_block tailZ1 := exec b4 startMain
sym_block tailL2 := exec b49 (startL .rax 24)
sym_block tailZ2 := exec b61 startMain
sym_block tailL3 := exec b62 (startL .rax 32)
sym_block tailZ3 := exec b50 startMain
sym_block tailL4 := exec b63 (startL .rax 40)
sym_block tailZ4 := exec b51 startMain
sym_block tailL5 := exec b64 (startL .rax 48)
sym_block tailZ5 := exec b52 startMain
sym_block tailL6 := exec b65 (startL .rax 56)
sym_block tailZ6 := exec b53 startMain
sym_block tailL7 := exec b66 (startL .rax 64)
sym_block tailZ7 := exec b54 startMain
sym_block tailL8 := exec b67 (startL .rax 72)
sym_block tailZ8 := exec b55 startMain
sym_block tailL9 := exec b68 (startL .rax 80)
sym_block tailZ9 := exec b56 startMain
sym_block tailL10 := exec b69 (startL .rax 88)
sym_block tailZ10 := exec b57 startMain
sym_block tailL11 := exec b70 (startL .rax 96)
sym_block tailZ11 := exec b58 startMain
sym_block tailL12 := exec b71 (startL .rax 104)
sym_block tailZ12 := exec b59 startMain
sym_block tailL13 := exec b72 (startL .rax 112)
sym_block tailZ13 := exec b60 startMain
sym_block tailL14 := exec b74 (startL .rax 120)
sym_block tailZ14 := exec b75 startMain
sym_block tailL15 := exec b77 (startL .rax 128)
sym_block tailZ15 := exec b78 startMain
sym_block tailL16 := exec b80 (startL .rax 136)
sym_block tailZ16 := exec b81 startMain
sym_block tailX1 := exec b48 startMain
sym_block tailX13 := exec b73 startMain
sym_block tailX14 := exec b76 startMain
sym_block tailX15 := exec b79 startMain
sym_block padB0 := exec padBCode (startPad 0)
sym_block padB1 := exec padBCode (startPad 1)
sym_block padB2 := exec padBCode (startPad 2)
sym_block padB3 := exec padBCode (startPad 3)
sym_block padB4 := exec padBCode (startPad 4)
sym_block padB5 := exec padBCode (startPad 5)
sym_block padB6 := exec padBCode (startPad 6)
sym_block padB7 := exec padBCode (startPad 7)
sym_block padB8 := exec padBCode (startPad 8)
sym_block padB9 := exec padBCode (startPad 9)
sym_block padB10 := exec padBCode (startPad 10)
sym_block padB11 := exec padBCode (startPad 11)
sym_block padB12 := exec padBCode (startPad 12)
sym_block padB13 := exec padBCode (startPad 13)
sym_block padB14 := exec padBCode (startPad 14)
sym_block padB15 := exec padBCode (startPad 15)
sym_block padB16 := exec padBCode (startPad 16)

end NativeRustcVmX64.WordsHash
