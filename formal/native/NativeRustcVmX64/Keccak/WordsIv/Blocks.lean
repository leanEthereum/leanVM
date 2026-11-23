module

public import NativeRustcX64.Sym
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfFiatShamirIv
public meta import NativeRustcVmX64.Code.Vm.Keccak256WordsOfFiatShamirIv
public meta import NativeRustcX64.Sym

/-!
# `keccak256_words::<fiat_shamir_iv's closure>`'s blocks, run by the symbolic executor (x86-64)

The blocks of `NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv` the function runs, each from a
symbolic state whose region 0 is the 296-byte frame (`WordsHash.frame`), RSP at its offset 8 but at
the entry (offset 288). Every lane `j` of a block has a call block (`call j`: `iv_word` of the
word index in RDX, R12 the bytecode, R15 its word count) and an XOR block (`xor j`: RAX into lane
`j`, RDX the next index, the branch on it), or a zero block (`zero j`). The whole blocks' zero
blocks are never reached: a whole block's words are below the count.

- `entry` (`b0`): the registers pushed, `out` saved at 32, `memset` called on the lanes; `setup`
  (`b1`): `nb` at 16, `len` at 24, the branch on `136 ≤ len`;
- the whole blocks: `fullInit` (`b21`), the head `fullHead` (`b26`), lane `j`'s call (`fullC j`)
  and XOR (`fullX j`), lane 16's XOR and the call of `keccak_f` (`fullKf`, `b24`), the next block
  (`fullNext`, `b25`);
- the last block: its head `tailHead` (`b2`), lane `j`'s call (`tailC j`), XOR (`tailX j`), zero
  (`tailZ j`; lane 15's add 16 to RBX), lane 16's zero `tailZ16` (`b20`); the padding: `padA`
  (`b110`'s first 15 directives: lane 16's XOR, the padding word and the padded lane's offset),
  `padB t` (the padding word's XOR into lane `t`, an alias at the frame's byte `8 + 8 t` plus 32)
  and `padC` (`0x80` into byte 135, the call of `keccak_f`);
- the epilogue `epi` (`b111`): the digest into region 1, the 32 bytes at `out` (the slot at 32).
-/

namespace NativeRustcVmX64.WordsIv

open NativeRustcX64 NativeRustcX64.Sym Vm.Keccak256WordsOfFiatShamirIv

set_option Elab.async false

@[expose] public section

/-- The entry's start: RSP at the frame's offset 288. -/
def startEntry : SState :=
  (init [296, 8] [(.rsp, .ptr 0 288)] [] []
    [(.gotSlot "memset", 1, 0)]).withKnownBytes 1 0 8 (.label "memset")

/-- A start in the body: RSP at the frame's offset 8. -/
def startMain : SState := init [296] [(.rsp, .ptr 0 8)]

/-- The padding at lane `t`: the padded lane's address an alias of the frame's byte `8 + 8 t`. -/
def startPad (t : Nat) : SState :=
  init [296] [(.rsp, .ptr 0 8)] [] [] [(.bin .add .W64 (.ptr 0 8) (.reg .rdx), 0, 8 + 8 * t)]

/-- The epilogue's: region 1 the digest, at the slot at 32. -/
def startEpi : SState := init [296, 32] [(.rsp, .ptr 0 8)] [] [] [(.load 0 32 8, 1, 0)]

/-- `b110`'s first part: lane 16's XOR and the padding's word and offset. -/
def padACode : List Directive := b110.take 15

/-- `b110`'s second part: the padding word's XOR into the padded lane. -/
def padBCode : List Directive := (b110.drop 15).take 1

/-- `b110`'s third part: `PAD_LAST`'s XOR into byte 135 and the call of `keccak_f`. -/
def padCCode : List Directive := b110.drop 16

end

sym_block entry := exec b0 startEntry
sym_block setup := exec b1 startMain
sym_block fullInit := exec b21 startMain
sym_block fullHead := exec b26 startMain
sym_block fullKf := exec b24 startMain
sym_block fullNext := exec b25 startMain
sym_block tailHead := exec b2 startMain
sym_block tailZ16 := exec b20 startMain
sym_block padA := exec padACode startMain
sym_block padC := exec padCCode startMain
sym_block epi := exec b111 startEpi

sym_block fullC0 := exec b27 startMain
sym_block fullC1 := exec b47 startMain
sym_block fullC2 := exec b49 startMain
sym_block fullC3 := exec b51 startMain
sym_block fullC4 := exec b53 startMain
sym_block fullC5 := exec b55 startMain
sym_block fullC6 := exec b57 startMain
sym_block fullC7 := exec b59 startMain
sym_block fullC8 := exec b61 startMain
sym_block fullC9 := exec b63 startMain
sym_block fullC10 := exec b65 startMain
sym_block fullC11 := exec b67 startMain
sym_block fullC12 := exec b69 startMain
sym_block fullC13 := exec b71 startMain
sym_block fullC14 := exec b73 startMain
sym_block fullC15 := exec b75 startMain
sym_block fullC16 := exec b23 startMain
sym_block fullX0 := exec b28 startMain
sym_block fullX1 := exec b48 startMain
sym_block fullX2 := exec b50 startMain
sym_block fullX3 := exec b52 startMain
sym_block fullX4 := exec b54 startMain
sym_block fullX5 := exec b56 startMain
sym_block fullX6 := exec b58 startMain
sym_block fullX7 := exec b60 startMain
sym_block fullX8 := exec b62 startMain
sym_block fullX9 := exec b64 startMain
sym_block fullX10 := exec b66 startMain
sym_block fullX11 := exec b68 startMain
sym_block fullX12 := exec b70 startMain
sym_block fullX13 := exec b72 startMain
sym_block fullX14 := exec b74 startMain
sym_block fullX15 := exec b76 startMain
sym_block tailC0 := exec b3 startMain
sym_block tailC1 := exec b79 startMain
sym_block tailC2 := exec b81 startMain
sym_block tailC3 := exec b83 startMain
sym_block tailC4 := exec b85 startMain
sym_block tailC5 := exec b87 startMain
sym_block tailC6 := exec b89 startMain
sym_block tailC7 := exec b91 startMain
sym_block tailC8 := exec b93 startMain
sym_block tailC9 := exec b95 startMain
sym_block tailC10 := exec b97 startMain
sym_block tailC11 := exec b99 startMain
sym_block tailC12 := exec b101 startMain
sym_block tailC13 := exec b103 startMain
sym_block tailC14 := exec b105 startMain
sym_block tailC15 := exec b107 startMain
sym_block tailC16 := exec b109 startMain
sym_block tailX0 := exec b4 startMain
sym_block tailX1 := exec b80 startMain
sym_block tailX2 := exec b82 startMain
sym_block tailX3 := exec b84 startMain
sym_block tailX4 := exec b86 startMain
sym_block tailX5 := exec b88 startMain
sym_block tailX6 := exec b90 startMain
sym_block tailX7 := exec b92 startMain
sym_block tailX8 := exec b94 startMain
sym_block tailX9 := exec b96 startMain
sym_block tailX10 := exec b98 startMain
sym_block tailX11 := exec b100 startMain
sym_block tailX12 := exec b102 startMain
sym_block tailX13 := exec b104 startMain
sym_block tailX14 := exec b106 startMain
sym_block tailX15 := exec b108 startMain
sym_block tailZ0 := exec b78 startMain
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

end NativeRustcVmX64.WordsIv
