module

public import Native.Keccak
public import Native.Context

/-!
# leanSPHINCS verification on the QM machine

`body` verifies the signature in the input area (`Native.SphincsVerifier.encode`'s words) and leaves
`1` in `rax` when it verifies, `0` when it does not; it saves and restores the callee-saved
registers. Every hash input is built as words in the working area and hashed by `Keccak.hash`:
`PK.seed` (two words), the address (four words, `adrs`), then the payload.

The working area, as word indices from `rdi`:

| words | hold |
|---|---|
| `mdBuf .. +11` | `R ‖ PK.seed ‖ PK.root ‖ M ‖ BE_32(i)`, a digest call's input |
| `dgst .. +8` | the two digest calls' outputs, four lanes each |
| `forsLeaves .. +24` | the digest's FORS leaves |
| `adrsRec .. +8` | the address as eight 32-bit fields: layer, `0`, `0`, tree, type, key pair, chain or height, hash or index |
| `msg .. +2` | the digest the next one-time key signs |
| `val .. +2` | the current chain value or path node |
| `digits .. +64` | a codeword's digits |
| `smallBuf .. +10` | a chain step's, FORS leaf's, node's or encoding's input |
| `bigBuf .. +134` | a one-time key's leaf input (64 chain ends), or the FORS roots' (24 roots) |
-/

@[expose] public section

namespace Native.SphincsVerifier

/-! ## The context's words, as indices from `rdi` -/

/-- The input's first word. -/
def inp : Nat := 128
/-- A digest call's input. -/
def mdBuf : Nat := 1152
/-- The digest calls' outputs. -/
def dgst : Nat := 1168
/-- The FORS leaves. -/
def forsLeaves : Nat := 1176
/-- The address's fields. -/
def adrsRec : Nat := 1200
/-- The digest the next one-time key signs. -/
def msg : Nat := 1208
/-- The current value. -/
def val : Nat := 1210
/-- The digits of a codeword. -/
def digits : Nat := 1216
/-- The small hash buffer. -/
def smallBuf : Nat := 1280
/-- The big hash buffer. -/
def bigBuf : Nat := 1296

/-- The context word `k`. -/
def cw (k : Nat) : Addr := at_ .rdi (8 * k).toInt64

/-- The context word `k + r`, for a register `r`. -/
def cwi (r : Reg64) (k : Nat) : Addr := { base := .rdi, idx := some (r, .W64), disp := (8 * k).toInt64 }

/-! ## Gadgets -/

/-- Copy a word. Uses `rax`. -/
def mv (src dst : Addr) : Stmt := blk [I (.load .rax src), I (.store dst .rax)]

/-- Copy the two words of a digest. Uses `rax`. -/
def mv2 (src dst : Nat) : Stmt := blk [mv (cw src) (cw dst), mv (cw (src + 1)) (cw (dst + 1))]

/-- `rax := ` the big-endian bytes of its low 32 bits, as a little-endian word. Uses `rcx`, `rdx`. -/
def be32 : Stmt := blk [
  I (.mov .rdx .rax), I (.andi .rdx 0xff), I (.shli .rdx 24),
  I (.mov .rcx .rax), I (.shri .rcx 8), I (.andi .rcx 0xff), I (.shli .rcx 16), I (.or .rdx .rcx),
  I (.mov .rcx .rax), I (.shri .rcx 16), I (.andi .rcx 0xff), I (.shli .rcx 8), I (.or .rdx .rcx),
  I (.mov .rcx .rax), I (.shri .rcx 24), I (.andi .rcx 0xff), I (.or .rdx .rcx),
  I (.mov .rax .rdx)]

/-- Address word `j` of the buffer at `buf`: fields `2 j` and `2 j + 1`, big-endian. Uses `rax`,
`rcx`, `rdx`, `r8`. -/
def adrsWord (buf j : Nat) : Stmt := blk [
  I (.load .rax (cw (adrsRec + 2 * j + 1))), be32, I (.shli .rax 32), I (.mov .r8 .rax),
  I (.load .rax (cw (adrsRec + 2 * j))), be32, I (.or .rax .r8),
  I (.store (cw (buf + 2 + j)) .rax)]

/-- The address's four words, after `PK.seed`, in the buffer at `buf`. -/
def adrs (buf : Nat) : Stmt := blk ((List.range 4).map (adrsWord buf))

/-- Hash the `len` bytes of the buffer at `buf`. -/
def hashAt (buf len : Nat) : Stmt :=
  blk [I (.lea .rsi (cw buf)), I (.movi .rbx len.toInt64), Keccak.hash]

/-- `Trunc_16(H(PK.seed ‖ ADRS ‖ payload))` of the buffer at `buf`, into `dst`. -/
def tweak (buf len dst : Nat) : Stmt := blk [adrs buf, hashAt buf len, mv2 0 dst]

/-- Set an address field. -/
def setField (j : Nat) (k : Int64) : Stmt := I (.storei (cw (adrsRec + j)) k)

/-! ## The message digest -/

/-- `R ‖ PK.seed ‖ PK.root ‖ M`, the digest calls' common words. -/
def digestInput : Stmt := blk <|
  (List.range 10).map fun i ↦ mv (cw (inp + (i + 8) % 10)) (cw (mdBuf + i))

/-- The two digest calls, `rbp` the call: their lanes at `dgst`. -/
def digestCalls : Stmt := blk [
  I (.movi .rbp 0),
  .loop (.cmp .ltu .rbp (.imm 2)) (blk [
    I (.mov .rax .rbp), I (.shli .rax 24), I (.store (cw (mdBuf + 10)) .rax),
    hashAt mdBuf 84,
    I (.mov .r9 .rbp), I (.shli .r9 2),
    blk ((List.range 4).map fun k ↦ mv (cw k) (cwi .r9 (dgst + k))),
    I (.addi .rbp 1)])]

/-- Byte `j` of the digest into `d`. -/
def digestByte (d : Reg64) (j : Nat) : Stmt :=
  blk [I (.load d (cw (dgst + j / 8))), I (.shri d (8 * (j % 8))), I (.andi d 0xff)]

/-- The index `idx` into `r15`: bytes `30 .. 32` big-endian, cut to 18 bits, then byte `33`. -/
def readIndex : Stmt := blk [
  digestByte .rax 30, I (.shli .rax 16),
  digestByte .rcx 31, I (.shli .rcx 8), I (.add .rax .rcx),
  digestByte .rcx 32, I (.add .rax .rcx),
  I (.andi .rax 0x3ffff), I (.shli .rax 8),
  digestByte .rcx 33, I (.add .rax .rcx),
  I (.mov .r15 .rax)]

/-- FORS tree `κ`'s leaf: the 10 bits from bit `10 κ`, each byte's most significant bit first. -/
def forsLeaf (κ : Nat) : Stmt := blk [
  digestByte .rax (10 * κ / 8), I (.shli .rax 8),
  digestByte .rcx (10 * κ / 8 + 1), I (.add .rax .rcx),
  I (.shri .rax (6 - 10 * κ % 8)), I (.andi .rax 1023),
  I (.store (cw (forsLeaves + κ)) .rax)]

/-! ## FORS -/

/-- A path node: the current value and the sibling at `cwi .rcx sib`, in index order by bit `0`
of `r14`. -/
def pathNode (sib : Nat) : Stmt :=
  .ite (.test true .r14 (.imm 1))
    (blk [mv2 val (smallBuf + 6), mv (cwi .rcx sib) (cw (smallBuf + 8)),
      mv (cwi .rcx (sib + 1)) (cw (smallBuf + 9))])
    (blk [mv (cwi .rcx sib) (cw (smallBuf + 6)), mv (cwi .rcx (sib + 1)) (cw (smallBuf + 7)),
      mv2 val (smallBuf + 8)])

/-- One FORS tree, `r12 = κ`, `r13 = 22 κ`: the leaf hashed, the path folded, its root into the
roots' input. Uses `r9` (`κ 2^(10 - z)`), `r10` (the level `z`), `r14` (the leaf index `>> z`). -/
def forsTree : Stmt := blk [
  setField 4 3, setField 6 0,
  I (.load .r14 (cwi .r12 forsLeaves)),
  I (.mov .rax .r12), I (.shli .rax 10), I (.add .rax .r14),
  I (.store (cw (adrsRec + 7)) .rax),
  mv (cwi .r13 (inp + 10)) (cw (smallBuf + 6)), mv (cwi .r13 (inp + 11)) (cw (smallBuf + 7)),
  tweak smallBuf 64 val,
  I (.mov .r9 .r12), I (.shli .r9 10),
  I (.movi .r10 0),
  .loop (.cmp .ltu .r10 (.imm 10)) (blk [
    I (.mov .rax .r10), I (.addi .rax 1), I (.store (cw (adrsRec + 6)) .rax),
    I (.shri .r9 1),
    I (.mov .rax .r14), I (.shri .rax 1), I (.add .rax .r9), I (.store (cw (adrsRec + 7)) .rax),
    I (.mov .rcx .r10), I (.shli .rcx 1), I (.add .rcx .r13),
    pathNode (inp + 12),
    tweak smallBuf 80 val,
    I (.shri .r14 1), I (.addi .r10 1)]),
  I (.mov .rcx .r12), I (.shli .rcx 1),
  mv (cw val) (cwi .rcx (bigBuf + 6)), mv (cw (val + 1)) (cwi .rcx (bigBuf + 7))]

/-- The FORS public key into `msg`: every tree, then `T_k` of the roots. -/
def fors : Stmt := blk [
  setField 0 0,
  I (.mov .rax .r15), I (.shri .rax 8), I (.store (cw (adrsRec + 3)) .rax),
  I (.mov .rax .r15), I (.andi .rax 255), I (.store (cw (adrsRec + 5)) .rax),
  I (.movi .r12 0), I (.movi .r13 0),
  .loop (.cmp .ltu .r12 (.imm 24)) (blk [forsTree, I (.addi .r12 1), I (.addi .r13 22)]),
  setField 4 4, setField 6 0, setField 7 0,
  tweak bigBuf 432 msg]

/-! ## The layers -/

/-- Digit `i` of the codeword in scratch words `0, 1`: bits `8 ⌊i/4⌋ + 6 - 2 (i mod 4)`, into
`digits`, added to `rbp`. -/
def digit (i : Nat) : Stmt := blk [
  I (.load .rax (cw (i / 32))), I (.shri .rax ((8 * (i / 4) + 6 - 2 * (i % 4)) % 64)),
  I (.andi .rax 3), I (.store (cw (digits + i)) .rax), I (.add .rbp .rax)]

/-- Chain `r13` of the layer's key: walked from its digit to the end, into the leaf's input. -/
def chain : Stmt := blk [
  setField 4 0, I (.store (cw (adrsRec + 6)) .r13),
  I (.mov .rcx .r13), I (.shli .rcx 1), I (.add .rcx .r11),
  mv (cwi .rcx (inp + 539)) (cw val), mv (cwi .rcx (inp + 540)) (cw (val + 1)),
  I (.load .r14 (cwi .r13 digits)),
  .loop (.cmp .ltu .r14 (.imm 3)) (blk [
    I (.store (cw (adrsRec + 7)) .r14),
    mv2 val (smallBuf + 6),
    tweak smallBuf 64 val,
    I (.addi .r14 1)]),
  I (.mov .rcx .r13), I (.shli .rcx 1),
  mv (cw val) (cwi .rcx (bigBuf + 6)), mv (cw (val + 1)) (cwi .rcx (bigBuf + 7))]

/-- The layer's tree: its leaf `r10` and path folded into `val`, `rbp` levels. -/
def foldTree : Stmt := blk [
  setField 4 2, setField 5 0,
  I (.mov .r14 .r10), I (.movi .r13 0),
  .loop (.cmp .ltu .r13 (.reg .rbp)) (blk [
    I (.mov .rax .r13), I (.addi .rax 1), I (.store (cw (adrsRec + 6)) .rax),
    I (.mov .rax .r14), I (.shri .rax 1), I (.store (cw (adrsRec + 7)) .rax),
    I (.mov .rcx .r13), I (.shli .rcx 1), I (.add .rcx .r11),
    pathNode (inp + 667),
    tweak smallBuf 80 val,
    I (.shri .r14 1), I (.addi .r13 1)])]

/-- The layer's key once the codeword is valid: the chains, the leaf, the tree. -/
def layerRest : Stmt := blk [
  I (.movi .r13 0),
  .loop (.cmp .ltu .r13 (.imm 64)) (blk [chain, I (.addi .r13 1)]),
  setField 4 1, setField 6 0, setField 7 0,
  tweak bigBuf 1072 val,
  .ite (.cmp .eq .r12 (.imm 2)) (I (.movi .rbp 10)) (I (.movi .rbp 8)),
  foldTree,
  mv2 val msg,
  I (.shri .r15 8), I (.addi .r12 1), I (.addi .r11 145)]

/-- Layer `r12`, `r11 = 145 r12` its signature's offset, `r15 = idx >> 8 r12`: its key's leaf
`r10` and tree, the encoding of `msg`, then the rest, or `r12 := 4` when the counter does not
give a codeword. -/
def layer : Stmt := blk [
  .ite (.cmp .eq .r12 (.imm 2))
    (blk [I (.mov .r10 .r15), I (.andi .r10 1023), I (.mov .r9 .r15), I (.shri .r9 10)])
    (blk [I (.mov .r10 .r15), I (.andi .r10 255), I (.mov .r9 .r15), I (.shri .r9 8)]),
  I (.store (cw adrsRec) .r12), I (.store (cw (adrsRec + 3)) .r9),
  I (.store (cw (adrsRec + 5)) .r10),
  setField 4 7, setField 6 0, setField 7 0,
  mv2 msg (smallBuf + 6),
  I (.load .rax (cwi .r11 (inp + 538))), be32, I (.store (cw (smallBuf + 8)) .rax),
  adrs smallBuf, hashAt smallBuf 68,
  I (.movi .rbp 0),
  blk ((List.range 64).map digit),
  .ite (.cmp .ne .rbp (.imm 128)) (I (.movi .r12 4)) layerRest]

/-- The hypertree, from `msg` up: `r12 = 3` when every layer's counter gave a codeword. -/
def layers : Stmt := blk [
  I (.movi .r12 0), I (.movi .r11 0),
  .loop (.cmp .ltu .r12 (.imm 3)) layer]

/-- `rax := 1` when `r12 = 3` and `msg` is `PK.root`, else `0`. -/
def result : Stmt :=
  .ite (.cmp .eq .r12 (.imm 3))
    (blk [I (.load .rax (cw msg)), I (.load .rcx (cw (inp + 2))),
      .ite (.cmp .eq .rax (.reg .rcx))
        (blk [I (.load .rax (cw (msg + 1))), I (.load .rcx (cw (inp + 3))),
          .ite (.cmp .eq .rax (.reg .rcx)) (I (.movi .rax 1)) (I (.movi .rax 0))])
        (I (.movi .rax 0))])
    (I (.movi .rax 0))

/-! ## The verifier -/

/-- The save area's first word, `Context.saveOff / 8`. -/
def saveWord : Nat := 88

/-- Save the callee-saved registers. -/
def save : Stmt := blk <| (List.range 6).map fun i ↦
  I (.store (cw (saveWord + i)) (Context.calleeSaved.getD i .rbx))

/-- Restore the callee-saved registers. -/
def restore : Stmt := blk <| (List.range 6).map fun i ↦
  I (.load (Context.calleeSaved.getD i .rbx) (cw (saveWord + i)))

/-- **leanSPHINCS verification.** -/
def body : Stmt := blk [
  save,
  mv2 inp smallBuf, mv2 inp bigBuf, setField 1 0, setField 2 0,
  digestInput, digestCalls, readIndex,
  blk ((List.range 24).map forsLeaf),
  fors,
  layers,
  result,
  restore]

/-- The failure exit: `body` has no `fail`. -/
def onFail : Stmt := .skip

end Native.SphincsVerifier
