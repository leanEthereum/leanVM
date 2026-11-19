module

public import X86.Keccak
public import X86.Context

/-!
# leanXMSS verification in the x86 subset

`body` verifies the signature in the input area of `X86.Context` (the words of
`XmssVerifier.encode`) and leaves `1` in `rax` if it verifies, `0` if not. It saves the callee-saved
registers first and restores them last, and never fails.

Each layer hashes its message, walks its 58 chains, hashes the chain ends into the leaf and folds
the path to the root. Every hash input is `P || address || payload` in words: `P` and the address
two words each (the address `lo | hi << 32 | (type + 32 step) << 56`, then `0`), the payload's
digests two words each. Chain steps, nodes and messages are hashed from the buffer `bufA`, the leaf
from `bufL`, which collects the chain ends. The checks accumulate in `r12`, zero while every one
passes: the last six digits of each message digest, the digit sum `106`, the root.

Registers across the layers: `r15` the layer, `r14` the address of its signature, `r13` its key
index, `r12` the checks; in a layer `r11` the chain (or level), `r10` the chain's position, `r9`
the digit sum (or the key shifted to the level), `rbp` the digest shifted to the chain's digit.
`Keccak.hash` writes only `rax`, `rbx`, `rcx`, `rdx`, `rsi`, `r8`.
-/

@[expose] public section

namespace X86.XmssVerifier

open Context

/-- The byte displacement of word `k`. -/
def wdisp (k : Nat) : Int64 := Int64.ofNat (8 * k)

/-- Word `k` of the context. -/
abbrev ctx (k : Nat) : Addr := at_ .rdi (wdisp k)

/-! ## Word indices in the context -/

/-- The input area's first word. -/
def inputW : Nat := inputOff / 8
/-- The public key's root, two words. -/
def rootW : Nat := inputW
/-- The public parameter `P`, two words. -/
def paramW : Nat := inputW + 2
/-- The message, four words. -/
def msgW : Nat := inputW + 4
/-- The leaf index. -/
def idxW : Nat := inputW + 8
/-- The bottom layer's signature; the top layer's follows after `sigStride`. -/
def sigW : Nat := inputW + 9
/-- The words of a layer's signature (`XmssVerifier.layerWords`). -/
def sigStride : Nat := 150
/-- The buffer of chain steps, nodes and message digests: `P`, the address, `0`, six payload
words. -/
def bufA : Nat := workOff / 8
/-- The message digest's high word, read again at chain 32. -/
def dhiW : Nat := bufA + 10
/-- The leaf's buffer: `P`, the address, `0`, the 58 chain ends. -/
def bufL : Nat := bufA + 16

/-- The address of word `k` past `rdi + 8 rax`. -/
def ctxAt (k : Nat) : Addr := { base := .rdi, idx := some (.rax, .W8), disp := wdisp k }

/-- The address of word `k` of the layer's signature past `r14 + 8 rax`. -/
def sigAt (k : Nat) : Addr := { base := .r14, idx := some (.rax, .W8), disp := wdisp k }

/-! ## The code -/

/-- Save the callee-saved registers. -/
def save : Stmt := blk [
  I (.store (at_ .rdi saveOff) .rbx), I (.store (at_ .rdi (saveOff + 8)) .rbp),
  I (.store (at_ .rdi (saveOff + 16)) .r12), I (.store (at_ .rdi (saveOff + 24)) .r13),
  I (.store (at_ .rdi (saveOff + 32)) .r14), I (.store (at_ .rdi (saveOff + 40)) .r15)]

/-- Restore the callee-saved registers. -/
def restore : Stmt := blk [
  I (.load .rbx (at_ .rdi saveOff)), I (.load .rbp (at_ .rdi (saveOff + 8))),
  I (.load .r12 (at_ .rdi (saveOff + 16))), I (.load .r13 (at_ .rdi (saveOff + 24))),
  I (.load .r14 (at_ .rdi (saveOff + 32))), I (.load .r15 (at_ .rdi (saveOff + 40)))]

/-- `P` and the zero word into both buffers; the bottom layer's registers. -/
def init : Stmt := blk [
  I (.load .rax (ctx paramW)), I (.store (ctx bufA) .rax), I (.store (ctx bufL) .rax),
  I (.load .rax (ctx (paramW + 1))), I (.store (ctx (bufA + 1)) .rax),
  I (.store (ctx (bufL + 1)) .rax),
  I (.storei (ctx (bufA + 3)) 0), I (.storei (ctx (bufL + 3)) 0),
  I (.movi .r15 0), I (.movi .r12 0), I (.load .r13 (ctx idxW)), I (.lea .r14 (ctx sigW))]

/-- `rax := (layer << 55) | key | (rdx << 56)`: an address with the type byte in `rdx`. -/
def tweakWord : List Stmt :=
  [I (.mov .rax .r15), I (.shli .rax 55), I (.or .rax .r13), I (.shli .rdx 56), I (.or .rax .rdx)]

/-- The bottom layer's message payload: the message, the randomizer; `80` bytes. -/
def msgBottom : Stmt := blk [
  I (.load .rax (ctx msgW)), I (.store (ctx (bufA + 4)) .rax),
  I (.load .rax (ctx (msgW + 1))), I (.store (ctx (bufA + 5)) .rax),
  I (.load .rax (ctx (msgW + 2))), I (.store (ctx (bufA + 6)) .rax),
  I (.load .rax (ctx (msgW + 3))), I (.store (ctx (bufA + 7)) .rax),
  I (.load .rax (at_ .r14 0)), I (.store (ctx (bufA + 8)) .rax),
  I (.load .rax (at_ .r14 8)), I (.store (ctx (bufA + 9)) .rax),
  I (.movi .rbx 80)]

/-- The top layer's message payload: the bottom root, already in the buffer, the randomizer; `64`
bytes. -/
def msgTop : Stmt := blk [
  I (.load .rax (at_ .r14 0)), I (.store (ctx (bufA + 6)) .rax),
  I (.load .rax (at_ .r14 8)), I (.store (ctx (bufA + 7)) .rax),
  I (.movi .rbx 64)]

/-- The message digest: `rbp` its low word, `dhiW` its high word; its last six digits into the
checks. -/
def message : Stmt := blk ([I (.movi .rdx 12)] ++ tweakWord ++ [
  I (.store (ctx (bufA + 2)) .rax),
  .ite (.cmp .eq .r15 (.imm 0)) msgBottom msgTop,
  I (.lea .rsi (ctx bufA)), Keccak.hash,
  I (.load .rbp (ctx 0)), I (.load .rax (ctx 1)), I (.store (ctx dhiW) .rax),
  I (.shri .rax 52), I (.or .r12 .rax)])

/-- One step of chain `r11` from position `r10`. -/
def chainStep : Stmt := blk ([I (.mov .rdx .r10), I (.shli .rdx 5), I (.addi .rdx 1)] ++
  tweakWord ++ [
  I (.store (ctx (bufA + 2)) .rax),
  I (.lea .rsi (ctx bufA)), I (.movi .rbx 64), Keccak.hash,
  I (.load .rax (ctx 0)), I (.store (ctx (bufA + 4)) .rax),
  I (.load .rax (ctx 1)), I (.store (ctx (bufA + 5)) .rax),
  I (.addi .r10 1)])

/-- Chain `r11`: its digit from `rbp` into the sum, its value walked to the end, the end into the
leaf's buffer. -/
def chain : Stmt := blk [
  .ite (.cmp .eq .r11 (.imm 32)) (I (.load .rbp (ctx dhiW))) .skip,
  I (.mov .r10 .rbp), I (.andi .r10 3), I (.add .r9 .r10), I (.shri .rbp 2),
  I (.mov .rax .r11), I (.shli .rax 4),
  I (.load .rdx (sigAt 2)), I (.store (ctx (bufA + 4)) .rdx),
  I (.load .rdx (sigAt 3)), I (.store (ctx (bufA + 5)) .rdx),
  I (.store (ctx (bufA + 6)) .r11), I (.storei (ctx (bufA + 7)) 0),
  .loop (.cmp .ltu .r10 (.imm 3)) chainStep,
  I (.mov .rax .r11), I (.shli .rax 4),
  I (.load .rdx (ctx (bufA + 4))), I (.store (ctxAt (bufL + 4)) .rdx),
  I (.load .rdx (ctx (bufA + 5))), I (.store (ctxAt (bufL + 5)) .rdx),
  I (.addi .r11 1)]

/-- The 58 chains, then the digit sum into the checks. -/
def chains : Stmt := blk [
  I (.movi .r11 0), I (.movi .r9 0),
  .loop (.cmp .ltu .r11 (.imm 58)) chain,
  I (.xori .r9 106), I (.or .r12 .r9)]

/-- The leaf: the hash of the chain ends. -/
def leaf : Stmt := blk ([I (.movi .rdx 2)] ++ tweakWord ++ [
  I (.store (ctx (bufL + 2)) .rax),
  I (.lea .rsi (ctx bufL)), I (.movi .rbx 960), Keccak.hash])

/-- The node above level `r11`: the current node, in scratch words `0` and `1`, and its sibling in
the order of bit `0` of `r9`, the key shifted to the level. -/
def node : Stmt := blk [
  I (.mov .rax .r11), I (.shli .rax 4),
  I (.load .rcx (sigAt 118)), I (.load .rdx (sigAt 119)),
  I (.load .rax (ctx 0)), I (.load .r8 (ctx 1)),
  .ite (.test true .r9 (.imm 1))
    (blk [I (.store (ctx (bufA + 4)) .rax), I (.store (ctx (bufA + 5)) .r8),
      I (.store (ctx (bufA + 6)) .rcx), I (.store (ctx (bufA + 7)) .rdx)])
    (blk [I (.store (ctx (bufA + 4)) .rcx), I (.store (ctx (bufA + 5)) .rdx),
      I (.store (ctx (bufA + 6)) .rax), I (.store (ctx (bufA + 7)) .r8)]),
  I (.shri .r9 1), I (.addi .r11 1),
  I (.mov .rax .r15), I (.shli .rax 23), I (.add .rax .r11), I (.shli .rax 32), I (.or .rax .r9),
  I (.movi .rdx 3), I (.shli .rdx 56), I (.or .rax .rdx),
  I (.store (ctx (bufA + 2)) .rax),
  I (.lea .rsi (ctx bufA)), I (.movi .rbx 64), Keccak.hash]

/-- Fold the path: the root in scratch words `0` and `1`. -/
def fold : Stmt := blk [
  I (.movi .r11 0), I (.mov .r9 .r13),
  .loop (.cmp .ltu .r11 (.imm 16)) node]

/-- Layer `r15`: its root into the buffer's payload, which is the next layer's message; the next
layer's registers. -/
def layer : Stmt := blk [
  message, chains, leaf, fold,
  I (.load .rax (ctx 0)), I (.store (ctx (bufA + 4)) .rax),
  I (.load .rax (ctx 1)), I (.store (ctx (bufA + 5)) .rax),
  I (.shri .r13 16), I (.addi .r14 (wdisp sigStride)), I (.addi .r15 1)]

/-- The top root against the public key's, then `rax`: `1` when every check passed. -/
def final : Stmt := blk [
  I (.load .rax (ctx (bufA + 4))), I (.load .rdx (ctx rootW)), I (.xor .rax .rdx),
  I (.or .r12 .rax),
  I (.load .rax (ctx (bufA + 5))), I (.load .rdx (ctx (rootW + 1))), I (.xor .rax .rdx),
  I (.or .r12 .rax),
  I (.movi .rax 0),
  .ite (.cmp .eq .r12 (.imm 0)) (I (.movi .rax 1)) .skip]

/-- **leanXMSS verification**: `rax` is `1` if the signature verifies, `0` if not. -/
def body : Stmt := blk [
  save, init,
  .loop (.cmp .ltu .r15 (.imm 2)) layer,
  final, restore]

/-- The failure handler: `body` never fails. -/
def onFail : Stmt := .skip

end X86.XmssVerifier
