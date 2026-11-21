module

public import Native.Keccak
public import NativeVm.Input

/-!
# The wire decoder on the QM machine

`decode` reads the proof's wire bytes (the context's words `0` and `1`, `NativeVm.Input`) and writes
the decoded proof (`Decoded`) to the area at context word `8`, or fails, as
`LeanVM.Protocol.Compile.Proof.fromBytes` decodes or refuses the bytes. It uses the working area at
context word `10` (`workWords` words) and `Keccak.hash`'s scratch at context word `32`.

The reader's position, a byte count, is `r15` throughout; a byte is read from its aligned word,
shifted left so that it is the top byte, then down (`rdByte`); a little-endian value of `n` bytes is
`n` bytes shifted in from the top (`rdLE`). Every read checks first that the bytes are there
(`needI`, `needR`), as `readBytes` does.

A phase is read as `readPhase` reads it, up to its carried siblings: the queries, the three sizes,
the distinct positions (an insertion sort, `sortQ`), the checks, the rows (`rows`). Then the leaves
are hashed (`leafHashes`) and the tree climbed level by level (`climb`), each node's sibling the
level's node beside it or else the next carried sibling read from the bytes, as the Rust reads
them; each level's nodes with their siblings are kept (`wSib`). Last, each query's opening is
looked up (`output`). A lookup is a scan for the first entry with the key (`find`).

Registers in a phase: `r14` the query count, `r13` the height, `r12` the leaf width, `r11` the row
width (then the level), `r10` the distinct positions' count. `Keccak.hash` writes only `rax`,
`rbx`, `rcx`, `rdx`, `rsi`, `r8`, and is called with `rdi` at the context's scratch.
-/

@[expose] public section

namespace NativeVm.Wire

open Native

/-- The byte displacement of word `k`. -/
def wd (k : Nat) : Int64 := Int64.ofNat (8 * k)

/-- Word `k` of the context. -/
abbrev cw (k : Nat) : Addr := at_ .rdi (wd k)

/-- Word `k` past `r`. -/
abbrev rw (r : Reg64) (k : Nat) : Addr := at_ r (wd k)

/-- Word `k` past `b + 8 i`. -/
abbrev ix (b i : Reg64) (k : Nat) : Addr := { base := b, idx := some (i, .W64), disp := wd k }

/-! ## The context's words -/

/-- The wire bytes' address. -/
def cWire : Nat := 0
/-- The wire bytes' count `L`. -/
def cLen : Nat := 1
/-- The decoded area's address. -/
def cDec : Nat := 8
/-- The decoded area's size in words. -/
def cDecN : Nat := 9
/-- The working area's address. -/
def cWork : Nat := 10
/-- The working area's size in words. -/
def cWorkN : Nat := 11
/-- `Keccak.hash`'s scratch, the digest in its first four words. -/
def cScr : Nat := 32

/-! ## The working area's words -/

/-- Phases left. -/
def wPN : Nat := 0
/-- The current phase's address in the decoded area. -/
def wPB : Nat := 1
/-- The nodes of the current level. -/
def wN : Nat := 2
/-- The parents found so far. -/
def wK : Nat := 3
/-- The current entry of the level's sibling table. -/
def wSP : Nat := 4
/-- The node of the current query at the current level. -/
def wX : Nat := 5
/-- The two digests a parent hashes. -/
def wH : Nat := 8
/-- The queries. -/
def wQ : Nat := 16
/-- The distinct positions, ascending. -/
def wP : Nat := wQ + 256
/-- Whether each node of the level has its sibling among the level's nodes. -/
def wFL : Nat := wP + 256
/-- The level's nodes: the node and its digest, five words each. -/
def wNode : Nat := wFL + 256
/-- The next level's nodes. -/
def wPar : Nat := wNode + 1280
/-- Each level's node count. -/
def wSibN : Nat := wPar + 1280
/-- Each level's nodes and their siblings, five words each, `1280` words a level. -/
def wSib : Nat := wSibN + 32
/-- The leaves at the distinct positions, `wireMaxLeafWords` words each. -/
def wLeaf : Nat := wSib + 32 * 1280
/-- The working area's words. -/
def workWords : Nat := wLeaf + 256 * 64

/-! ## Reading bytes -/

/-- `rax :=` byte `r15` of the wire, `r15 += 1`. Writes `rax`, `rcx`, `rdx`. -/
def rdByte : Stmt := blk [
  I (.load .rdx (cw cWire)), I (.mov .rax .r15), I (.shri .rax 3),
  I (.load .rax { base := .rdx, idx := some (.rax, .W64) }),
  I (.mov .rcx .r15), I (.not .rcx), I (.andi .rcx 7), I (.shli .rcx 3),
  I (.shlcl .rax), I (.shri .rax 56), I (.addi .r15 1)]

/-- Shift the next byte into `rbx` from the top. -/
def leStep : Stmt := blk [rdByte, I (.shri .rbx 8), I (.shli .rax 56), I (.add .rbx .rax)]

/-- `rbx :=` the little-endian value of the `n ≤ 8` bytes at `r15`, `r15 += n`. Writes `rax`,
`rbx`, `rcx`, `rdx`. -/
def rdLE (n : Nat) : Stmt :=
  blk ([I (.movi .rbx 0)] ++ List.replicate n leStep ++ [I (.shri .rbx (64 - 8 * n))])

/-- Fail unless `n` bytes are left. Writes `rax`. -/
def needI (n : Nat) : Stmt :=
  blk [I (.load .rax (cw cLen)), I (.sub .rax .r15), failIf (.cmp .ltu .rax (.imm n.toInt64))]

/-- Fail unless `r` bytes are left. Writes `rax`. -/
def needR (r : Reg64) : Stmt :=
  blk [I (.load .rax (cw cLen)), I (.sub .rax .r15), failIf (.cmp .ltu .rax (.reg r))]

/-- `Reader::u32` into `rbx`. -/
def getU32 : Stmt := blk [needI 4, rdLE 4]

/-! ## Tables -/

/-- The first entry of the `rdx` entries of `S` words at `rsi` whose first word is `rax`: its
index in `rcx`, `rdx` if none, its address in `r8`. Writes `rbx`, `rcx`, `rdx`, `r8`. -/
def find (S : Nat) : Stmt := blk [I (.movi .rcx 0), I (.mov .r8 .rsi),
  .loop (.cmp .ltu .rcx (.reg .rdx)) (blk [I (.load .rbx (rw .r8 0)),
    .ite (.cmp .eq .rbx (.reg .rax)) (I (.mov .rdx .rcx))
      (blk [I (.addi .rcx 1), I (.addi .r8 (wd S))])])]

/-- Copy `rdx` words from `rsi` to `rbx`. Writes `rax`, `rbx`, `rdx`, `rsi`. -/
def copyWords : Stmt :=
  .loop (.cmp .ne .rdx (.imm 0)) (blk [I (.load .rax (rw .rsi 0)), I (.store (rw .rbx 0) .rax),
    I (.addi .rsi 8), I (.addi .rbx 8), I (.subi .rdx 1)])

/-- Copy the four words from `src + 8 i` to `dst + 8 j`. Writes `rax`. -/
def copy4 (src : Reg64) (i : Nat) (dst : Reg64) (j : Nat) : Stmt := blk <|
  (List.range 4).flatMap fun l ↦ [I (.load .rax (rw src (i + l))), I (.store (rw dst (j + l)) .rax)]

/-- `Keccak.hash` of the `rbx` bytes at `rsi`, the digest at context word `cScr`. -/
def hashCall : Stmt :=
  blk [I (.lea .rdi (cw cScr)), Keccak.hash, I (.lea .rdi (at_ .rdi (-wd cScr)))]

/-- `rsi :=` the working area's node table entry `rbp`. Writes `rax`, `rsi`. -/
def nodeAddr : Stmt := blk [I (.load .rsi (cw cWork)), I (.mov .rax .rbp), I (.shli .rax 2),
  I (.add .rax .rbp), I (.lea .rsi (ix .rsi .rax wNode))]

/-- `rax :=` level `r11`'s sibling table, `rcx` holding the working area. Writes `rax`, `rdx`. -/
def sibBase : Stmt := blk [I (.mov .rax .r11), I (.shli .rax 13), I (.mov .rdx .r11),
  I (.shli .rdx 11), I (.add .rax .rdx), I (.add .rax .rcx), I (.addi .rax (wd wSib))]

/-- The sibling table's next entry. -/
def nextSP : Stmt := blk [I (.load .rcx (cw cWork)), I (.load .rax (rw .rcx wSP)),
  I (.addi .rax 40), I (.store (rw .rcx wSP) .rax)]

/-! ## The stream -/

/-- The stream's length, then its `2 n` words, into the decoded area. -/
def stream : Stmt := blk [
  getU32, I (.mov .r14 .rbx), I (.mov .r8 .rbx), I (.shli .r8 4), needR .r8,
  I (.load .r9 (cw cDec)), I (.store (rw .r9 0) .r14), I (.addi .r9 8),
  I (.mov .rbp .r14), I (.shli .rbp 1),
  .loop (.cmp .ne .rbp (.imm 0)) (blk [rdLE 8, I (.store (rw .r9 0) .rbx), I (.addi .r9 8),
    I (.subi .rbp 1)])]

/-! ## A phase -/

/-- The `r14` queries into `wQ`. -/
def readQueries : Stmt := blk [
  I (.load .r9 (cw cWork)), I (.addi .r9 (wd wQ)), I (.mov .rbp .r14),
  .loop (.cmp .ne .rbp (.imm 0)) (blk [getU32, I (.store (rw .r9 0) .rbx), I (.addi .r9 8),
    I (.subi .rbp 1)])]

/-- Insert `rax`, absent, into the `r10` ascending positions at `rsi`. -/
def insertQ : Stmt := blk [
  I (.mov .rcx .r10), I (.movi .rdx 0),
  .loop (.cmp .ne .rcx (.imm 0)) (blk [
    I (.load .rbx { base := .rsi, idx := some (.rcx, .W64), disp := -8 }),
    .ite (.cmp .ltu .rax (.reg .rbx))
      (blk [I (.store { base := .rsi, idx := some (.rcx, .W64) } .rbx), I (.subi .rcx 1)])
      (blk [I (.mov .rdx .rcx), I (.movi .rcx 0)])]),
  I (.store { base := .rsi, idx := some (.rdx, .W64) } .rax),
  I (.addi .r10 1)]

/-- The distinct positions, ascending, into `wP`; their count in `r10`. -/
def sortQ : Stmt := blk [
  I (.movi .r10 0), I (.load .r9 (cw cWork)), I (.addi .r9 (wd wQ)), I (.mov .rbp .r14),
  .loop (.cmp .ne .rbp (.imm 0)) (blk [
    I (.load .rax (rw .r9 0)),
    I (.load .rsi (cw cWork)), I (.addi .rsi (wd wP)), I (.mov .rdx .r10), find 1,
    .ite (.cmp .eq .rcx (.reg .r10)) insertQ .skip,
    I (.addi .r9 8), I (.subi .rbp 1)])]

/-- `readPhase`'s checks: the height, the leaf width, the row width, the last position. -/
def checks : Stmt := blk [
  failIf (.cmp .geu .r13 (.imm 33)), failIf (.cmp .geu .r12 (.imm 65)),
  failIf (.cmp .ltu .r12 (.reg .r11)), failIf (.cmp .eq .r10 (.imm 0)),
  I (.load .rax (cw cWork)), I (.mov .rdx .r10), I (.subi .rdx 1),
  I (.load .rbx (ix .rax .rdx wP)),
  I (.movi .rax 1), I (.mov .rcx .r13), I (.shlcl .rax), failIf (.cmp .geu .rbx (.reg .rax))]

/-- One row into the leaf at `r9`, its leading zeros first; `r8` collects its first word. -/
def row : Stmt := blk [
  I (.mov .rbx .r11), I (.shli .rbx 3), needR .rbx,
  I (.mov .rsi .r12), I (.sub .rsi .r11),
  .loop (.cmp .ne .rsi (.imm 0)) (blk [I (.storei (rw .r9 0) 0), I (.addi .r9 8),
    I (.subi .rsi 1)]),
  I (.mov .rsi .r11),
  .loop (.cmp .ne .rsi (.imm 0)) (blk [rdLE 8, I (.store (rw .r9 0) .rbx), I (.addi .r9 8),
    I (.subi .rsi 1)]),
  .ite (.cmp .ne .r11 (.imm 0))
    (blk [I (.mov .rax .r11), I (.shli .rax 3), I (.mov .rbx .r9), I (.sub .rbx .rax),
      I (.load .rbx (rw .rbx 0)), I (.or .r8 .rbx)]) .skip,
  I (.mov .rax .r12), I (.shli .rax 3), I (.neg .rax), I (.addi .rax 512), I (.add .r9 .rax)]

/-- The rows at the distinct positions into `wLeaf`, then the check that the row width is the
least. -/
def rows : Stmt := blk [
  I (.load .r9 (cw cWork)), I (.addi .r9 (wd wLeaf)), I (.mov .rbp .r10), I (.movi .r8 0),
  .loop (.cmp .ne .rbp (.imm 0)) (blk [row, I (.subi .rbp 1)]),
  .ite (.cmp .ne .r11 (.imm 0)) (failIf (.cmp .eq .r8 (.imm 0))) .skip]

/-- The level-`0` nodes: each distinct position with its leaf's digest. -/
def leafHashes : Stmt := blk [I (.movi .rbp 0),
  .loop (.cmp .ltu .rbp (.reg .r10)) (blk [
    I (.load .rsi (cw cWork)), I (.mov .rax .rbp), I (.shli .rax 6),
    I (.lea .rsi (ix .rsi .rax wLeaf)), I (.mov .rbx .r12), I (.shli .rbx 3), hashCall,
    nodeAddr, I (.load .rcx (cw cWork)), I (.load .rcx (ix .rcx .rbp wP)),
    I (.store (rw .rsi 0) .rcx), copy4 .rdi cScr .rsi 1,
    I (.addi .rbp 1)]),
  I (.load .rax (cw cWork)), I (.store (rw .rax wN) .r10)]

/-- Each node's sibling: the level's node beside it, or else the next carried sibling. -/
def pass1 : Stmt := blk [I (.movi .rbp 0), I (.load .rcx (cw cWork)), I (.load .r9 (rw .rcx wN)),
  .loop (.cmp .ltu .rbp (.reg .r9)) (blk [
    nodeAddr, I (.load .rax (rw .rsi 0)),
    I (.load .r8 (cw cWork)), I (.load .r8 (rw .r8 wSP)), I (.store (rw .r8 0) .rax),
    I (.xori .rax 1), I (.load .rsi (cw cWork)), I (.addi .rsi (wd wNode)), I (.mov .rdx .r9),
    find 5,
    .ite (.cmp .ltu .rcx (.reg .r9))
      (blk [I (.load .rsi (cw cWork)), I (.load .rsi (rw .rsi wSP)), copy4 .r8 1 .rsi 1,
        I (.load .rax (cw cWork)), I (.storei (ix .rax .rbp wFL) 1)])
      (blk [needI 32, I (.load .rsi (cw cWork)), I (.load .rsi (rw .rsi wSP)),
        rdLE 8, I (.store (rw .rsi 1) .rbx), rdLE 8, I (.store (rw .rsi 2) .rbx),
        rdLE 8, I (.store (rw .rsi 3) .rbx), rdLE 8, I (.store (rw .rsi 4) .rbx),
        I (.load .rax (cw cWork)), I (.storei (ix .rax .rbp wFL) 0)]),
    nextSP, I (.addi .rbp 1)])]

/-- The parent of the node at `rsi`, `rdx` its node, `r8` its sibling's entry, into the next
level's table. -/
def parent : Stmt := blk [
  I (.load .r8 (cw cWork)), I (.load .r8 (rw .r8 wSP)), I (.load .rcx (cw cWork)),
  .ite (.test true .rdx (.imm 1))
    (blk [copy4 .rsi 1 .rcx wH, copy4 .r8 1 .rcx (wH + 4)])
    (blk [copy4 .r8 1 .rcx wH, copy4 .rsi 1 .rcx (wH + 4)]),
  I (.shri .rdx 1), I (.load .rax (rw .rcx wK)), I (.mov .rbx .rax), I (.shli .rbx 2),
  I (.add .rbx .rax), I (.lea .rbx (ix .rcx .rbx wPar)), I (.store (rw .rbx 0) .rdx),
  I (.lea .rsi (rw .rcx wH)), I (.movi .rbx 64), hashCall,
  I (.load .rcx (cw cWork)), I (.load .rax (rw .rcx wK)), I (.mov .rbx .rax), I (.shli .rbx 2),
  I (.add .rbx .rax), I (.lea .rbx (ix .rcx .rbx wPar)), copy4 .rdi cScr .rbx 1,
  I (.load .rcx (cw cWork)), I (.load .rax (rw .rcx wK)), I (.addi .rax 1),
  I (.store (rw .rcx wK) .rax)]

/-- The parents of the first children: the even nodes and those without their sibling. -/
def pass2 : Stmt := blk [I (.movi .rbp 0), I (.load .rcx (cw cWork)),
  I (.storei (rw .rcx wK) 0), sibBase, I (.store (rw .rcx wSP) .rax),
  .loop (.cmp .ltu .rbp (.reg .r9)) (blk [
    nodeAddr, I (.load .rdx (rw .rsi 0)),
    I (.load .rcx (cw cWork)), I (.load .rax (ix .rcx .rbp wFL)),
    I (.mov .rbx .rdx), I (.andi .rbx 1), I (.and .rbx .rax),
    .ite (.test true .rbx (.reg .rbx)) parent .skip,
    nextSP, I (.addi .rbp 1)])]

/-- The parents become the level's nodes. -/
def nextLevel : Stmt := blk [
  I (.load .rcx (cw cWork)), I (.load .rdx (rw .rcx wK)), I (.store (rw .rcx wN) .rdx),
  I (.mov .rax .rdx), I (.shli .rax 2), I (.add .rdx .rax),
  I (.lea .rsi (rw .rcx wPar)), I (.lea .rbx (rw .rcx wNode)), copyWords]

/-- Level `r11`: its node count and sibling table, then its parents. -/
def level : Stmt := blk [
  I (.load .rcx (cw cWork)), I (.load .rax (rw .rcx wN)), I (.store (ix .rcx .r11 wSibN) .rax),
  sibBase, I (.store (rw .rcx wSP) .rax),
  pass1, pass2, nextLevel]

/-- The climb from the leaves, `r13` levels. -/
def climb : Stmt := blk [I (.movi .r11 0),
  .loop (.cmp .ltu .r11 (.reg .r13)) (blk [level, I (.addi .r11 1)])]

/-- Query `rbp`'s sibling at level `r11`, the query's node at the level in `wX`, into the opening
at `r9`. -/
def pathStep : Stmt := blk [
  I (.load .rcx (cw cWork)), sibBase, I (.mov .rsi .rax), I (.load .rdx (ix .rcx .r11 wSibN)),
  I (.load .rax (rw .rcx wX)), find 5,
  I (.load .rax (cw cWork)), I (.load .rdx (ix .rax .r11 wSibN)),
  I (.mov .rbx .r11), I (.shli .rbx 2), I (.lea .rbx (ix .r9 .rbx (1 + LeanVM.Protocol.Compile.wireMaxLeafWords))),
  .ite (.cmp .ltu .rcx (.reg .rdx)) (copy4 .r8 1 .rbx 0)
    (blk [I (.storei (rw .rbx 0) 0), I (.storei (rw .rbx 1) 0), I (.storei (rw .rbx 2) 0),
      I (.storei (rw .rbx 3) 0)]),
  I (.load .rcx (cw cWork)), I (.load .rax (rw .rcx wX)), I (.shri .rax 1),
  I (.store (rw .rcx wX) .rax), I (.addi .r11 1)]

/-- Each query's opening: its position, the leaf there, its path. -/
def output : Stmt := blk [
  I (.load .rcx (cw cWork)), I (.load .r9 (rw .rcx wPB)), I (.addi .r9 24), I (.movi .rbp 0),
  .loop (.cmp .ltu .rbp (.reg .r14)) (blk [
    I (.load .rcx (cw cWork)), I (.load .rax (ix .rcx .rbp wQ)),
    I (.store (rw .r9 0) .rax), I (.store (rw .rcx wX) .rax),
    I (.lea .rsi (rw .rcx wP)), I (.mov .rdx .r10), find 1,
    I (.load .rsi (cw cWork)), I (.shli .rcx 6), I (.lea .rsi (ix .rsi .rcx wLeaf)),
    I (.lea .rbx (rw .r9 1)), I (.mov .rdx .r12), copyWords,
    I (.movi .r11 0),
    .loop (.cmp .ltu .r11 (.reg .r13)) pathStep,
    I (.addi .r9 (wd openingWords)), I (.addi .rbp 1)])]

/-- The phase's three counts. -/
def header : Stmt := blk [I (.load .rcx (cw cWork)), I (.load .rax (rw .rcx wPB)),
  I (.store (rw .rax 0) .r14), I (.store (rw .rax 1) .r13), I (.store (rw .rax 2) .r12)]

/-- A phase's queries and sizes: the query count into `r14`, the queries, the height into `r13`,
the leaf width into `r12`, the row width into `r11`. -/
def phaseHead : Stmt := blk [
  getU32, failIf (.cmp .geu .rbx (.imm 257)), I (.mov .r14 .rbx),
  readQueries,
  getU32, I (.mov .r13 .rbx), getU32, I (.mov .r12 .rbx), getU32, I (.mov .r11 .rbx)]

/-- A phase's leaves: the distinct positions, the checks, the rows, the leaves' digests. -/
def phaseLeaves : Stmt := blk [sortQ, checks, rows, leafHashes]

/-- One phase, into the decoded area at `wPB`. -/
def phase : Stmt := blk [phaseHead, phaseLeaves, climb, output, header]

/-- The phase count, then the phases. -/
def phases : Stmt := blk [
  getU32, failIf (.cmp .geu .rbx (.imm 9)),
  I (.load .rax (cw cLen)), I (.shri .rax 4), I (.shli .rax 4), I (.load .rcx (cw cDec)),
  I (.add .rax .rcx), I (.store (rw .rax 1) .rbx), I (.addi .rax 16),
  I (.load .rcx (cw cWork)), I (.store (rw .rcx wPB) .rax), I (.store (rw .rcx wPN) .rbx),
  I (.mov .rbp .rbx),
  .loop (.cmp .ne .rbp (.imm 0)) (blk [phase,
    I (.load .rcx (cw cWork)), I (.load .rax (rw .rcx wPB)), I (.addi .rax (wd phaseWords)),
    I (.store (rw .rcx wPB) .rax), I (.load .rbp (rw .rcx wPN)), I (.subi .rbp 1),
    I (.store (rw .rcx wPN) .rbp)])]

/-- **The wire decoder**: the areas' sizes checked, the stream, the phases, no byte left. -/
def decode : Stmt := blk [
  I (.load .rax (cw cLen)), I (.shri .rax 4), I (.shli .rax 1),
  I (.addi .rax (Int64.ofNat (2 + 8 * phaseWords))), I (.load .rbx (cw cDecN)),
  failIf (.cmp .ltu .rbx (.reg .rax)),
  I (.load .rbx (cw cWorkN)), failIf (.cmp .ltu .rbx (.imm (Int64.ofNat workWords))),
  I (.movi .r15 0), stream, phases,
  I (.load .rax (cw cLen)), failIf (.cmp .ne .rax (.reg .r15))]

end NativeVm.Wire
