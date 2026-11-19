module

public import NativeVm.Transcript.Layout

/-!
# The transcript's gadgets

QM code for the transcript's operations, on the words of `NativeVm.Transcript.Layout`, with `rdi`
at the context throughout (`Keccak.hash` and `Keccak.permute` run with it moved to the scratch
area, `hashAt`, `permuteAt`). A gadget that rejects ends at `.fail`.

| gadget | `run`'s constructor | inputs | outputs |
|---|---|---|---|
| `readScalar` | `read` | | the scalar's limbs in `r9`, `r10` |
| `sampleChallenge` | `sample` | | the challenge's limbs in `r9`, `r10` |
| `grind` | `grind bits` | `bits` in `rsi` | |
| `commit` | `commit height width` | `height` in `rsi`, `width` in `rbx` | |
| `query` | `query i positions` | `i` in `r9`, the positions' address in `r10`, their count in `r11`, the rows' address in `r12` | the rows, `width` words each |
| `seed` | `spongeSeedWith`, `runProof`'s start | | |
| `finish` | `runProof`'s check | | |

All but `query` write only `clobbers`; `query` writes every register but `rdi`, `rsp` and `rbp`.
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Protocol.Compile

/-- The byte displacement of word `k`. -/
def wdisp (k : Nat) : Int64 := Int64.ofNat (8 * k)

/-- Word `k` of the context. -/
abbrev cw (k : Nat) : Addr := at_ .rdi (wdisp k)

/-- Copy the context's words `src .. src + n` to `dst .. dst + n`, through `rax`. -/
def copyCtx (src dst n : Nat) : Stmt := blk <| (List.range n).flatMap fun t ↦
  [I (.load .rax (cw (src + t))), I (.store (cw (dst + t)) .rax)]

/-- Zero the context's words `dst .. dst + n`. -/
def zeroCtx (dst n : Nat) : Stmt := blk <| (List.range n).flatMap fun t ↦ [I (.storei (cw (dst + t)) 0)]

/-- `Keccak.hash` with its scratch area at the context's `scratchW`. -/
def hashAt : Stmt := blk [I (.addi .rdi (wdisp scratchW)), Keccak.hash, I (.subi .rdi (wdisp scratchW))]

/-- `Keccak.permute` on the lanes at the context's `scratchW`. -/
def permuteAt : Stmt :=
  blk [I (.addi .rdi (wdisp scratchW)), Keccak.permute, I (.subi .rdi (wdisp scratchW))]

/-! ## The sponge -/

/-- `duplex`: the rate lanes of the waiting scalars and the state's capacity into the scratch
lanes, permute, the result back into the state; the queue empties. Writes `rax`, `rcx`, `r8`. -/
def duplex : Stmt := blk [
  copyCtx rateW scratchW 16,
  copyCtx (laneW + 16) (scratchW + 16) 9,
  permuteAt,
  copyCtx scratchW laneW 25,
  zeroCtx rateW 16,
  I (.storei (cw countW) 0)]

/-- Word `k` of the rate lanes from `rdx` bytes on. -/
def rateAt (k : Nat) : Addr := { base := .rdi, idx := some (.rdx, .W8), disp := wdisp (rateW + k) }

/-- Append the scalar of limbs `r9`, `r10` with the tag `tag` to a queue that is not full. -/
def appendPending (tag : Nat) : List Stmt := [
  I (.load .rax (cw countW)),
  I (.mov .rdx .rax), I (.shli .rdx 5),
  I (.store (rateAt 0) .r9), I (.store (rateAt 1) .r10),
  I (.storei (rateAt 2) 0), I (.storei (rateAt 3) (Int64.ofNat tag)),
  I (.addi .rax 1), I (.store (cw countW) .rax)]

/-- `absorb` the scalar of limbs `r9`, `r10` with the tag `tag`: a full queue is permuted first.
Writes `rax`, `rcx`, `rdx`, `r8`. -/
def absorb (tag : Nat) : Stmt := blk <|
  I (.load .rax (cw countW)) :: .ite (.cmp .eq .rax (.imm 4)) duplex .skip :: appendPending tag

/-- Reject while a grind's challenge waits. Writes `rax`. -/
def checkGround : Stmt := blk [I (.load .rax (cw groundW)), failIf (.cmp .ne .rax (.imm 0))]

/-- Word `k` of the decoded area from `rdx + rcx`. -/
def decAt (k : Nat) : Addr := { base := .rdx, idx := some (.rcx, .W8), disp := wdisp k }

/-- The next stream element's limbs into `r9`, `r10`, the cursor advanced; reject at the stream's
end. Writes `rax`, `rcx`, `rdx`, `r9`, `r10`, `r11`. -/
def nextScalar : Stmt := blk [
  I (.load .r11 (cw ctxWork)), I (.load .rdx (cw ctxDecoded)),
  I (.load .rax (at_ .r11 (wdisp workCursor))), I (.load .rcx (at_ .rdx 0)),
  failIf (.cmp .geu .rax (.reg .rcx)),
  I (.mov .rcx .rax), I (.shli .rcx 4),
  I (.load .r9 (decAt 1)), I (.load .r10 (decAt 2)),
  I (.addi .rax 1), I (.store (at_ .r11 (wdisp workCursor)) .rax)]

/-! ## The gadgets -/

/-- **`read`**: the next scalar, absorbed with `dsObserve`; its limbs in `r9`, `r10`. -/
def readScalar : Stmt := blk [checkGround, nextScalar, absorb dsObserve]

/-- **`sample`**: the ground challenge if a grind drew one, else a permutation's first two lanes;
its limbs in `r9`, `r10`. -/
def sampleChallenge : Stmt := blk [
  I (.load .rax (cw groundW)),
  .ite (.cmp .ne .rax (.imm 0))
    (blk [I (.load .r9 (cw (groundW + 1))), I (.load .r10 (cw (groundW + 2))),
      I (.storei (cw groundW) 0)])
    (blk [duplex, I (.load .r9 (cw laneW)), I (.load .r10 (cw (laneW + 1)))])]

/-- **`grind bits`**, `bits` in `rsi`: the nonce read, absorbed with `dsPowNonce` and permuted
(`absorbNonce`); the permutation's first two lanes become the ground challenge, and its third lane's
low `bits` bits must be zero (`powOk`). -/
def grind : Stmt := blk [
  checkGround, nextScalar, absorb dsPowNonce, duplex,
  I (.load .r9 (cw laneW)), I (.store (cw (groundW + 1)) .r9),
  I (.load .r9 (cw (laneW + 1))), I (.store (cw (groundW + 2)) .r9),
  I (.storei (cw groundW) 1),
  I (.mov .rcx .rsi), I (.movi .rdx 1), I (.shlcl .rdx), I (.subi .rdx 1),
  .ite (.cmp .geu .rsi (.imm 64)) (I (.movi .rdx (-1))) .skip,
  I (.load .rax (cw (laneW + 2))), I (.and .rax .rdx),
  failIf (.cmp .ne .rax (.imm 0))]

/-- Word `k` of the root entry `rcx` bytes into the roots, from `r11`. -/
def rootAt (k : Nat) : Addr := { base := .r11, idx := some (.rcx, .W8), disp := wdisp (workRoots + k) }

/-- Store `r9`, `r10` at words `k`, `k + 1` of the next root's entry. Writes `rcx`, `r11`. -/
def storeRootPair (k : Nat) : Stmt := blk [
  I (.load .r11 (cw ctxWork)), I (.load .rcx (at_ .r11 (wdisp workRootCount))), I (.shli .rcx 6),
  I (.store (rootAt k) .r9), I (.store (rootAt (k + 1)) .r10)]

/-- **`commit height width`**, `height` in `rsi`, `width` in `rbx`: two scalars read and absorbed,
the root their halves' digest (`digestFromHalves`), appended to the roots with its shape. -/
def commit : Stmt := blk [
  checkGround,
  nextScalar, absorb dsObserve, storeRootPair 0,
  nextScalar, absorb dsObserve, storeRootPair 2,
  I (.load .r11 (cw ctxWork)), I (.load .rax (at_ .r11 (wdisp workRootCount))),
  I (.mov .rcx .rax), I (.shli .rcx 6),
  I (.store (rootAt 4) .rsi), I (.store (rootAt 5) .rbx),
  I (.addi .rax 1), I (.store (at_ .r11 (wdisp workRootCount)) .rax)]

/-! ## Queries -/

/-- One level of a climb: the node in the scratch lanes and the sibling at `r9` into the climb's
input, the node left when the position `r14` is even; hashed; the position halved, `r9` at the
next sibling, `r15` counted down. -/
def climbStep : Stmt := blk [
  .ite (.test true .r14 (.imm 1))
    (blk [copyCtx scratchW climbW 4,
      blk ((List.range 4).flatMap fun k ↦
        [I (.load .rax (at_ .r9 (wdisp k))), I (.store (cw (climbW + 4 + k)) .rax)])])
    (blk [blk ((List.range 4).flatMap fun k ↦
        [I (.load .rax (at_ .r9 (wdisp k))), I (.store (cw (climbW + k)) .rax)]),
      copyCtx scratchW (climbW + 4) 4]),
  I (.lea .rsi (cw climbW)), I (.movi .rbx 64), hashAt,
  I (.shri .r14 1), I (.addi .r9 32), I (.subi .r15 1)]

/-- The climb's top against the root's digest. -/
def checkRoot : Stmt := blk <| (List.range 4).flatMap fun k ↦
  [I (.load .rax (cw (scratchW + k))), I (.load .rcx (cw (qRootW + k))),
    failIf (.cmp .ne .rax (.reg .rcx))]

/-- One opening, at `r13`, its position at `r10`: the leaf index checked against the position, the
leaf hashed and copied to `r12`, the path climbed, the top checked; `r10`, `r13` at the next, `r11`
counted down. -/
def openOne : Stmt := blk [
  I (.load .rax (at_ .r13 0)), I (.load .r14 (at_ .r10 0)), failIf (.cmp .ne .rax (.reg .r14)),
  I (.lea .rsi (at_ .r13 8)), I (.load .rbx (cw (qRootW + 5))), I (.shli .rbx 3),
  hashAt,
  I (.load .r15 (cw (qRootW + 5))), I (.lea .r9 (at_ .r13 8)),
  .loop (.cmp .ne .r15 (.imm 0)) (blk [
    I (.load .rax (at_ .r9 0)), I (.store (at_ .r12 0) .rax),
    I (.addi .r9 8), I (.addi .r12 8), I (.subi .r15 1)]),
  I (.load .r15 (cw (qRootW + 4))), I (.lea .r9 (at_ .r13 (wdisp (1 + wireMaxLeafWords)))),
  .loop (.cmp .ne .r15 (.imm 0)) climbStep,
  checkRoot,
  I (.addi .r10 8), I (.addi .r13 (wdisp openingWords)), I (.subi .r11 1)]

/-- **`query i positions`**: root `i` (`r9`) and its shape, the next phase, its shape and its
positions checked against the root's and `positions` (`r11` words at `r10`), and each opening's
path climbed to the root (`openPhase`); the rows to `r12`, `width` words each. -/
def query : Stmt := blk [
  I (.load .r8 (cw ctxWork)),
  I (.load .rax (at_ .r8 (wdisp workRootCount))),
  failIf (.cmp .geu .r9 (.reg .rax)),
  I (.shli .r9 6),
  blk ((List.range 6).flatMap fun k ↦
    [I (.load .rax { base := .r8, idx := some (.r9, .W8), disp := wdisp (workRoots + k) }),
      I (.store (cw (qRootW + k)) .rax)]),
  I (.load .rax (at_ .r8 (wdisp workPhase))), I (.load .rcx (at_ .r8 (wdisp workPhaseCount))),
  failIf (.cmp .geu .rax (.reg .rcx)),
  I (.addi .rax 1), I (.store (at_ .r8 (wdisp workPhase)) .rax),
  I (.load .r13 (at_ .r8 (wdisp workPhasePtr))),
  I (.lea .rax (at_ .r13 (wdisp phaseWords))), I (.store (at_ .r8 (wdisp workPhasePtr)) .rax),
  I (.load .rax (at_ .r13 0)), failIf (.cmp .ne .rax (.reg .r11)),
  .ite (.cmp .eq .r11 (.imm 0)) .skip (blk [
    I (.load .rax (at_ .r13 8)), I (.load .rcx (cw (qRootW + 4))),
    failIf (.cmp .ne .rax (.reg .rcx)),
    I (.load .rax (at_ .r13 16)), I (.load .rcx (cw (qRootW + 5))),
    failIf (.cmp .ne .rax (.reg .rcx))]),
  I (.addi .r13 24),
  .loop (.cmp .ne .r11 (.imm 0)) openOne]

/-! ## The start and the end -/

/-- `"leanvm-v"`, the tag's first eight bytes, as a little-endian word. -/
def tagWord : Int64 := 0x762D6D766E61656C

/-- `"1"`, the tag's ninth byte. -/
def tagByte : Int64 := 0x31

/-- The seed's hash input (`seedWords`) into the working area: the tag's first eight bytes, then
each bytecode word shifted up a byte over the previous word's top byte (first the tag's ninth),
then the last word's top byte. -/
def shiftLoop : Stmt :=
  .loop (.cmp .ltu .rcx (.reg .r9)) (blk [
    I (.load .rax { base := .rsi, idx := some (.rcx, .W64) }),
    I (.mov .r8 .rax), I (.shli .r8 8), I (.add .r8 .rdx),
    I (.store { base := .r11, idx := some (.rcx, .W64), disp := 8 } .r8),
    I (.mov .rdx .rax), I (.shri .rdx 56),
    I (.addi .rcx 1)])

/-- The seed's hash input, `bytecode length + 2` words from the working area's start. -/
def seedBuffer : Stmt := blk [
  I (.load .r11 (cw ctxWork)), I (.load .rsi (cw ctxBytecode)), I (.load .r9 (cw ctxBytecodeLen)),
  I (.movi .rax tagWord), I (.store (at_ .r11 0) .rax),
  I (.movi .rdx tagByte), I (.movi .rcx 0),
  shiftLoop,
  I (.store { base := .r11, idx := some (.rcx, .W64), disp := 8 } .rdx)]

/-- The sponge's initial state: the IV in the scratch lanes, the public input after it, zeros,
permuted; the queue and the ground empty. -/
def seedState : Stmt := blk [
  copyCtx ctxPublic (scratchW + 4) 4,
  zeroCtx (scratchW + 8) 17,
  permuteAt,
  copyCtx scratchW laneW 25,
  zeroCtx rateW 16,
  I (.storei (cw countW) 0), I (.storei (cw groundW) 0)]

/-- The cursors at the stream's and the openings' starts, no roots. -/
def seedCursors : Stmt := blk [
  I (.load .r11 (cw ctxWork)), I (.load .rdx (cw ctxDecoded)),
  I (.storei (at_ .r11 (wdisp workCursor)) 0), I (.storei (at_ .r11 (wdisp workPhase)) 0),
  I (.storei (at_ .r11 (wdisp workRootCount)) 0),
  I (.load .rax (cw ctxWireLen)), I (.shri .rax 4), I (.shli .rax 4), I (.add .rax .rdx),
  I (.load .rcx (at_ .rax 8)), I (.store (at_ .r11 (wdisp workPhaseCount)) .rcx),
  I (.addi .rax 16), I (.store (at_ .r11 (wdisp workPhasePtr)) .rax)]

/-- **The seed** (`spongeSeedWith`) and `runProof`'s initial state: the tag's bytes then the
bytecode's into the working area (`seedBuffer`), hashed; the digest and the public input permuted
into the sponge (`seedState`); the cursors at the stream's and the openings' starts, no roots
(`seedCursors`). -/
def seed : Stmt := blk [
  seedBuffer,
  I (.mov .rbx .r9), I (.shli .rbx 3), I (.addi .rbx 9), I (.mov .rsi .r11),
  hashAt,
  seedState,
  seedCursors]

/-- **`runProof`'s check**: reject unless the stream and the openings are consumed. -/
def finish : Stmt := blk [
  I (.load .r11 (cw ctxWork)), I (.load .rdx (cw ctxDecoded)),
  I (.load .rax (at_ .r11 (wdisp workCursor))), I (.load .rcx (at_ .rdx 0)),
  failIf (.cmp .ne .rax (.reg .rcx)),
  I (.load .rax (at_ .r11 (wdisp workPhase))), I (.load .rcx (at_ .r11 (wdisp workPhaseCount))),
  failIf (.cmp .ne .rax (.reg .rcx))]

end NativeVm.Transcript
