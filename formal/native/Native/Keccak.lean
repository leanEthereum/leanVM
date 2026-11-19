module

public import Native.QM
public import Statement.Keccak

/-!
# Keccak-256 on the QM machine

`Keccak.hash` hashes a run of 64-bit words in memory with Keccak-256 (`LeanVM.Protocol.KeccakHash.
keccak256`): `rsi` holds the words' address and `rbx` the byte length `len`; the bytes are the
words' little-endian bytes, the bytes past `len` in the last word zero. It leaves the final state's
lanes at `rdi + sA`, the digest in lanes `0` to `3`, and uses the `scratchWords` words from `rdi`
as its scratch area. It writes `rax`, `rbx`, `rcx`, `rdx`, `rsi`, `r8` and nothing else but its
scratch words. `Native.Keccak.Spec` proves it.
-/

@[expose] public section

namespace Native.Keccak

open LeanVM.Parameters

/-! ## The scratch area, as byte offsets from `rdi` -/

/-- The state's 25 lanes. -/
def sA : Int64 := 0
/-- θ's column parities. -/
def sC : Int64 := 200
/-- θ's column effects. -/
def sD : Int64 := 240
/-- The lanes after ρ and π. -/
def sB : Int64 := 280
/-- The 24 round constants. -/
def sRC : Int64 := 480
/-- The scratch area's words: `[rdi, rdi + 8 · scratchWords)`. -/
def scratchWords : Nat := 84

/-- The address `rdi + disp`. -/
abbrev atDi (disp : Int64) : Addr := at_ .rdi disp

/-- Write the 24 round constants. -/
def writeRoundConstants : Stmt := blk <| (List.range 24).flatMap fun i ↦
  [I (.movi .rax (keccakRC.getD i 0).toInt64), I (.store (atDi (sRC + 8 * i.toInt64)) .rax)]

/-- The sources of the lanes after ρ and π, in the order of `Statement.Fast.Keccak`'s
`roundLanes`: lane `j` is `rot (a_i ^ d_(i % 5)) r` for the `(i, r)` at `j`. -/
def rhoPi : List (Nat × Nat) :=
  [(0, 0), (6, 44), (12, 43), (18, 21), (24, 14), (3, 28), (9, 20), (10, 3), (16, 45), (22, 61),
    (1, 1), (7, 6), (13, 25), (19, 8), (20, 18), (4, 27), (5, 36), (11, 10), (17, 15), (23, 56),
    (2, 62), (8, 55), (14, 39), (15, 41), (21, 2)]

/-- One round of Keccak-f on the lanes at `sA`, the round's index in `rcx`, as `roundLanes`
computes it: θ's parities, its effects, ρ and π, then χ and ι. Uses `rax`, `r8`. -/
def round : Stmt := blk <|
  ((List.range 5).flatMap fun x ↦
    [I (.load .rax (atDi (sA + 8 * x.toInt64)))] ++
    ((List.range 4).flatMap fun y ↦
      [I (.load .r8 (atDi (sA + 8 * (x + 5 * (y + 1)).toInt64))), I (.xor .rax .r8)]) ++
    [I (.store (atDi (sC + 8 * x.toInt64)) .rax)]) ++
  ((List.range 5).flatMap fun x ↦
    [I (.load .rax (atDi (sC + 8 * ((x + 4) % 5).toInt64))),
      I (.load .r8 (atDi (sC + 8 * ((x + 1) % 5).toInt64))),
      I (.roli .r8 1), I (.xor .rax .r8),
      I (.store (atDi (sD + 8 * x.toInt64)) .rax)]) ++
  ((List.range 25).flatMap fun j ↦
    let (i, r) := rhoPi.getD j (0, 0)
    [I (.load .rax (atDi (sA + 8 * i.toInt64))),
      I (.load .r8 (atDi (sD + 8 * (i % 5).toInt64))),
      I (.xor .rax .r8), I (.roli .rax r),
      I (.store (atDi (sB + 8 * j.toInt64)) .rax)]) ++
  ((List.range 25).flatMap fun j ↦
    let row := j - j % 5
    [I (.load .rax (atDi (sB + 8 * (row + (j + 1) % 5).toInt64))), I (.not .rax),
      I (.load .r8 (atDi (sB + 8 * (row + (j + 2) % 5).toInt64))), I (.and .rax .r8),
      I (.load .r8 (atDi (sB + 8 * j.toInt64))), I (.xor .r8 .rax),
      I (.store (atDi (sA + 8 * j.toInt64)) .r8)]) ++
  [I (.load .rax { base := .rdi, idx := some (.rcx, .W64), disp := sRC }),
    I (.load .r8 (atDi sA)), I (.xor .r8 .rax), I (.store (atDi sA) .r8)]

/-- Keccak-f[1600] on the lanes at `sA`. Uses `rax`, `rcx`, `r8`. -/
def permute : Stmt := blk [
  writeRoundConstants,
  I (.movi .rcx 0),
  .loop (.cmp .ltu .rcx (.imm 24)) (blk [round, I (.addi .rcx 1)])]

/-- XOR the word at `rsi + 8k` into lane `k`, for `k < 17`: one block. Uses `rax`, `r8`. -/
def xorBlock : Stmt := blk <| (List.range 17).flatMap fun k ↦
  [I (.load .rax (at_ .rsi (8 * k.toInt64))), I (.load .r8 (atDi (sA + 8 * k.toInt64))),
    I (.xor .r8 .rax), I (.store (atDi (sA + 8 * k.toInt64)) .r8)]

/-- **Keccak-256 of the `rbx` bytes at `rsi`**: zero the state, absorb the whole blocks, XOR in the
words of the rest, pad (`0x01` after the last byte, `0x80` in the block's last byte), permute. -/
def hash : Stmt := blk [
  blk ((List.range 25).map fun k ↦ I (.storei (atDi (sA + 8 * k.toInt64)) 0)),
  .loop (.cmp .geu .rbx (.imm 136)) (blk [
    xorBlock, permute, I (.addi .rsi 136), I (.subi .rbx 136)]),
  I (.movi .rcx 0),
  .loop (.cmp .ltu .rcx (.reg .rbx)) (blk [
    I (.load .rax { base := .rsi, idx := some (.rcx, .W8) }),
    I (.load .r8 { base := .rdi, idx := some (.rcx, .W8), disp := sA }),
    I (.xor .r8 .rax),
    I (.store { base := .rdi, idx := some (.rcx, .W8), disp := sA } .r8),
    I (.addi .rcx 8)]),
  I (.mov .rcx .rbx), I (.andi .rcx 7), I (.shli .rcx 3),
  I (.movi .rax 1), I (.shlcl .rax),
  I (.mov .rdx .rbx), I (.andi .rdx (-8)),
  I (.load .r8 { base := .rdi, idx := some (.rdx, .W8), disp := sA }),
  I (.xor .r8 .rax),
  I (.store { base := .rdi, idx := some (.rdx, .W8), disp := sA } .r8),
  I (.movi .rax (-0x8000000000000000)),
  I (.load .r8 (atDi (sA + 128))), I (.xor .r8 .rax), I (.store (atDi (sA + 128)) .r8),
  permute]

end Native.Keccak
