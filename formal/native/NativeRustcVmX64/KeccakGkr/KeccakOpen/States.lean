module

public import NativeRustcVmX64.Transcript.Frame

/-!
# `keccak_open`'s symbolic states and block checks (x86-64)

The frame: RBP to RBX pushed at offsets `2200` to `2160` of the 2208 bytes below the entry's RSP
(`slots`), RSP at offset `8` in the body; the call's argument word at `8`, the frame's saved words
from `16` (a looped round's row, the addresses of rows), the result's address at `64`, the
sumcheck's value at `72` (high) and `80` (low), the sumcheck's `Option<EW>` at `88`, the row
buffers at `112` and `1136`.

The blocks around the fold run from `pS ks`: region 0 the frame (and the return address), 1 the
slot point (96 bytes), 2 the rows, 3 the six stack argument words (reached as the frame's offsets
`2216` on, aliases), the known registers `ks` (stable values over the regions and variables `0`
to `3`). A block's result is checked by `blkOk`: its writes in the frame below `64`, the known
registers `ks'` after it (`regsOk`, reading the known loads `klOf t ws` as their values: the rows'
and slot point's addresses, round `t`'s challenge, the saved words `ws`), the saved words `ws'`
after it (`wordsOk`). An inner loop's loads run from `loS`, its stores from `stS`/`st5S`.
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots :=
  [(2200, .rbp), (2192, .r15), (2184, .r14), (2176, .r13), (2168, .r12), (2160, .rbx)]

/-- The rows. -/
def P : Sym := .ptr 2 0
/-- The challenge's low limb. -/
def V0 : Sym := .var 0
/-- The challenge's high limb. -/
def V1 : Sym := .var 1
/-- A looped round's row `i` (variable `2`) and its address `rows + 1024 i` (variable `3`). -/
def P3 : Sym := .bin .add .W64 P (.var 3)

/-- The six stack argument words as region `r`. -/
def argAliases (r : Nat) : List (Sym × Nat × Int) :=
  [(.ptr 0 2216, r, 0), (.ptr 0 2224, r, 8), (.ptr 0 2232, r, 16), (.ptr 0 2240, r, 24),
    (.ptr 0 2248, r, 32), (.ptr 0 2256, r, 40)]

/-- The fold's aliases: the arguments, the slot point's address (argument `4`). -/
def alsF : List (Sym × Nat × Int) :=
  argAliases 3 ++ [(.load 3 32 8, 1, 0), (.gotSlot "memcpy", 4, 0)]

/-- Around the fold, the registers `ks` known. -/
def pS (ks : List (Reg64 × Sym)) : SState :=
  (init [2216, 96, 65536, 48, 8] ((.rsp, .ptr 0 8) :: ks) [] [] alsF).withKnownBytes
    4 0 8 (.label "memcpy")

/-- The entry. -/
def e0S : SState :=
  (init [2216, 96, 65536, 48, 8] [(.rsp, .ptr 0 2208)] [] [] alsF).withKnownBytes
    4 0 8 (.label "memcpy")

/-- An inner loop's loads: region 0 the call's return address slot, region 1 the buffers' bytes
from the first buffer's entry (`1040` bytes), the counter `ib` from `s0`. -/
def loS (ib : Reg64) (s0 : Nat) : SState :=
  init [8, 1040] [(.rsp, .ptr 0 8)] [] [] [(.bin .add .W64 (.ptr 0 8) (.reg ib), 1, (s0 : Int) - 104)]

/-- An inner loop's stores through `dr + ib`: region 1 the row's entry (`so` below the address). -/
def stS (dr ib : Reg64) (so : Nat) : SState :=
  init [2216, 16, 48] [(.rsp, .ptr 0 8)] [] []
    (argAliases 2 ++ [(.bin .add .W64 (.reg dr) (.reg ib), 1, (so : Int))])

/-- The last round's stores, through the rows' address (argument `5`) plus RBX. -/
def st5S : SState :=
  init [2216, 16, 48] [(.rsp, .ptr 0 8)] [] []
    (argAliases 2 ++ [(.bin .add .W64 (.load 2 40 8) (.reg .rbx), 1, 0)])

/-- The result's value: region 1 the result at the frame's word `64`. -/
def outS : SState := init [2216, 24] [(.rsp, .ptr 0 8)] [] [] [(.load 0 64 8, 1, 0)]

/-- The result's tag and the epilogue: region 1 the result at RBX. -/
def resS : SState := init [2216, 24] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

/-! ## Checks -/

/-- A value that reads no register, flag or memory. -/
def stable : Sym → Bool
  | .lit _ | .ptr _ _ | .var _ | .label _ => true
  | .bin _ _ a b => stable a && stable b
  | .un _ _ a => stable a
  | _ => false

/-- The known loads `kl` replaced by their values. -/
def subst (kl : List (Sym × Sym)) (e : Sym) : Sym :=
  match kl.lookup e with
  | some v => v
  | none =>
    match e with
    | .bin op w a b => .bin op w (subst kl a) (subst kl b)
    | .un op w a => .un op w (subst kl a)
    | e => e

/-- The known loads of round `t` with the saved words `ws`. -/
def klOf (t : Nat) (ws : List (Nat × Sym)) : List (Sym × Sym) :=
  [(.load 3 40 8, P), (.load 3 32 8, .ptr 1 0), (.load 1 (16 * t) 8, V0),
    (.load 1 (16 * t + 8) 8, V1)] ++ ws.map fun p ↦ (.load 0 p.1 8, p.2)

/-- Known registers: callee-saved, with stable values. -/
def wfK (ks : List (Reg64 × Sym)) : Bool := ks.all fun p ↦ calleeSaved p.1 && stable p.2

/-- The registers `ks` after a block. -/
def regsOk (kl : List (Sym × Sym)) (S : SState) (ks : List (Reg64 × Sym)) : Bool :=
  ks.all fun p ↦ calleeSaved p.1 && stable p.2 && (S.reg p.1).map (subst kl) == some p.2

/-- A saved word after a block: written whole, or untouched and saved before. -/
def wordOk (kl : List (Sym × Sym)) (S : SState) (ws : List (Nat × Sym)) (p : Nat × Sym) : Bool :=
  stable p.2 && decide (16 ≤ p.1) && decide (p.1 + 8 ≤ 64) &&
    ((match findWrite 0 p.1 S.mem with
        | some (e, _) => subst kl e == p.2 &&
            (List.range 8).all fun j ↦ findWrite 0 (p.1 + j) S.mem == some (e, j)
        | none => false) ||
      (S.mem.all (fun w ↦ w.r != 0 || decide (w.off + w.n ≤ p.1) || decide (p.1 + 8 ≤ w.off)) &&
        ws.contains p))

/-- The saved words `ws'` after a block. -/
def wordsOk (kl : List (Sym × Sym)) (S : SState) (ws ws' : List (Nat × Sym)) : Bool :=
  ws'.all (wordOk kl S ws)

/-- Every write in the frame below `64`. -/
def low64 (S : SState) : Bool := S.mem.all fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 64)

/-- **A block around the fold**: RSP at `o'`, writes in the frame below `64`, the registers `ks'`
and the saved words `ws'` after it. -/
def blkOk (o' t : Nat) (ws : List (Nat × Sym)) (S : SState) (ks' : List (Reg64 × Sym))
    (ws' : List (Nat × Sym)) : Bool :=
  MidOk 2208 o' slots S && low64 S && regsOk (klOf t ws) S ks' && wordsOk (klOf t ws) S ws ws'

/-- **A block calling `memcpy`** from `src` into the frame's `dst`, 1024 bytes. -/
def mOk (dst : Nat) (src : Sym) (t : Nat) (ws : List (Nat × Sym)) (S : SState)
    (ks' : List (Reg64 × Sym)) (ws' : List (Nat × Sym)) : Bool :=
  blkOk 0 t ws S ks' ws' && S.reg .rdi == some (.ptr 0 dst) && S.reg .rdx == some (.lit 1024) &&
    stable src && (S.reg .rsi).map (subst (klOf t ws)) == some src

/-- **An inner loop's loads**: `EW::mul`'s arguments, the challenge (`cx0`, `cx1`) and the sum of
the two buffers' entries; the first's in `lo0`, `lo1`; the registers `keep` kept. -/
def lOk (cx0 cx1 lo0 lo1 : Reg64) (keep : List Reg64) (S : SState) : Bool :=
  S.reg .rdi == some (.reg cx0) && S.reg .rsi == some (.reg cx1) &&
    S.reg .rdx == some (.bin .xor .W64 (.load 1 1024 8) (.load 1 0 8)) &&
    S.reg .rcx == some (.bin .xor .W64 (.load 1 1032 8) (.load 1 8 8)) &&
    S.reg lo0 == some (.load 1 0 8) && S.reg lo1 == some (.load 1 8 8) &&
    S.reg .rsp == some (.ptr 0 0) && S.mem == [⟨0, 0, 8, .retAddr⟩] && calleeSaved lo0 &&
    calleeSaved lo1 && keep.all fun r ↦ S.reg r == some (.reg r)

/-- **An inner loop's stores**: the product plus the first buffer's entry at the row's entry, the
counter `ib` the value `nib`, the registers `keep` kept. -/
def sOk (lo0 lo1 ib : Reg64) (nib : Sym) (keep : List Reg64) (S : SState) : Bool :=
  MidOk 2208 8 slots S &&
    S.mem == [⟨1, 8, 8, .bin .xor .W64 (.reg .rdx) (.reg lo1)⟩,
      ⟨1, 0, 8, .bin .xor .W64 (.reg .rax) (.reg lo0)⟩] &&
    S.reg ib == some nib && keep.all fun r ↦ S.reg r == some (.reg r)

/-- An inner loop's test: the new counter is not `E`. -/
def notEnd (nib : Sym) (E : Nat) : SBool := .not (.cmp .eq .W64 nib (.lit E))

/-- Registers holding their atoms. -/
def atoms (S : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

/-! ## The known registers and saved words, by the block they start -/

/-- `i << 11`, a looped round's row's offset in the rows. -/
def sh2 : Sym := .bin .shl .W64 (.var 2) (.lit 11)
/-- The rows' `2 i`th row. -/
def srcA0 : Sym := .bin .add .W64 P sh2
/-- The rows' `2 i + 1`th row. -/
def srcB0 : Sym := .bin .add .W64 (.lit 1024) (.bin .add .W64 P sh2)

/-- Round 0's head. -/
def kR0 : List (Reg64 × Sym) := [(.r12, V0), (.r13, V1), (.rbx, .var 2), (.r14, P3)]
def k5 : List (Reg64 × Sym) :=
  [(.r12, V0), (.r13, V1), (.rbx, sh2), (.r14, P3), (.r15, P), (.rbp, .label "memcpy")]
def k7 : List (Reg64 × Sym) := [(.r12, V0), (.r13, V1), (.r14, P3), (.rbx, .lit 8)]
def kI0 : List (Reg64 × Sym) := [(.r12, V0), (.r13, V1), (.r14, P3)]
def k10 : List (Reg64 × Sym) :=
  [(.r12, V0), (.r13, V1), (.rbx, .bin .add .W64 (.var 2) (.lit 1)),
    (.r14, .bin .add .W64 (.lit 1024) P3)]
/-- Round 1's start and head. -/
def k11 : List (Reg64 × Sym) := [(.r12, V0), (.r13, V1), (.rbp, .lit 0), (.rbx, P)]
def kR1 : List (Reg64 × Sym) := [(.r12, V0), (.r13, V1), (.rbp, .var 2), (.rbx, P3)]
def k12 : List (Reg64 × Sym) :=
  [(.r12, V0), (.r13, V1), (.rbp, sh2), (.rbx, P3), (.r14, P), (.r15, .label "memcpy")]
def k14 : List (Reg64 × Sym) := [(.r12, V0), (.r13, V1), (.rbx, P3), (.rbp, .lit 8)]
def kI1 : List (Reg64 × Sym) := [(.r12, V0), (.r13, V1), (.rbx, P3)]
def k17 : List (Reg64 × Sym) :=
  [(.r12, V0), (.r13, V1), (.rbp, .bin .add .W64 (.var 2) (.lit 1)),
    (.rbx, .bin .add .W64 (.lit 1024) P3)]
/-- Rounds 2 to 5. -/
def k18 : List (Reg64 × Sym) := [(.rbp, V0), (.r12, V1), (.r13, P)]
def k58 : List (Reg64 × Sym) := [(.r12, V0), (.rbp, V1), (.r13, P)]
def k78 : List (Reg64 × Sym) := [(.r12, V0), (.r13, V1), (.rbp, P)]
def k88 : List (Reg64 × Sym) := [(.r14, V0), (.r15, V1), (.rbp, P)]
/-- A counter set. -/
def kc (ks : List (Reg64 × Sym)) (s0 : Nat) : List (Reg64 × Sym) := ks ++ [(.rbx, .lit s0)]

/-- A paired row copy retains the loaded target in callee-saved RBX. -/
def kCopy (ks : List (Reg64 × Sym)) : List (Reg64 × Sym) := ks ++ [(.rbx, .label "memcpy")]

/-- A row's address in the rows. -/
def p2 (o : Nat) : Sym := .ptr 2 (o : Int)
/-- A looped round's saved row. -/
def w5 : List (Nat × Sym) := [(16, .var 2)]
/-- Round 2's saved addresses. -/
def w19 : List (Nat × Sym) := [(16, p2 1024)]
def w23 : List (Nat × Sym) := w19 ++ [(32, p2 2048)]
def w24 : List (Nat × Sym) := w23 ++ [(24, p2 3072)]
def w28 : List (Nat × Sym) := w24 ++ [(56, p2 4096)]
def w29 : List (Nat × Sym) := w28 ++ [(48, p2 5120)]
def W6 : List (Nat × Sym) := w29 ++ [(40, p2 6144)]

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
