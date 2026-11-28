module

public import NativeRustcArm.Code.Xmss.WotsLeaf.Names

public import NativeRustcArm.WotsLeaf.Steps
public import NativeRustcArm.Code.Xmss.WotsLeaf
public meta import NativeRustcArm.Code.Xmss.WotsLeaf
public meta import NativeRustcArm.WotsLeaf.FrameS

/-!
# The chains' blocks, run by the symbolic executor

The symbolic states the chains' proof starts blocks from and the executor's results
(`run_b<k>`). The step's blocks run in the frame (region 0) with X19 `136` and the hashers'
buffers X21, X23 known (`sK`); where the proof knows a `buf_len`, the start state holds it as a
literal write, so the executor folds the branches (the full-buffer blocks `b17`, `b25`, `b34` and
the panics are never reached). `b16` reads `P` through X20: `P`'s 16 bytes are region 1 (`s16`).
`b14` reads chain `i`'s digit at `380 + i` (X28 bounded by 58) and its value at the chain values
plus `16 i` (region 1, the alias of `X22 + (X28 << 4)`). `b13` stores chain `i`'s end at
`440 + 16 i`: it runs with `i` a literal (`s13 i`), its checks `ok13` decided for every `i < 58`.
-/

namespace NativeRustcArm.WotsLeafProof.Chain

open NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf

@[expose] public section

/-- The registers the chains keep: X19 `136`, the hashers' buffers X21 and X23. -/
def keptK : List (XReg × Sym) := [(.X19, .lit 136), (.X21, .ptr 0 1976), (.X23, .ptr 0 1632)]

/-- The frame, the registers `k` and `keptK`. -/
def sK (k : List (XReg × Sym)) : SState := frameS (k ++ keptK)

/-- `X28 << 4`. -/
def sh4 (x : XReg) : Sym := .un (.shift .LSL 4) .W64 (.reg x)

/-- At `b14`: the frame, chain `i`'s value (region 1); X9 the codeword, X28 below 58. -/
def s14 : SState :=
  init [(2752, true), (16, false)] (.ptr 0 0) ((.X29, .ptr 0 2656) :: (.X9, .ptr 0 380) :: keptK) []
    [(.reg .X28, 58)] [(.bin .add .W64 (.reg .X22) (sh4 .X28), 1, 0)]

/-- At `b16`: the frame, `P` (region 1) at X20, A's `buf_len` zero. -/
def s16 : SState :=
  { init [(2752, true), (16, false)] (.ptr 0 0) ((.X29, .ptr 0 2656) :: (.X20, .ptr 1 0) :: keptK)
    with mem := [litW 2112 0] }

/-- After the address's `memcpy`: X24, X25, X26 the loop's, A's `buf_len` 16. -/
def s24 : SState :=
  { sK [(.X24, .ptr 0 2504), (.X25, .lit 16), (.X26, .lit 16)] with mem := [litW 2112 16] }

/-- After the clone: B's `buf_len` 32. -/
def s28 : SState := { sK [] with mem := [litW 1768 32] }

/-- After the payload's `memcpy`: X24, X25, X27 the loop's, B's `buf_len` 32. -/
def s33 : SState :=
  { sK [(.X24, .ptr 0 1400), (.X25, .lit 32), (.X27, .lit 32)] with mem := [litW 1768 32] }

/-- From the state's copy on: X26 B's `buf_len`, 64. -/
def s37 : SState := sK [(.X26, .lit 64)]

/-- At `b13` for chain `i`. -/
def s13 (i : Nat) : SState := sK [(.X28, .lit i)]

/-- What `b13` does for chain `i` (decided on the literal state): the end's two words written at
`440 + 16 i` from `1384`, no other write below them, the frame's invariant kept, X19, X21, X23
kept, X28 `i + 1`, X22 the chain values' address from the frame's byte 8, X9 the codeword's, the
exit to `b44` after chain 57. -/
def ok13 (i : Nat) : Bool :=
  match exec b13 (s13 i) with
  | some (S, x) =>
    covers S.mem 0 (440 + 16 * i) 8 (.load 0 1384 8) &&
      covers S.mem 0 (448 + 16 * i) 8 (.load 0 1392 8) && blockOK S &&
      Run.noWriteIn S 0 (440 + 16 * i) && S.reg .X19 == some (.lit 136) &&
      S.reg .X20 == some (.reg .X20) && S.reg .X21 == some (.ptr 0 1976) &&
      S.reg .X23 == some (.ptr 0 1632) && S.reg .X28 == some (.lit (i + 1)) &&
      S.reg .X22 == some (.load 0 8 8) && S.reg .X9 == some (.ptr 0 380) &&
      x == .cond (.lit (i + 1 == 58)) NativeRustcArm.Xmss.WotsLeaf.label_27
  | none => false

end

set_option Elab.async false

sym_block run_b14 := exec b14 s14
sym_block run_b15 := exec b15 (sK [])
sym_block run_b16 := exec b16 s16
sym_block run_b19 := exec b19 (after b16 s16)
sym_block run_b21 := exec b21 (after b19 (after b16 s16))
sym_block run_b22 := exec b22 (after b21 (after b19 (after b16 s16)))
sym_block run_b23 := exec b23 (after b22 (after b21 (after b19 (after b16 s16))))
sym_block run_b24 := exec b24 s24
sym_block run_b20 := exec b20 (after b24 s24)
sym_block run_b27 := exec b27 (after b20 (after b24 s24))
sym_block run_b28 := exec b28 s28
sym_block run_b30 := exec b30 (after b28 s28)
sym_block run_b31 := exec b31 (after b30 (after b28 s28))
sym_block run_b32 := exec b32 (after b31 (after b30 (after b28 s28)))
sym_block run_b33 := exec b33 s33
sym_block run_b29 := exec b29 (after b33 s33)
sym_block run_b36 := exec b36 (after b29 (after b33 s33))
sym_block run_b37 := exec b37 s37
sym_block run_b38 := exec b38 (after b37 s37)
sym_block run_b39 := exec b39 s37
sym_block run_b40 := exec b40 (sK [])
sym_block run_b41 := exec b41 (sK [])

public theorem ok13_all : ∀ i < 58, ok13 i = true := by decide +kernel

end NativeRustcArm.WotsLeafProof.Chain
