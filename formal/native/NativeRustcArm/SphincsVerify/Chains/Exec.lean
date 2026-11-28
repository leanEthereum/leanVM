module

public import NativeRustcArm.Sym
public import NativeRustcArm.Code.Sphincs.SphincsVerify
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# The chains' blocks, run by the symbolic executor

The symbolic states the chains' proof starts blocks from and the executor's results
(`run_b<k>`). Most blocks run in the frame (region 0, SP its base, `frameS`); where the proof knows
a value in memory (a hasher's `buf_len`), the start state holds it as a literal write, so the
executor folds the branches. Two blocks index memory by the chain:
- `b105` (`.LSphincsVerify_37`) reads the chain's digit at `15936 + i` and its value at the layer's
  chain values plus `16 i`, and spills `i` at `416`: region 0 the 64 digits (SP `ptr 0 (-15936)`),
  region 1 the chain's value, region 2 the 16-byte cell at `SP + 8224`, region 3 the spills at
  `408 .. 424`;
- `b104` (`.LSphincsVerify_36`) loads `i` from `416` and stores the chain's end at `20464 + 16 i`:
  region 0 the spills (`0 .. 448`), region 1 the end, region 2 the cell.

`after ds S` is the state `exec ds S` ends in.
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

theorem exec_after {ds ds' : List Directive} {S S₁ : SState} {x : Exit}
    (h : exec ds S = some (S₁, x)) {r : Option (SState × Exit)} (h' : exec ds' (after ds S) = r) :
    exec ds' S₁ = r := by
  rw [after, h] at h'
  exact h'

/-- The registers the chains keep: X29 the saved registers, the hashers' buffers, `136`, X27. -/
def keptK : List (XReg × Sym) :=
  [(.X29, .ptr 0 21520), (.X19, .lit 136), (.X21, .ptr 0 19208), (.X25, .ptr 0 8840),
    (.X27, .ptr 0 19008)]

/-- The frame (region 0), SP its base, the registers `k` and `keptK`. -/
def frameS (k : List (XReg × Sym)) : SState := init [(21616, true)] (.ptr 0 0) (k ++ keptK)

/-- A literal 64-bit word in the frame. -/
def litW (off v : Nat) : Write := ⟨0, off, 8, .lit v⟩

/-- At `b107` (a step's head). -/
def s107 : SState := frameS []

/-- After `memset` of hasher A: its `buf_len` zero. -/
def s108 : SState := { frameS [] with mem := [litW 8976 0] }

/-- After the address's `memcpy`: X22, X23, X24 the loop's, `buf_len` 16. -/
def s116 : SState :=
  { frameS [(.X22, .ptr 0 13888), (.X23, .lit 32), (.X24, .lit 32)] with mem := [litW 8976 16] }

/-- After the clone: hasher B's `buf_len` 48. -/
def s120 : SState := { frameS [] with mem := [litW 19344 48] }

/-- After the value's `memcpy`: X22, X23, X28 the loop's, B's `buf_len` 48. -/
def s125 : SState :=
  { frameS [(.X22, .ptr 0 12864), (.X23, .lit 16), (.X28, .lit 16)] with mem := [litW 19344 48] }

/-- From the state's copy on: X24 B's `buf_len`, 64. -/
def s129 : SState := frameS [(.X24, .lit 64)]

/-- After `keccak_f`, and at `b133`. -/
def s132 : SState := frameS []

/-- `s << 4`. -/
def sh4Sym (s : Sym) : Sym := .un (.shift .LSL 4) .W64 s

/-- At `b104`: the spills, the chain's end, the cell. -/
def s104 : SState :=
  init [(448, true), (16, false), (16, false)] (.ptr 0 0) [(.X29, .ptr 2 13296)] [] []
    [(.bin .add .W64 (.ptr 0 20464) (sh4Sym (.load 0 416 8)), 1, 0),
      (.ptr 0 8224, 2, 0), (.ptr 0 8232, 2, 8)]

/-- At `b105`: the digits, the chain's value, the cell, the spills `408..424`; X1 the chain. -/
def s105 : SState :=
  init [(64, true), (16, false), (16, false), (16, false)] (.ptr 0 (-15936)) [(.X29, .ptr 2 13296)]
    [] [(.reg .X1, 64)]
    [(.ptr 0 (-15528), 3, 0), (.ptr 0 (-15520), 3, 8),
      (.bin .add .W64 (.load 3 0 8) (sh4Sym (.reg .X1)), 1, 0),
      (.ptr 0 (-7712), 2, 0), (.ptr 0 (-7704), 2, 8)]

/-- At `b106`: the frame. -/
def s106 : SState := frameS []

end

set_option Elab.async false

sym_block run_b104 := exec b104 s104
sym_block run_b105 := exec b105 s105
sym_block run_b106 := exec b106 s106
sym_block run_b107 := exec b107 s107
sym_block run_b108 := exec b108 s108
sym_block run_b111 := exec b111 (after b108 s108)
sym_block run_b113 := exec b113 (after b111 (after b108 s108))
sym_block run_b114 := exec b114 (after b113 (after b111 (after b108 s108)))
sym_block run_b115 := exec b115 (after b114 (after b113 (after b111 (after b108 s108))))
sym_block run_b116 := exec b116 s116
sym_block run_b112 := exec b112 (after b116 s116)
sym_block run_b119 := exec b119 (after b112 (after b116 s116))
sym_block run_b120 := exec b120 s120
sym_block run_b122 := exec b122 (after b120 s120)
sym_block run_b123 := exec b123 (after b122 (after b120 s120))
sym_block run_b124 := exec b124 (after b123 (after b122 (after b120 s120)))
sym_block run_b125 := exec b125 s125
sym_block run_b121 := exec b121 (after b125 s125)
sym_block run_b128 := exec b128 (after b121 (after b125 s125))
sym_block run_b129 := exec b129 s129
sym_block run_b130 := exec b130 (after b129 s129)
sym_block run_b131 := exec b131 s129
sym_block run_b132 := exec b132 s132
sym_block run_b133 := exec b133 s132

end NativeRustcArm.SphincsVerifyProof.Chains
