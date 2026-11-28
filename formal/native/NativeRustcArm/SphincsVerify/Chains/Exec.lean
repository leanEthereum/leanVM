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
- `b114` (`.LSphincsVerify_45`) reads the chain's digit at `23696 + i` and its value at the layer's
  chain values plus `16 i`: region 0 the 64 digits (SP `ptr 0 (-23696)`), region 1 the chain's
  value (the alias of `X8 + (X0 << 4)`), region 2 the 16-byte cell at `SP + 15984`;
- `b113` (`.LSphincsVerify_44`) stores the chain's end at `28224 + 16 i`: region 0 the spills
  (`0 .. 432`), region 1 the end (the alias of `base + 28224 + (X28 << 4)`), region 2 the cell.

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

/-- The registers the chains keep: X29 the saved registers, the hashers' buffers, `136`. -/
def keptK : List (XReg × Sym) :=
  [(.X29, .ptr 0 29280), (.X21, .ptr 0 26968), (.X25, .ptr 0 16600), (.X26, .lit 136)]

/-- The frame (region 0), SP its base, the registers `k` and `keptK`. -/
def frameS (k : List (XReg × Sym)) : SState := init [(29376, true)] (.ptr 0 0) (k ++ keptK)

/-- A literal 64-bit word in the frame. -/
def litW (off v : Nat) : Write := ⟨0, off, 8, .lit v⟩

/-- At `b116` (a step's head): X22 the address's scratch. -/
def s116 : SState := frameS [(.X22, .ptr 0 21648)]

/-- After `memset` of hasher A: its `buf_len` zero. -/
def s117 : SState := { frameS [] with mem := [litW 16736 0] }

/-- After the address's `memcpy`: X22, X23, X24 the loop's, `buf_len` 16. -/
def s125 : SState :=
  { frameS [(.X22, .ptr 0 21648), (.X23, .lit 32), (.X24, .lit 32)] with mem := [litW 16736 16] }

/-- After the clone: hasher B's `buf_len` 48. -/
def s129 : SState := { frameS [] with mem := [litW 27104 48] }

/-- After the value's `memcpy`: X22, X23, X27 the loop's, B's `buf_len` 48. -/
def s134 : SState :=
  { frameS [(.X22, .ptr 0 20624), (.X23, .lit 16), (.X27, .lit 16)] with mem := [litW 27104 48] }

/-- From the state's copy on: X24 B's `buf_len`, 64. -/
def s138 : SState := frameS [(.X24, .lit 64)]

/-- After `keccak_f`, and at `b142`. -/
def s141 : SState := frameS []

/-- `X28 << 4` and `X0 << 4`. -/
def sh4 (x : XReg) : Sym := .un (.shift .LSL 4) .W64 (.reg x)

/-- At `b113`: the spills, the chain's end, the cell. -/
def s113 : SState :=
  init [(432, true), (16, false), (16, false)] (.ptr 0 0) [(.X29, .ptr 2 13296)] [] []
    [(.bin .add .W64 (.ptr 0 28224) (sh4 .X28), 1, 0),
      (.ptr 0 15984, 2, 0), (.ptr 0 15992, 2, 8)]

/-- At `b114`: the digits, the chain's value, the cell; X0 the chain. -/
def s114 : SState :=
  init [(64, true), (16, false), (16, false)] (.ptr 0 (-23696)) [(.X29, .ptr 2 13296)] [] [(.reg .X0, 64)]
    [(.bin .add .W64 (.reg .X8) (sh4 .X0), 1, 0),
      (.ptr 0 (-7712), 2, 0), (.ptr 0 (-7704), 2, 8)]

/-- At `b115`: registers only. -/
def s115 : SState := init []

end

set_option Elab.async false

sym_block run_b113 := exec b113 s113
sym_block run_b114 := exec b114 s114
sym_block run_b115 := exec b115 s115
sym_block run_b116 := exec b116 s116
sym_block run_b117 := exec b117 s117
sym_block run_b120 := exec b120 (after b117 s117)
sym_block run_b122 := exec b122 (after b120 (after b117 s117))
sym_block run_b123 := exec b123 (after b122 (after b120 (after b117 s117)))
sym_block run_b124 := exec b124 (after b123 (after b122 (after b120 (after b117 s117))))
sym_block run_b125 := exec b125 s125
sym_block run_b121 := exec b121 (after b125 s125)
sym_block run_b128 := exec b128 (after b121 (after b125 s125))
sym_block run_b129 := exec b129 s129
sym_block run_b131 := exec b131 (after b129 s129)
sym_block run_b132 := exec b132 (after b131 (after b129 s129))
sym_block run_b133 := exec b133 (after b132 (after b131 (after b129 s129)))
sym_block run_b134 := exec b134 s134
sym_block run_b130 := exec b130 (after b134 s134)
sym_block run_b137 := exec b137 (after b130 (after b134 s134))
sym_block run_b138 := exec b138 s138
sym_block run_b139 := exec b139 (after b138 s138)
sym_block run_b140 := exec b140 s138
sym_block run_b141 := exec b141 s141
sym_block run_b142 := exec b142 s141

end NativeRustcArm.SphincsVerifyProof.Chains
