module

public import NativeRustcX64.Sym
public import NativeRustcX64.SphincsVerify.Frame
public import NativeRustcX64.Code.Sphincs.SphincsVerify
public meta import NativeRustcX64.SphincsVerify.Frame
public meta import NativeRustcX64.Code.Sphincs.SphincsVerify

/-!
# The chains' blocks on x86-64, run by the symbolic executor

The symbolic states the chains' proof starts blocks from and the executor's results
(`run_b<k>`). Most blocks run in the frame's regions (`Run.match_frame`: region 0 the frame,
RSP its base, region 1 the slots below it, regions 2 and 3 the loader's `memcpy` and `memset`
slots; `frameS`), R13 the chain input buffer (`keptK`). Register-held call
targets are seeded at each call boundary. Where the proof knows a value in memory (a hasher's
`buf_len`), the start state holds it as a literal write, so the executor folds the branches.
Two blocks index the frame by the chain:
- `b117` (`.LSphincsVerify_42`) reads chain `i`'s digit at `3080 + i` (RAX `i`, bounded) and its
  value at the layer's chain values (`184(%rsp)`) plus `16 i`: region 0 the frame's first 20556
  bytes, region 1 the chain's value (the alias of that sum);
- `b116` (`.LSphincsVerify_60`) stores the chain's end at `28296 + 16 i` (`176(%rsp)` holds
  `16 i`): region 0 the frame's first 28296 bytes, region 1 the end (the alias of RSP plus
  `176(%rsp)`, less 28296).

`after ds S` is the state `exec ds S` ends in.
-/

namespace NativeRustcX64.SphincsVerifyProof.Chains

open NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify

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

/-- The register the chains keep: R13 the chain input buffer. -/
def keptK : List (Reg64 × Sym) := [(.r13, .ptr 0 8328)]

/-- The frame's regions, RSP the base, the registers `k` and `keptK`. -/
def frameS (k : List (Reg64 × Sym)) : SState :=
  Run.frameState (k ++ keptK)

/-- A literal 64-bit word in the frame. -/
def litW (off v : Nat) : Write := ⟨0, off, 8, .lit v⟩

/-- At `b118`: the frame. -/
def s118 : SState := frameS []

/-- At `b119` (a step's head): R12 hasher A, RBX `memset`. -/
def s119 : SState := frameS [(.r12, .ptr 0 4104), (.rbx, .label "memset")]

/-- After `memset` of hasher A: its `buf_len` zero. -/
def s120 : SState := { frameS [(.r14, .label "memcpy")] with mem := [litW 4440 0] }

/-- After the address's `memcpy`: R15, RBX, R12 the loop's, `buf_len` 16. -/
def s129 : SState :=
  { frameS [(.r15, .lit 32), (.rbx, .ptr 0 9352), (.r12, .lit 32), (.r14, .label "memcpy"), (.rbp, .ptr 0 560)]
    with mem := [litW 4440 16] }

/-- After the clone: hasher B's `buf_len` 48. -/
def s134 : SState := { frameS [(.r14, .label "memcpy")] with mem := [litW 896 48] }

/-- After the value's `memcpy`: R15, RBX, R12 the loop's, B's `buf_len` 48. -/
def s140 : SState :=
  { frameS [(.r15, .lit 16), (.rbx, .ptr 0 8328), (.r12, .lit 16), (.r14, .label "memcpy"), (.rbp, .ptr 0 560)]
    with mem := [litW 896 48] }

/-- After the state's copy: R14 B's `buf_len`, 64. -/
def s145 : SState := frameS [(.r14, .lit 64)]

/-- After the block's `memset`: RBX B's `buf_len`. -/
def s147 : SState := frameS [(.rbx, .lit 64), (.r15, .label "memcpy"), (.rbp, .ptr 0 2056)]

/-- After the block's `memcpy`: RBX, R12 hasher A. -/
def s148 : SState := frameS [(.rbx, .lit 64), (.r12, .ptr 0 4104), (.r14, .label "memset")]

/-- After `keccak_f`, and at `b150`. -/
def s149 : SState := frameS []

/-- At `b116`: the frame's first 28296 bytes, the chain's end. -/
def s116 : SState :=
  init [28296, 16] [(.rsp, .ptr 0 0)] [] []
    [(.bin .add .W64 (.ptr 0 0) (.load 0 176 8), 1, -28296)]

/-- At `b117`: the frame's first 20556 bytes, the chain's value; RAX the chain. -/
def s117 : SState :=
  init [20556, 16] [(.rsp, .ptr 0 0)] [] [(.reg .rax, 64)]
    [(.bin .add .W64 (.load 0 184 8) (.bin .shl .W64 (.reg .rax) (.lit 4)), 1, 0)]

end

set_option Elab.async false

sym_block run_b116 := exec b116 s116
sym_block run_b117 := exec b117 s117
sym_block run_b118 := exec b118 s118
sym_block run_b119 := exec b119 s119
sym_block run_b120 := exec b120 s120
sym_block run_b123 := exec b123 (after b120 s120)
sym_block run_b126 := exec b126 (after b123 (after b120 s120))
sym_block run_b127 := exec b127 (after b126 (after b123 (after b120 s120)))
sym_block run_b128 := exec b128 (after b127 (after b126 (after b123 (after b120 s120))))
sym_block run_b129 := exec b129 s129
sym_block run_b125 := exec b125 (after b129 s129)
sym_block run_b133 := exec b133 (after b125 (after b129 s129))
sym_block run_b134 := exec b134 s134
sym_block run_b137 := exec b137 (after b134 s134)
sym_block run_b138 := exec b138 (after b137 (after b134 s134))
sym_block run_b139 := exec b139 (after b138 (after b137 (after b134 s134)))
sym_block run_b140 := exec b140 s140
sym_block run_b136 := exec b136 (after b140 s140)
sym_block run_b144 := exec b144 (after b136 (after b140 s140))
sym_block run_b145 := exec b145 s145
sym_block run_b146 := exec b146 (after b145 s145)
sym_block run_b147 := exec b147 s147
sym_block run_b148 := exec b148 s148
sym_block run_b149 := exec b149 s149
sym_block run_b150 := exec b150 s149

end NativeRustcX64.SphincsVerifyProof.Chains
