module

public import NativeRustcX64.Sym
public import NativeRustcX64.SphincsVerify.Frame
public import NativeRustcX64.Code.Sphincs.SphincsVerify
public meta import NativeRustcX64.Sym
public meta import NativeRustcX64.SphincsVerify.Frame
public meta import NativeRustcX64.Code.Sphincs.SphincsVerify

/-!
# The FORS region's blocks on x86-64, run by the symbolic executor

The symbolic states the FORS proof starts blocks from and the executor's results (`run_b<k>`).
Most blocks run in the frame (`frameS k`: region 0 the frame with the return address, RSP its
base, region 1 the 16 bytes below it, regions 2 and 3 the loader's `memcpy` and `memset` slots,
and the registers `k` known). Register-held call targets are carried through the node invariants.
Where the proof knows a hasher's `buf_len`, the start state holds it as a literal write (`litS`),
so the executor folds the update loops' branches. Blocks without an intervening call run on (`after`).
Three blocks index the frame by the tree `c` (RSI) or the height `z` (RCX):
- `b49` (`.LSphincsVerify_19`, a tree's head) loads tree `c`'s leaf index at `10352 + 8 c`: RSI
  bounded by 24 (`s58`);
- `b56` (`.LSphincsVerify_20`, a node's head) loads the path's node `z` of tree `c`, at the
  opening's address (`104(%rsp)`) plus `16 z`, through `cmov`ed addresses: region 0 the frame's
  first 12780 bytes, region 1 the slots below, region 2 the path's node (the alias of that sum;
  RCX bounded by 10, `s65`);
- `b87` stores tree `c`'s root at `12396 + 16 c`: region 0 the frame's first 12396 bytes, region 2
  the root's slot (the alias of RSP plus `16 c`, less 12396; `s96`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Fors

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

/-- The frame's symbolic state: RSP its base, the registers `k`. -/
def frameS (k : List (Reg64 × Sym)) : SState :=
  Run.frameState k

/-- The frame's symbolic state with the literal 64-bit word `v` at `off`. -/
def litS (k : List (Reg64 × Sym)) (off v : Nat) : SState :=
  { frameS k with mem := [⟨0, off, 8, .lit v⟩] }

/-- The address of the path's node `z` (RCX) of the tree whose opening `104(%rsp)` holds. -/
def pathSym : Sym := .bin .add .W64 (.load 0 104 8) (.bin .shl .W64 (.reg .rcx) (.lit 4))

/-- The root slot alias uses the tree counter spilled at `88`. -/
def rootSym : Sym := .bin .add .W64 (.ptr 0 0) (.bin .shl .W64 (.load 0 88 8) (.lit 4))

/-- At `b49`: the frame, RSI the tree (below 24). -/
def s58 : SState :=
  Run.frameState [(.rbx, .label "memset")] [] [(.reg .rsi, 24)]

/-- At `b56`: the frame's prefix, slots, path node; RCX below 10 and RBX `memset`. -/
def s65 : SState :=
  init [12780, 16, 16] [(.rsp, .ptr 0 0), (.rbx, .label "memset")] [] [(.reg .rcx, 10)]
    (Run.frameAliases ++ [(pathSym, 2, 0)])

/-- At `b87`: the frame's first 12396 bytes, the slots, the root's slot. -/
def s96 : SState :=
  init [12396, 16, 16] [(.rsp, .ptr 0 0)] [] [] (Run.frameAliases ++ [(rootSym, 2, -12396)])

/-- After `b87`. -/
def s96e : SState := ((exec b87 s96).getD (s96, .fall)).1

/-- After `memset` of hasher A: its `buf_len` zero. -/
def s66 : SState := litS [(.r12, .ptr 0 2024), (.r14, .label "memcpy")] 4408 0

/-- After the address's `memcpy`: RBX, R13 the loop's, RBP the address, R12 hasher A,
`buf_len` 16. -/
def s75 : SState :=
  litS [(.rbx, .lit 32), (.r13, .lit 32), (.rbp, .ptr 0 3048), (.r15, .ptr 0 4072),
    (.r14, .label "memcpy")] 4408 16

/-- After the clone: hasher B's `buf_len` 48. -/
def s80 : SState := litS [(.r14, .label "memcpy")] 896 48

/-- After the children's `memcpy`: RBX, R12 the loop's, RBP the children, B's `buf_len` 48. -/
def s86 : SState := litS [(.rbx, .lit 32), (.r15, .lit 32), (.rbp, .ptr 0 11368),
  (.r14, .label "memcpy")] 896 48

/-- After the state's copy, the block's `memset` and the block's `memcpy`: R13 B's `buf_len`
(80), R15 the block, R12 hasher A. -/
def s91 : SState := frameS [(.r13, .lit 80), (.r12, .ptr 0 2024), (.r15, .ptr 0 4072),
  (.r14, .label "memcpy")]

end

set_option Elab.async false

sym_block run_b49 := exec b49 s58
sym_block run_b50 := exec b50 (frameS [(.r12, .ptr 0 4072), (.r14, .ptr 0 112)])
sym_block run_b51 := exec b51 (frameS [(.r12, .ptr 0 4072)])
sym_block run_b52 := exec b52 (frameS [(.r12, .ptr 0 4072), (.r15, .ptr 0 560)])
sym_block run_b53 := exec b53 (frameS [(.r15, .ptr 0 560), (.r14, .label "memcpy")])
sym_block run_b54 := exec b54 (frameS [(.r15, .ptr 0 560)])
sym_block run_b55 := exec b55 (frameS [])
sym_block run_b56 := exec b56 s65
sym_block run_b57 := exec b57 s66
sym_block run_b60 := exec b60 (after b57 s66)
sym_block run_b63 := exec b63 (after b60 (after b57 s66))
sym_block run_b64 := exec b64 (after b63 (after b60 (after b57 s66)))
sym_block run_b65 := exec b65 (after b64 (after b63 (after b60 (after b57 s66))))
sym_block run_b66 := exec b66 s75
sym_block run_b62 := exec b62 (after b66 s75)
sym_block run_b70 := exec b70 (after b62 (after b66 s75))
sym_block run_b71 := exec b71 s80
sym_block run_b74 := exec b74 (after b71 s80)
sym_block run_b75 := exec b75 (after b74 (after b71 s80))
sym_block run_b76 := exec b76 (after b75 (after b74 (after b71 s80)))
sym_block run_b77 := exec b77 s86
sym_block run_b73 := exec b73 (after b77 s86)
sym_block run_b81 := exec b81 (after b73 (after b77 s86))
sym_block run_b82 := exec b82 s91
sym_block run_b83 := exec b83 (after b82 s91)
sym_block run_b84 := exec b84 s91
sym_block run_b85 := exec b85 s91
sym_block run_b86 := exec b86 (frameS [])
sym_block run_b87 := exec b87 s96

end NativeRustcX64.SphincsVerifyProof.Fors
