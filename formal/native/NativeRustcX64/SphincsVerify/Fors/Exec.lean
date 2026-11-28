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
- `b58` (`.LSphincsVerify_19`, a tree's head) loads tree `c`'s leaf index at `10384 + 8 c`: RSI
  bounded by 24 (`s58`);
- `b65` (`.LSphincsVerify_20`, a node's head) loads the path's node `z` of tree `c`, at the
  opening's address (`104(%rsp)`) plus `16 z`, through `cmov`ed addresses: region 0 the frame's
  first 20556 bytes, region 1 the slots below, region 2 the path's node (the alias of that sum;
  RCX bounded by 10, `s65`);
- `b96` stores tree `c`'s root at `20172 + 16 c`: region 0 the frame's first 20172 bytes, region 2
  the root's slot (the alias of RSP plus `16 c`, less 20172; `s96`).
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

/-- At `b58`: the frame, RSI the tree (below 24). -/
def s58 : SState :=
  Run.frameState [(.rbx, .label "memset")] [] [(.reg .rsi, 24)]

/-- At `b65`: the frame's prefix, slots, path node; RCX below 10 and RBX `memset`. -/
def s65 : SState :=
  init [20556, 16, 16] [(.rsp, .ptr 0 0), (.rbx, .label "memset")] [] [(.reg .rcx, 10)]
    (Run.frameAliases ++ [(pathSym, 2, 0)])

/-- At `b96`: the frame's first 20172 bytes, the slots, the root's slot. -/
def s96 : SState :=
  init [20172, 16, 16] [(.rsp, .ptr 0 0)] [] [] (Run.frameAliases ++ [(rootSym, 2, -20172)])

/-- After `b96`. -/
def s96e : SState := ((exec b96 s96).getD (s96, .fall)).1

/-- After `memset` of hasher A: its `buf_len` zero. -/
def s66 : SState := litS [(.r12, .ptr 0 2056), (.r14, .label "memcpy")] 4440 0

/-- After the address's `memcpy`: RBX, R13 the loop's, RBP the address, R12 hasher A,
`buf_len` 16. -/
def s75 : SState :=
  litS [(.rbx, .lit 32), (.r13, .lit 32), (.rbp, .ptr 0 3080), (.r15, .ptr 0 4104),
    (.r14, .label "memcpy")] 4440 16

/-- After the clone: hasher B's `buf_len` 48. -/
def s80 : SState := litS [(.r14, .label "memcpy")] 896 48

/-- After the children's `memcpy`: RBX, R12 the loop's, RBP the children, B's `buf_len` 48. -/
def s86 : SState := litS [(.rbx, .lit 32), (.r15, .lit 32), (.rbp, .ptr 0 19144),
  (.r14, .label "memcpy")] 896 48

/-- After the state's copy, the block's `memset` and the block's `memcpy`: R13 B's `buf_len`
(80), R15 the block, R12 hasher A. -/
def s91 : SState := frameS [(.r13, .lit 80), (.r12, .ptr 0 2056), (.r15, .ptr 0 4104),
  (.r14, .label "memcpy")]

end

set_option Elab.async false

sym_block run_b58 := exec b58 s58
sym_block run_b59 := exec b59 (frameS [(.r12, .ptr 0 4104), (.r14, .ptr 0 112)])
sym_block run_b60 := exec b60 (frameS [(.r12, .ptr 0 4104)])
sym_block run_b61 := exec b61 (frameS [(.r12, .ptr 0 4104), (.r15, .ptr 0 560)])
sym_block run_b62 := exec b62 (frameS [(.r15, .ptr 0 560), (.r14, .label "memcpy")])
sym_block run_b63 := exec b63 (frameS [(.r15, .ptr 0 560)])
sym_block run_b64 := exec b64 (frameS [])
sym_block run_b65 := exec b65 s65
sym_block run_b66 := exec b66 s66
sym_block run_b69 := exec b69 (after b66 s66)
sym_block run_b72 := exec b72 (after b69 (after b66 s66))
sym_block run_b73 := exec b73 (after b72 (after b69 (after b66 s66)))
sym_block run_b74 := exec b74 (after b73 (after b72 (after b69 (after b66 s66))))
sym_block run_b75 := exec b75 s75
sym_block run_b71 := exec b71 (after b75 s75)
sym_block run_b79 := exec b79 (after b71 (after b75 s75))
sym_block run_b80 := exec b80 s80
sym_block run_b83 := exec b83 (after b80 s80)
sym_block run_b84 := exec b84 (after b83 (after b80 s80))
sym_block run_b85 := exec b85 (after b84 (after b83 (after b80 s80)))
sym_block run_b86 := exec b86 s86
sym_block run_b82 := exec b82 (after b86 s86)
sym_block run_b90 := exec b90 (after b82 (after b86 s86))
sym_block run_b91 := exec b91 s91
sym_block run_b92 := exec b92 (after b91 s91)
sym_block run_b93 := exec b93 s91
sym_block run_b94 := exec b94 s91
sym_block run_b95 := exec b95 (frameS [])
sym_block run_b96 := exec b96 s96

end NativeRustcX64.SphincsVerifyProof.Fors
