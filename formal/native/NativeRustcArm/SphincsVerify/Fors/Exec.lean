module

public import NativeRustcArm.Sym
public import NativeRustcArm.Code.Sphincs.SphincsVerify
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# The FORS region's blocks, run by the symbolic executor

The symbolic states the FORS proof starts blocks from and the executor's results (`run_*`). Most
blocks run in the frame (region 0, SP its base, `frameS`), with X29, the hashers' buffers (X26,
X22) and `136` (X28) known (`kept`); where the proof knows a hasher's `buf_len`, the start state
holds it as a literal write, so the executor folds the update loops' branches. Blocks that follow
one another without a call run on (`after`).

`b58` (a node's head) loads the two children through `csel`ed addresses (the current node's copy or
the path's node): it runs in five pieces, the two `ldp`s each in an environment whose one region
is the 16 bytes the address register points to (`ldS`). `b84` stores the tree's root at
`20064 + 16 c`: its `stp` runs alone likewise.
-/

namespace NativeRustcArm.SphincsVerifyProof.Fors

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

/-- The registers FORS keeps: X29 the saved registers, the hashers' buffers, `136`. -/
def kept : List (XReg × Sym) :=
  [(.X29, .ptr 0 21520), (.X26, .ptr 0 8840), (.X22, .ptr 0 19208), (.X28, .lit 136)]

/-- The frame (region 0), SP its base, the registers `k` and `kept`, the bounds `bs`. -/
def frameS (k : List (XReg × Sym)) (bs : List (Sym × Nat) := []) : SState :=
  init [(21616, true)] (.ptr 0 0) (k ++ kept) [] bs

/-- A literal 64-bit word in the frame. -/
def litW (off v : Nat) : Write := ⟨0, off, 8, .lit v⟩

/-- The 16 bytes register `x` points to, region 0. -/
def ldS (x : XReg) : SState := init [(16, false)] .sp [(x, .ptr 0 0)]

/-- `0x03000000`: the type `FORS_TREE`'s word. -/
def typeW : Nat := 50331648

/-! ## The states -/

/-- At `b50`: the leaves' copy, hasher A, the hashes' scratch. -/
def s50 : SState :=
  init [(21616, true)] (.ptr 0 0)
    [(.X29, .ptr 0 21520), (.X24, .ptr 0 17992), (.X20, .ptr 0 8640), (.X23, .ptr 0 15936)]

/-- At `b51` (a tree's head): X19 the tree (below 24), the leaves, the signature, `176`. -/
def s51 : SState :=
  frameS [(.X24, .ptr 0 17992), (.X9, .ptr 0 484), (.X8, .lit 176), (.X23, .ptr 0 15936),
    (.X10, .lit typeW)] [(.reg .X19, 24)]

/-- After a call: the frame only. -/
def s0 : SState := frameS []

/-- `b58`'s third piece: X11 and X0 as the first left them. -/
def s58c : SState := frameS [(.X11, .ptr 0 12288), (.X0, .ptr 0 8192)]

/-- `b58`'s last piece. -/
def s58e : SState := frameS [(.X11, .ptr 0 14912)]

/-- After `memset` of hasher A: its `buf_len` zero. -/
def s59 : SState := { frameS [] with mem := [litW 8976 0] }

/-- After the address's `memcpy`: X23, X24, X20 the loop's, `buf_len` 16. -/
def s67 : SState :=
  { frameS [(.X23, .ptr 0 15936), (.X24, .lit 32), (.X20, .lit 32)] with mem := [litW 8976 16] }

/-- After the clone: hasher B's `buf_len` 48. -/
def s71 : SState := { frameS [] with mem := [litW 19344 48] }

/-- After the children's `memcpy`: X23, X24, X20 the loop's, B's `buf_len` 48. -/
def s76 : SState :=
  { frameS [(.X23, .ptr 0 14912), (.X24, .lit 32), (.X20, .lit 32)] with mem := [litW 19344 48] }

/-- After the state's copy, and after the buffer's: X25 B's `buf_len`, 80. -/
def s80 : SState := frameS [(.X25, .lit 80)]

/-- `b84`'s last piece: the flags as the first piece left them. -/
def s84c : SState := frameS []

/-! ## The pieces of `b58` and `b84` -/

/-- `b58` up to the first `ldp`. -/
def b58a : List Directive := b58.take 18
/-- The first `ldp` (the left child). -/
def b58b : List Directive := (b58.drop 18).take 1
/-- Up to the second `ldp`. -/
def b58c : List Directive := (b58.drop 19).take 5
/-- The second `ldp` (the right child). -/
def b58d : List Directive := (b58.drop 24).take 1
/-- The rest, to `bl memset`. -/
def b58e : List Directive := b58.drop 25

/-- `b84` up to the `stp` of the root. -/
def b84a : List Directive := b84.take 8
/-- The `stp`. -/
def b84b : List Directive := (b84.drop 8).take 1
/-- The rest, to the branch back. -/
def b84c : List Directive := b84.drop 9

end

set_option Elab.async false

sym_block run_b50 := exec b50 s50
sym_block run_b51 := exec b51 s51
sym_block run_b52 := exec b52 s0
sym_block run_b53 := exec b53 s0
sym_block run_b54 := exec b54 s0
sym_block run_b55 := exec b55 s0
sym_block run_b56 := exec b56 s0
sym_block run_b57 := exec b57 s0
sym_block run_b58a := exec b58a s0
sym_block run_b58b := exec b58b (ldS .X8)
sym_block run_b58c := exec b58c s58c
sym_block run_b58d := exec b58d (ldS .X10)
sym_block run_b58e := exec b58e s58e
sym_block run_b59 := exec b59 s59
sym_block run_b62 := exec b62 (after b59 s59)
sym_block run_b64 := exec b64 (after b62 (after b59 s59))
sym_block run_b65 := exec b65 (after b64 (after b62 (after b59 s59)))
sym_block run_b66 := exec b66 (after b65 (after b64 (after b62 (after b59 s59))))
sym_block run_b67 := exec b67 s67
sym_block run_b63 := exec b63 (after b67 s67)
sym_block run_b70 := exec b70 (after b63 (after b67 s67))
sym_block run_b71 := exec b71 s71
sym_block run_b73 := exec b73 (after b71 s71)
sym_block run_b74 := exec b74 (after b73 (after b71 s71))
sym_block run_b75 := exec b75 (after b74 (after b73 (after b71 s71)))
sym_block run_b76 := exec b76 s76
sym_block run_b72 := exec b72 (after b76 s76)
sym_block run_b79 := exec b79 (after b72 (after b76 s76))
sym_block run_b80 := exec b80 s80
sym_block run_b81 := exec b81 (after b80 s80)
sym_block run_b82 := exec b82 s80
sym_block run_b83 := exec b83 s0
sym_block run_b84a := exec b84a s0
sym_block run_b84b := exec b84b (ldS .X8)
sym_block run_b84c := exec b84c s84c

end NativeRustcArm.SphincsVerifyProof.Fors
