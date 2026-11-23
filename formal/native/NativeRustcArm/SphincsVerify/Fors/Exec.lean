module

public import NativeRustcArm.Sym
public import NativeRustcArm.Code.Sphincs.SphincsVerify
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# The FORS region's blocks, run by the symbolic executor

The symbolic states the FORS proof starts blocks from and the executor's results (`run_*`). Most
blocks run in the frame (region 0, SP its base, `frameS`), with X29, the hashers' buffers (X21,
X22) and `136` (X20) known (`kept`); where the proof knows a hasher's `buf_len`, the start state
holds it as a literal write, so the executor folds the update loops' branches. Blocks that follow
one another without a call run on (`after`).

`b67` (a node's head) loads the two children through `csel`ed addresses (the current node's copy or
the path's node): it runs in five pieces, the two `ldp`s each in an environment whose one region
is the 16 bytes the address register points to (`ldS`). `b93` stores the tree's root at
`27808 + 16 c`: its `stp` runs alone likewise.
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
  [(.X29, .ptr 0 29280), (.X21, .ptr 0 16600), (.X22, .ptr 0 26968), (.X20, .lit 136)]

/-- The frame (region 0), SP its base, the registers `k` and `kept`, the bounds `bs`. -/
def frameS (k : List (XReg × Sym)) (bs : List (Sym × Nat) := []) : SState :=
  init [(29376, true)] (.ptr 0 0) (k ++ kept) [] bs

/-- A literal 64-bit word in the frame. -/
def litW (off v : Nat) : Write := ⟨0, off, 8, .lit v⟩

/-- The 16 bytes register `x` points to, region 0. -/
def ldS (x : XReg) : SState := init [(16, false)] .sp [(x, .ptr 0 0)]

/-- `0x03000000`: the type `FORS_TREE`'s word. -/
def typeW : Nat := 50331648

/-! ## The states -/

/-- At `b59`: the leaves' copy, hasher A, the hashes' scratch. -/
def s59 : SState :=
  init [(29376, true)] (.ptr 0 0)
    [(.X29, .ptr 0 29280), (.X24, .ptr 0 25752), (.X21, .ptr 0 16400), (.X23, .ptr 0 21648)]

/-- At `b60` (a tree's head): X19 the tree (below 24), the leaves, the signature, `176`. -/
def s60 : SState :=
  frameS [(.X24, .ptr 0 25752), (.X9, .ptr 0 8244), (.X8, .lit 176), (.X23, .ptr 0 21648),
    (.X25, .lit typeW)] [(.reg .X19, 24)]

/-- After a call: the frame only. -/
def s0 : SState := frameS []

/-- At `b67` (a node's head), its first piece. -/
def s67 : SState := frameS [(.X23, .ptr 0 21648), (.X25, .lit typeW)]

/-- `b67`'s third piece: X11 and X0 as the first left them. -/
def s67c : SState := frameS [(.X11, .ptr 0 20480), (.X0, .ptr 0 16384), (.X23, .ptr 0 21648)]

/-- `b67`'s last piece. -/
def s67e : SState := frameS [(.X11, .ptr 0 22672), (.X23, .ptr 0 21648), (.X25, .lit typeW)]

/-- After `memset` of hasher A: its `buf_len` zero. -/
def s68 : SState := { frameS [] with mem := [litW 16736 0] }

/-- After the address's `memcpy`: X23, X24, X25 the loop's, `buf_len` 16. -/
def s76 : SState :=
  { frameS [(.X23, .ptr 0 23696), (.X24, .lit 32), (.X25, .lit 32)] with mem := [litW 16736 16] }

/-- After the clone: hasher B's `buf_len` 48. -/
def s80 : SState := { frameS [] with mem := [litW 27104 48] }

/-- After the children's `memcpy`: X23, X24, X26 the loop's, B's `buf_len` 48. -/
def s85 : SState :=
  { frameS [(.X23, .ptr 0 22672), (.X24, .lit 32), (.X26, .lit 32)] with mem := [litW 27104 48] }

/-- After the state's copy, and after the buffer's: X25 B's `buf_len`, 80. -/
def s89 : SState := frameS [(.X25, .lit 80)]

/-- `b93`'s last piece: the flags as the first piece left them. -/
def s93c : SState := frameS []

/-! ## The pieces of `b67` and `b93` -/

/-- `b67` up to the first `ldp`. -/
def b67a : List Directive := b67.take 18
/-- The first `ldp` (the left child). -/
def b67b : List Directive := (b67.drop 18).take 1
/-- Up to the second `ldp`. -/
def b67c : List Directive := (b67.drop 19).take 5
/-- The second `ldp` (the right child). -/
def b67d : List Directive := (b67.drop 24).take 1
/-- The rest, to `bl memset`. -/
def b67e : List Directive := b67.drop 25

/-- `b93` up to the `stp` of the root. -/
def b93a : List Directive := b93.take 8
/-- The `stp`. -/
def b93b : List Directive := (b93.drop 8).take 1
/-- The rest, to the branch back. -/
def b93c : List Directive := b93.drop 9

end

set_option Elab.async false

sym_block run_b59 := exec b59 s59
sym_block run_b60 := exec b60 s60
sym_block run_b61 := exec b61 s0
sym_block run_b62 := exec b62 s0
sym_block run_b63 := exec b63 s0
sym_block run_b64 := exec b64 s0
sym_block run_b65 := exec b65 s0
sym_block run_b66 := exec b66 s0
sym_block run_b67a := exec b67a s67
sym_block run_b67b := exec b67b (ldS .X8)
sym_block run_b67c := exec b67c s67c
sym_block run_b67d := exec b67d (ldS .X10)
sym_block run_b67e := exec b67e s67e
sym_block run_b68 := exec b68 s68
sym_block run_b71 := exec b71 (after b68 s68)
sym_block run_b73 := exec b73 (after b71 (after b68 s68))
sym_block run_b74 := exec b74 (after b73 (after b71 (after b68 s68)))
sym_block run_b75 := exec b75 (after b74 (after b73 (after b71 (after b68 s68))))
sym_block run_b76 := exec b76 s76
sym_block run_b72 := exec b72 (after b76 s76)
sym_block run_b79 := exec b79 (after b72 (after b76 s76))
sym_block run_b80 := exec b80 s80
sym_block run_b82 := exec b82 (after b80 s80)
sym_block run_b83 := exec b83 (after b82 (after b80 s80))
sym_block run_b84 := exec b84 (after b83 (after b82 (after b80 s80)))
sym_block run_b85 := exec b85 s85
sym_block run_b81 := exec b81 (after b85 s85)
sym_block run_b88 := exec b88 (after b81 (after b85 s85))
sym_block run_b89 := exec b89 s89
sym_block run_b90 := exec b90 (after b89 s89)
sym_block run_b91 := exec b91 s89
sym_block run_b92 := exec b92 s0
sym_block run_b93a := exec b93a s0
sym_block run_b93b := exec b93b (ldS .X8)
sym_block run_b93c := exec b93c s93c

end NativeRustcArm.SphincsVerifyProof.Fors
