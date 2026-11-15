/-
  LeanVM.Guest.B1.Sig.XmssT

  The body of `verify_lean_xmss` as a template, written from the guest's structure
  (`lean_ethereum.py`) with the values numbered as the renumbered expansion numbers them.
-/

module

public import LeanVM.Guest.B1.Sig.WotsT

/-!
# `verify_lean_xmss` as a template

* `xPrologue`: `pp`, the leaf index's 32 bits pinned Boolean, the node indices `xNode l`
  (`shifts`), the powers `g^s` (`xPower s`, `s < 10`) and the chain indices `xTag i` (`i < 58`);
* `xWots`: the chain step, a 64-byte `keccak` of `P`, the step's address, the value and the chain
  index, into its slot of `walks`; the codeword is `codewordT` over it (19 groups and the last
  chain), the paths `merkleT`;
* `xDigest0`, `xDigest1`: the layers' message digests; `xLayer`, `xBody`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-- The padding run of `verify_lean_xmss`, set by the bottom layer's message digest. -/
def xPad : Nat := 206

def xNode (l : Nat) : V := .n (34 + 3 * (31 - l))
def xBit (l : Nat) : V := .n (2 + l)
def xPower (s : Nat) : V := .n (128 + s)
def xTag (i : Nat) : V := .n (138 + i)

/-- `g^106`, the leanXMSS target sum in the exponent. -/
def xTarget : E := word 118747255799808 0

/-- The prologue (`lean_ethereum.py`). -/
def xPrologue : List Stmt :=
  [loadS (.n 1) (.n 0) 1, hintW "leaf_index_bits" (runV 2 32)] ++ booleans 2 32 ++ shifts 2 32 34 ++
    (List.range 10).map (fun s => cst (128 + s) (word (2 ^ s) 0)) ++
    (List.range 58).map (fun i => cst (138 + i) (word i 0))

/-- leanXMSS's chain step: `keccak([P, steps s], [v, i], walks[o:o + 1])` (`walk`,
`lean_ethereum.py`), its constant at `c`. -/
def xWots (steps : Nat → V) : WotsT where
  step i s v c o := k64 xPad (.n 1) (steps s) v (xTag i) c o
  size := 1
  power := xPower

/-- The bottom layer's message digest from base `b`: `D = Th(P, A_msg, M | ρ)`, 80 bytes, one
block; it sets the padding run at `b + 10`. -/
def xDigest0 (b : Nat) : List Stmt :=
  [hintW "randomizer" [.n b], cst (b + 1) (word (tw 12) 0), addS (.n (b + 2)) (xNode 0) (.n (b + 1)),
    loadS (.n (b + 3)) (.n 0) 2, loadS (.n (b + 4)) (.n 0) 3, copyS (.n (b + 5)) (.n b),
    cst (b + 6) (word 1 0), cst (b + 7) (word 0 0), cst (b + 8) (word 0 0),
    cst (b + 9) (word (2 ^ 63) 0)] ++
  (List.range 5).map (fun k => cst (b + 10 + k) (word (if k = 0 then 1 else 0) 0)) ++
  [kecS [.n 1, .n (b + 2), .n (b + 3), .n (b + 4), .n (b + 5), .n (b + 6), .n (b + 7), .n (b + 8),
    .n (b + 9), .n (b + 11), .n (b + 12), .n (b + 13), .n (b + 14)] (runV (b + 15) 1) false false]

/-- The top layer's index and message digest from base `b`, over the bottom root `root`. -/
def xDigest1 (b : Nat) (root : V) : List Stmt :=
  [cst b (word lxTop 0), addS (.n (b + 1)) (xNode 16) (.n b), hintW "randomizer" [.n (b + 2)],
    cst (b + 3) (word (tw 12) 0), addS (.n (b + 4)) (.n (b + 1)) (.n (b + 3))] ++
  k64 xPad (.n 1) (.n (b + 4)) root (.n (b + 2)) (b + 5) (b + 6)

/-- The three step addresses from base `b`, at `n(b + 2s + 1)`. -/
def xStepAddrs (idx : V) (b : Nat) : List Stmt :=
  (List.range 3).flatMap fun s =>
    [cst (b + 2 * s) (word (tw 1 + s * stepMul) 0), addS (.n (b + 2 * s + 1)) idx (.n (b + 2 * s))]

/-! ## A layer -/

def xA (layer b : Nat) : Nat := if layer = 0 then b + 16 else b + 7
def xIdx (layer b : Nat) : V := if layer = 0 then xNode 0 else .n (b + 1)
def xD0 (layer b : Nat) : V := if layer = 0 then .n (b + 15) else .n (b + 6)
def xRho (layer b : Nat) : V := if layer = 0 then .n b else .n (b + 2)
def xW (layer b : Nat) : WotsT := xWots fun s => .n (xA layer b + 2 * s + 1)
def xCw (layer b : Nat) : List Stmt × Nat × List V :=
  codewordT (xW layer b) 19 xTarget (xD0 layer b) (xA layer b + 6)
def xLeafCells (layer b : Nat) : List V := V.n 1 :: V.n ((xCw layer b).2.1 + 1) :: (xCw layer b).2.2
def xLeafK (layer b : Nat) : List Stmt × Nat × Nat :=
  kMsg xPad ((xLeafCells layer b).map KC.cell) 960 false none ((xCw layer b).2.1 + 2)
def xNodeOf (layer l : Nat) : Option V :=
  if 16 * layer + l + 1 = 32 then none else some (xNode (16 * layer + l + 1))
def xBitOf (layer l : Nat) : V := xBit (16 * layer + l)
def xAddrOf (layer l : Nat) : Nat := tw 3 + (l + 1) * hiMul + layer * lxTop
def xMk (layer b : Nat) : List Stmt × Nat × V :=
  merkleT xPad (.n 1) (xBitOf layer) (xNodeOf layer) (xAddrOf layer) 16 0 (.n (xLeafK layer b).2.2)
    (xLeafK layer b).2.1

/-- Layer `layer` from base `b`, over the bottom root `root` at the top: its message digest, its
step addresses, its codeword, its one-time leaf and its path; the statements, the next base and
its root. -/
def xLayer (layer b : Nat) (root : V) : List Stmt × Nat × V :=
  ((if layer = 0 then xDigest0 b else xDigest1 b root) ++ xStepAddrs (xIdx layer b) (xA layer b) ++
    (xCw layer b).1 ++ [cst (xCw layer b).2.1 (word (tw 2) 0),
      addS (.n ((xCw layer b).2.1 + 1)) (xIdx layer b) (.n (xCw layer b).2.1)] ++
    (xLeafK layer b).1 ++ (xMk layer b).1, (xMk layer b).2.1, (xMk layer b).2.2)

/-- The body of `verify_lean_xmss`. -/
def xBody : List Stmt :=
  let l0 := xLayer 0 196 (.n 0)
  let l1 := xLayer 1 l0.2.1 l0.2.2
  xPrologue ++ l0.1 ++ l1.1 ++
    [loadS (.n l1.2.1) (.n 0) 0, .atom (.assertEq l1.2.2 (.n l1.2.1)), .ret []]

end
end LeanVM.Guest.B1.Sig
