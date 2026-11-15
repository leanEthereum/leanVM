/-
  LeanVM.Guest.B1.Da.VerifyDefs

  The checks of `da_verify`'s body, of its loops and of the roots' tree's (G:4516-4561).
-/

module

public import LeanVM.Guest.B1.Da.BlobDefs
public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.Data.NameStrings

/-!
# `da_verify` (G:4516-4561), checked

`da_verify(g_squares)`: the shape (`g_log_pad = g^L`, `L ≤ 10`, by a range check, then
`da_row_shape`), the hinted challenge `z`, the dual codeword's builders (`da_vector`), the columns'
weights (`da_weights`, unrolled: `weights[h]` is `da_expand__L7_L8` from the column's leaf of the tree
above, its factors shifted by the column's offsets), the blobs (`da_verify_loop0`: `da_verify_blob`
on the weights, its root at `roots·x²`), and the tree over the blob roots and the padding blob roots
(`da_roots_tree__L{k}` dispatched on `g_log_pad`: `da_pad`, whose loop `da_pad_loop0` writes
`DA_PAD_BLOB` at `roots·n_blob²·x²`, then `da_levels`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-- The atom `a` is in the list. -/
def hasAtom (A : List Atom) (a : Atom) : Bool := A.any (atomEqb · a)

theorem hasAtom_sound {rd : Reader} {σ : Val} {A : List Atom} {a : Atom} (h : hasAtom A a = true)
    (hat : ∀ b ∈ A, b.Holds rd σ) : a.Holds rd σ := by
  obtain ⟨b, hb, he⟩ := List.any_eq_true.mp h
  rw [← atomEqb_sound he]
  exact hat b hb

/-- `da_levels`' specializations, by `k`. -/
def dlNames : List String := (List.range 11).map daLevelsName

/-- The roots' tree's arm `da_roots_tree__L{k}`. -/
def rtName (k : ℕ) : String :=
  ["da_roots_tree__L0", "da_roots_tree__L1", "da_roots_tree__L2", "da_roots_tree__L3",
    "da_roots_tree__L4", "da_roots_tree__L5", "da_roots_tree__L6", "da_roots_tree__L7",
    "da_roots_tree__L8", "da_roots_tree__L9", "da_roots_tree__L10"].getD k ""

/-- The roots' tree's arms, by `k`. -/
def rtNames : List String := (List.range 11).map rtName

/-! ## The loops -/

/-- `da_verify_loop0`: blob `x`, `da_verify_blob` on the weights, its root at `roots·x²`. -/
def bOk (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn name% «da_verify_loop0» && decide (fn.params.length = 4) &&
  hasCall (loopPre fn) "da_verify_blob" [.n 2] [.n 4, .n 5] &&
  isMul A (.n 6) (.n 0) (.n 0) && isMul A (.n 7) (.n 3) (.n 6) &&
  A.any (isLoadAt (.n 4) (.n 7) 0) && A.any (isLoadAt (.n 5) (.n 7) 1)

/-- `da_pad_loop0`: the padding blob root's cells at `roots·n_blob²·x²`. -/
def padLOk (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn name% «da_pad_loop0» && decide (fn.params.length = 4) &&
  isMul A (.n 4) (.n 3) (.n 3) && isMul A (.n 5) (.n 2) (.n 4) && isMul A (.n 6) (.n 0) (.n 0) &&
  isMul A (.n 7) (.n 5) (.n 6) &&
  hasAtom A (.const (.n 8) (word 8002054802297438051 4108169256045952147)) &&
  A.any (isLoadAt (.n 8) (.n 7) 0) &&
  hasAtom A (.const (.n 9) (word 12830724869163462953 1721925254677230945)) &&
  A.any (isLoadAt (.n 9) (.n 7) 1)

/-- `da_pad(roots, n_blob, gap)`'s body: the padding loop from `1` while `gap ≠ 1`. -/
def padBody : List Stmt :=
  [.atom (.const (.n 3) (word 1 0)), .atom (.add (.n 4) (.n 3) (.n 2)), .atom (.const (.n 5) (word 1 0)),
    .callIf (.n 4) name% «da_pad_loop0» [.n 5, .n 2, .n 0, .n 1], .ret []]

/-- `da_pad`, checked. -/
def padOk (fn : Fn) : Bool := decide (fn.params = [.n 0, .n 1, .n 2]) && stmtsEqb fn.body padBody

/-- `da_roots_tree__L{k}(roots, n_blob, gap)`'s body: the padding, then the tree over `2^k` roots. -/
def rtBody (k : ℕ) : List Stmt :=
  [.call "da_pad" [.n 0, .n 1, .n 2] [], .call (daLevelsName k) [.n 0] [.n 3, .n 4],
    .atom (.copy (.n 5) (.n 3)), .atom (.copy (.n 6) (.n 4)), .ret [.n 5, .n 6]]

/-- The roots' tree's arm `k`, checked. -/
def rtOk (k : ℕ) (fn : Fn) : Bool := decide (fn.params = [.n 0, .n 1, .n 2]) && stmtsEqb fn.body (rtBody k)

/-! ## The weights -/

/-- The offsets' pointer `da_weights` passes to column `h`'s expansion: `offsets·g^(8h)`. -/
def wsOff (h : ℕ) : V := if h = 0 then .n 3 else .n (4 * h + 5)

/-- Column `h`'s leaf of the tree above, as `da_weights` loads it. -/
def wsLeaf (h : ℕ) : V := if h = 0 then .n 5 else .n (4 * h + 3)

/-- `da_weights`' block (its body but the final `ret`). -/
noncomputable def wsP : List Stmt := (Fn.body fn% «da_weights»).dropLast

/-- **`da_weights(top_leaves, cell_factors, zs, offsets)`, checked**: its buffer `weights` (`.n 4`),
then per column `h < 128` the leaf `top_leaves[h]` (`wsLeaf h`), the offsets' pointer
`wsOff h = wsOff (h-1)·g^8`, `da_expand__L7_L8` on them, its result at `weights[h]`. -/
noncomputable def wsOk : Bool :=
  let P := wsP
  let A := atomsIn P
  decide ((fn% «da_weights»).params = [.n 0, .n 1, .n 2, .n 3]) &&
  stmtsEqb (Fn.body fn% «da_weights») (P ++ [.ret [.n 515]]) && P.all Stmt.flat &&
  A.any (isCopyAt (.n 515) (.n 4)) &&
  (List.range 128).all fun h =>
    hasCall P "da_expand__L7_L8" [wsLeaf h, .n 1, .n 2, wsOff h] [.n (4 * h + 6)] &&
    A.any (isLoadAt (wsLeaf h) (.n 0) h) && A.any (isLoadAt (.n (4 * h + 6)) (.n 4) h) &&
    (h == 0 || (A.any (isConstAt (.n (4 * h + 4)) 256 0) && isMul A (wsOff h) (wsOff (h - 1)) (.n (4 * h + 4))))

/-! ## The body -/

/-- `da_verify`'s block (its body but the final `ret`). -/
noncomputable def dvP : List Stmt := (Fn.body fn% «da_verify»).dropLast

/-- **`da_verify`'s block, checked.** -/
noncomputable def dvOk : Bool :=
  let P := dvP
  let A := atomsIn P
  decide ((fn% «da_verify»).params = [.n 0]) &&
  stmtsEqb (Fn.body fn% «da_verify») (P ++ [.ret [.n 23, .n 24, .n 25]]) &&
  P.all Stmt.flat &&
  rcConstOk A (.n 2) 1024 &&
  hasCall P "da_row_shape" [.n 1, .n 2, .n 0] [.n 7, .n 8] &&
  hasCall P "da_vector" [.n 9] [.n 10, .n 11, .n 12, .n 13] &&
  hasCall P "da_weights" [.n 11, .n 12, .n 10, .n 13] [.n 14] &&
  guardOk P (.n 19) name% «da_verify_loop0» (.n 20) (.n 1) [.n 14, .n 17] &&
  P.any (stmtEqb · (.dispatch (.n 2) rtNames [.n 17, .n 1, .n 8] [.n 21, .n 22])) &&
  A.any (isCopyAt (.n 23) (.n 21)) && A.any (isCopyAt (.n 24) (.n 22)) &&
  A.any (isCopyAt (.n 25) (.n 9))

end
end LeanVM.Guest.B1.Da
