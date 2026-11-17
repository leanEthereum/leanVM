/-
  LeanVM.Guest.B1.Da.VerifyDefs

  The checks of `da_verify`'s body, of its loops and of `da_pad`'s.
-/

module

public import LeanVM.Guest.B1.Da.BlobDefs
public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# `da_verify`, checked

`da_verify(byte_bits)`: the blob count and the padding rows' (`da_padding`), the hinted challenge
`z`, the dual codeword's builders (`da_vector`), the columns' weights (`da_weights`, unrolled:
`weights[h]` is `da_expand__L6_L7` from the column's leaf of the tree above, its factors shifted by
the column's offsets), the blobs (`da_verify_loop0`: `da_verify_blob` on the weights, its root at
`roots·x²`), the padding blobs (`da_pad`, whose loop `da_pad_loop0` writes `DA_PAD_BLOB` at
`roots·n_blob²·x²`), the tree over the `DA_MAX_ROWS` blob roots (`dlTop`), and its root hashed with
the count's word, read at `byte_bits·n_blob` (`pairHashVOk`).
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

/-- `da_levels`' specialization at the tree over the `DA_MAX_ROWS` blob roots. -/
def dlTop : String := daLevelsName (guest_const% DA_LOG_MAX_ROWS)

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
def dpadBody : List Stmt :=
  [.atom (.const (.n 3) (word 1 0)), .atom (.add (.n 4) (.n 3) (.n 2)), .atom (.const (.n 5) (word 1 0)),
    .callIf (.n 4) name% «da_pad_loop0» [.n 5, .n 2, .n 0, .n 1], .ret []]

/-- `da_pad`, checked. -/
def dpadOk (fn : Fn) : Bool := decide (fn.params = [.n 0, .n 1, .n 2]) && stmtsEqb fn.body dpadBody

/-- `keccak([a, b], [c, d])`, its digest's two cells `o0`, `o1`. -/
def pairHashVOk (atoms : List Atom) (a b c d o0 o1 : V) : Bool :=
  (pairSpec a b c d atoms).check atoms &&
    decide ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) 0 = o0) &&
    decide ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) 1 = o1)

theorem pairHashV_sound {rd : Reader} {σ : Val} {atoms : List Atom} {a b c d o0 o1 : V}
    (h : pairHashVOk atoms a b c d o0 o1 = true) (hat : ∀ x ∈ atoms, x.Holds rd σ) :
    (σ o0, σ o1) = digestHalves (keccak256 (cellsBytes [σ a, σ b, σ c, σ d])) := by
  simp only [pairHashVOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, rfl⟩, rfl⟩ := h
  have hd := chain_final hc rfl hat (pre := []) (n := 0) rfl
    (fun c => (cellsOfState_zero false c).symm)
  have hv : ((pairSpec a b c d atoms).vals σ).take ((pairSpec a b c d atoms).len / 16) =
      [σ a, σ b, σ c, σ d] := by simp [pairSpec, ChainSpec.vals, srcVal]
  rw [hv, List.nil_append] at hd
  exact hd

/-! ## The weights -/

/-- The offsets' pointer `da_weights` passes to column `h`'s expansion: `offsets·g^(7h)`. -/
def wsOff (h : ℕ) : V := if h = 0 then .n 3 else .n (4 * h + 5)

/-- Column `h`'s leaf of the tree above, as `da_weights` loads it. -/
def wsLeaf (h : ℕ) : V := if h = 0 then .n 5 else .n (4 * h + 3)

/-- `da_weights`' block (its body but the final `ret`). -/
noncomputable def wsP : List Stmt := (Fn.body fn% «da_weights»).dropLast

/-- **`da_weights(top_leaves, cell_factors, zs, offsets)`, checked**: its buffer `weights` (`.n 4`),
then per column `h < 128` the leaf `top_leaves[h]` (`wsLeaf h`), the offsets' pointer
`wsOff h = wsOff (h-1)·g^7`, `da_expand__L6_L7` on them, its result at `weights[h]`. -/
noncomputable def wsOk : Bool :=
  let P := wsP
  let A := atomsIn P
  decide ((fn% «da_weights»).params = [.n 0, .n 1, .n 2, .n 3]) &&
  stmtsEqb (Fn.body fn% «da_weights») (P ++ [.ret [.n 515]]) && P.all Stmt.flat &&
  A.any (isCopyAt (.n 515) (.n 4)) &&
  (List.range 128).all fun h =>
    hasCall P "da_expand__L6_L7" [wsLeaf h, .n 1, .n 2, wsOff h] [.n (4 * h + 6)] &&
    A.any (isLoadAt (wsLeaf h) (.n 0) h) && A.any (isLoadAt (.n (4 * h + 6)) (.n 4) h) &&
    (h == 0 || (A.any (isConstAt (.n (4 * h + 4)) 128 0) && isMul A (wsOff h) (wsOff (h - 1)) (.n (4 * h + 4))))

/-! ## The body -/

/-- `da_verify`'s block (its body but the final `ret`). -/
noncomputable def dvP : List Stmt := (Fn.body fn% «da_verify»).dropLast

/-- **`da_verify`'s block, checked.** -/
noncomputable def dvOk : Bool :=
  let P := dvP
  let A := atomsIn P
  decide ((fn% «da_verify»).params = [.n 0]) &&
  stmtsEqb (Fn.body fn% «da_verify») (P ++ [.ret [.n 26, .n 27, .n 28]]) &&
  P.all Stmt.flat &&
  hasCall P "da_padding" [.n 1] [.n 2] &&
  hasCall P "da_vector" [.n 3] [.n 4, .n 5, .n 6, .n 7] &&
  hasCall P "da_weights" [.n 5, .n 6, .n 4, .n 7] [.n 8] &&
  guardOk P (.n 12) name% «da_verify_loop0» (.n 13) (.n 1) [.n 8, .n 10] &&
  hasCall P "da_pad" [.n 10, .n 1, .n 2] [] &&
  hasCall P dlTop [.n 10] [.n 14, .n 15] &&
  isMul A (.n 16) (.n 0) (.n 1) && A.any (isLoadAt (.n 17) (.n 16) 0) &&
  A.any (isConstAt (.n 19) 0 0) && pairHashVOk A (.n 14) (.n 15) (.n 17) (.n 19) (.n 24) (.n 25) &&
  A.any (isCopyAt (.n 26) (.n 24)) && A.any (isCopyAt (.n 27) (.n 25)) &&
  A.any (isCopyAt (.n 28) (.n 3))

end
end LeanVM.Guest.B1.Da
