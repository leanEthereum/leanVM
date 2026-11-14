/-
  LeanVM.Guest.B1.Da.VerifyDefs

  The checks of `da_verify`'s body and of its loops.
-/

module

public import LeanVM.Guest.B1.Da.ColumnDefs
public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# `da_verify`, checked

`da_verify()`: the blob count and the padding rows' (`da_padding`), the hinted challenge `z`, the
dual codeword's builders (`da_vector`), the blobs' regions
(`da_verify_loop0`: `rowbase[x] = blobs·x^641`, the running sum's first word `0`), the columns
(`da_verify_loop1`: `da_verify_column` on columns `0 … 127`), each blob's sum checked and its tree's
root (`da_verify_loop2`: word `640` of the region is `0`, `da_levels__L128_L7`, the root at
`roots·x²`), the padding blobs (`da_verify_loop3`: `DA_PAD_BLOB` at `roots·n_blob²·x²`), and the
tree over the `DA_MAX_ROWS` blob roots (`dlTop`).
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

/-- `da_verify_loop0`: `rowbase[x] = blobs·x^641`, the region's word `512` zero. -/
def l17Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn name% «da_verify_loop0» && decide (fn.params.length = 4) &&
  monoIs A (.n 15) (.n 2) (.n 0) 641 && isMul A (.n 16) (.n 3) (.n 0) &&
  A.any (isLoadAt (.n 15) (.n 16) 0) && A.any (isConstAt (.n 17) 0 0) &&
  A.any (isLoadAt (.n 17) (.n 15) 512)

/-- The body of the column loop `da_verify_loop1`: the column at `x`, then the next. -/
def l18Body : List Stmt :=
  [.call "da_verify_column" ((List.range 7).map V.n) [],
    .atom (.const (.n 7) (word 2 0)), .atom (.mul (.n 8) (.n 0) (.n 7)),
    .atom (.const (.n 9) (word 325 0)), .atom (.add (.n 10) (.n 8) (.n 9)),
    .atom (.const (.n 11) (word 2 0)), .atom (.mul (.n 12) (.n 0) (.n 11)),
    .callIf (.n 10) name% «da_verify_loop1» (.n 12 :: (List.range 6).map fun k => V.n (k + 1)),
        .ret []]

/-- `da_verify_loop1`, checked. -/
def l18Ok (fn : Fn) : Bool :=
  decide (fn.params = (List.range 7).map V.n) && stmtsEqb fn.body l18Body

/-- `da_verify_loop2`: the region at `rowbase[x]` has the sum `0` at word `640`; its tree's root, at
`roots·x²`. -/
def l19Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn name% «da_verify_loop2» && decide (fn.params.length = 4) &&
  isMul A (.n 4) (.n 2) (.n 0) && A.any (isLoadAt (.n 5) (.n 4) 0) &&
  A.any (isLoadAt (.n 6) (.n 5) 640) && A.any (isConstAt (.n 7) 0 0) &&
  A.any (isAssertEqAt (.n 6) (.n 7)) &&
  hasCall (loopPre fn) "da_levels__L128_L7" [.n 5] [.n 8, .n 9] &&
  isMul A (.n 10) (.n 0) (.n 0) && isMul A (.n 11) (.n 3) (.n 10) &&
  A.any (isLoadAt (.n 8) (.n 11) 0) && A.any (isLoadAt (.n 9) (.n 11) 1)

/-- `da_verify_loop3`: the padding blob root's cells at `roots·n_blob²·x²`. -/
def l20Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn name% «da_verify_loop3» && decide (fn.params.length = 4) &&
  isMul A (.n 4) (.n 3) (.n 3) && isMul A (.n 5) (.n 2) (.n 4) && isMul A (.n 6) (.n 0) (.n 0) &&
  isMul A (.n 7) (.n 5) (.n 6) &&
  hasAtom A (.const (.n 8) (word 8002054802297438051 4108169256045952147)) &&
  A.any (isLoadAt (.n 8) (.n 7) 0) &&
  hasAtom A (.const (.n 9) (word 12830724869163462953 1721925254677230945)) &&
  A.any (isLoadAt (.n 9) (.n 7) 1)

/-! ## The body -/

/-- `da_verify`'s block (its body but the final `ret`). -/
noncomputable def dvP : List Stmt := (Fn.body fn% «da_verify»).dropLast

/-- **`da_verify`'s block, checked.** -/
noncomputable def dvOk : Bool :=
  let P := dvP
  let A := atomsIn P
  decide ((fn% «da_verify»).params = []) &&
  stmtsEqb (Fn.body fn% «da_verify») (P ++ [.ret [.n 34, .n 35, .n 36]]) &&
  P.all Stmt.flat &&
  hasCall P "da_padding" [.n 0] [.n 1] &&
  hasCall P "da_vector" [.n 2] [.n 3, .n 4, .n 5, .n 6] &&
  guardOk P (.n 21) name% «da_verify_loop0» (.n 22) (.n 0) [.n 18, .n 19] &&
  A.any (isConstAt (.n 23) 1 0) &&
  hasCall P name% «da_verify_loop1» [.n 23, .n 0, .n 19, .n 3, .n 4, .n 5, .n 6] [] &&
  guardOk P (.n 27) name% «da_verify_loop2» (.n 28) (.n 0) [.n 19, .n 25] &&
  guardOk P (.n 30) name% «da_verify_loop3» (.n 31) (.n 1) [.n 25, .n 0] &&
  hasCall P dlTop [.n 25] [.n 32, .n 33] &&
  A.any (isCopyAt (.n 34) (.n 32)) && A.any (isCopyAt (.n 35) (.n 33)) &&
  A.any (isCopyAt (.n 36) (.n 2))

end
end LeanVM.Guest.B1.Da
