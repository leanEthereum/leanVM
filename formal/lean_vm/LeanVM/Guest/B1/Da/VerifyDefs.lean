/-
  LeanVM.Guest.B1.Da.VerifyDefs

  The checks of `da_verify`'s body and of its loops (G:4323-4363).
-/

module

public import LeanVM.Guest.B1.Da.ColumnDefs
public import LeanVM.Guest.B1.Main.Body

/-!
# `da_verify` (G:4323-4363), checked

`da_verify(g_squares)` (`core27`): the shape (`da_row_shape`), the hinted challenge `z`, the dual
codeword's builders (`da_vector`), the blobs' regions
(`__loop21`: `rowbase[x] = blobs·x^641`, the running sum's first word `0`), the columns
(`__loop22`: `da_verify_column` on columns `0 … 127`), each blob's sum checked and its tree's
root (`__loop23`: word `640` of the region is `0`, `da_levels__L128_L7`, the root at
`roots·x²`), the padding blobs (`__loop24`: `DA_PAD_BLOB` at `roots·n_blob²·x²`), and the tree
over the blob roots (`da_levels` dispatched on `g_log_pad`).
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

/-! ## The loops -/

/-- `__loop21`: `rowbase[x] = blobs·x^641`, the region's word `512` zero. -/
def l17Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop21" && decide (fn.params.length = 4) &&
  monoIs A (.n 15) (.n 2) (.n 0) 641 && isMul A (.n 16) (.n 3) (.n 0) &&
  A.any (isLoadAt (.n 15) (.n 16) 0) && A.any (isConstAt (.n 17) 0 0) &&
  A.any (isLoadAt (.n 17) (.n 15) 512)

/-- The body of the column loop `__loop22`: the column at `x`, then the next. -/
def l18Body : List Stmt :=
  [.call "da_verify_column" ((List.range 7).map V.n) [],
    .atom (.const (.n 7) (word 2 0)), .atom (.mul (.n 8) (.n 0) (.n 7)),
    .atom (.const (.n 9) (word 325 0)), .atom (.add (.n 10) (.n 8) (.n 9)),
    .atom (.const (.n 11) (word 2 0)), .atom (.mul (.n 12) (.n 0) (.n 11)),
    .callIf (.n 10) "__loop22" (.n 12 :: (List.range 6).map fun k => V.n (k + 1)), .ret []]

/-- `__loop22`, checked. -/
def l18Ok (fn : Fn) : Bool :=
  decide (fn.params = (List.range 7).map V.n) && stmtsEqb fn.body l18Body

/-- `__loop23`: the region at `rowbase[x]` has the sum `0` at word `640`; its tree's root, at
`roots·x²`. -/
def l19Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop23" && decide (fn.params.length = 4) &&
  isMul A (.n 4) (.n 2) (.n 0) && A.any (isLoadAt (.n 5) (.n 4) 0) &&
  A.any (isLoadAt (.n 6) (.n 5) 640) && A.any (isConstAt (.n 7) 0 0) &&
  A.any (isAssertEqAt (.n 6) (.n 7)) &&
  hasCall (loopPre fn) "da_levels__L128_L7" [.n 5] [.n 8, .n 9] &&
  isMul A (.n 10) (.n 0) (.n 0) && isMul A (.n 11) (.n 3) (.n 10) &&
  A.any (isLoadAt (.n 8) (.n 11) 0) && A.any (isLoadAt (.n 9) (.n 11) 1)

/-- `__loop24`: the padding blob root's cells at `roots·n_blob²·x²`. -/
def l20Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop24" && decide (fn.params.length = 4) &&
  isMul A (.n 4) (.n 3) (.n 3) && isMul A (.n 5) (.n 2) (.n 4) && isMul A (.n 6) (.n 0) (.n 0) &&
  isMul A (.n 7) (.n 5) (.n 6) &&
  hasAtom A (.const (.n 8) (word 8002054802297438051 4108169256045952147)) &&
  A.any (isLoadAt (.n 8) (.n 7) 0) &&
  hasAtom A (.const (.n 9) (word 12830724869163462953 1721925254677230945)) &&
  A.any (isLoadAt (.n 9) (.n 7) 1)

/-! ## The body -/

/-- `da_verify`'s block (its body but the final `ret`). -/
noncomputable def dvP : List Stmt := (Fn.body Data.core27).dropLast

/-- **`da_verify`'s block, checked.** -/
noncomputable def dvOk : Bool :=
  let P := dvP
  let A := atomsIn P
  decide (Data.core27.params = [.n 0]) &&
  stmtsEqb (Fn.body Data.core27) (P ++ [.ret [.n 38, .n 39, .n 40]]) &&
  P.all Stmt.flat &&
  hasCall P "da_row_shape" [.n 1, .n 2, .n 0] [.n 3, .n 4] &&
  hasCall P "da_vector" [.n 5] [.n 6, .n 7, .n 8, .n 9] &&
  guardOk P (.n 24) "__loop21" (.n 25) (.n 1) [.n 21, .n 22] &&
  A.any (isConstAt (.n 26) 1 0) &&
  hasCall P "__loop22" [.n 26, .n 1, .n 22, .n 6, .n 7, .n 8, .n 9] [] &&
  monoIs A (.n 28) (.n 3) (.n 3) 3 &&
  guardOk P (.n 31) "__loop23" (.n 32) (.n 1) [.n 22, .n 29] &&
  guardOk P (.n 34) "__loop24" (.n 35) (.n 4) [.n 29, .n 1] &&
  P.any (stmtEqb · (.dispatch (.n 2) dlNames [.n 29] [.n 36, .n 37])) &&
  A.any (isCopyAt (.n 38) (.n 36)) && A.any (isCopyAt (.n 39) (.n 37)) &&
  A.any (isCopyAt (.n 40) (.n 5))

end
end LeanVM.Guest.B1.Da
