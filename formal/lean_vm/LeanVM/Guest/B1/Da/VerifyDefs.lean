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
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_pad»
import LeanVM.Guest.Data.ValNames.«da_pad_loop0»
import LeanVM.Guest.Data.ValNames.«da_verify»
import LeanVM.Guest.Data.ValNames.«da_verify_loop0»
import LeanVM.Guest.Data.ValNames.«da_weights»
import LeanVM.Guest.StmtsAppend

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
  hasCall (loopPre fn) "da_verify_blob" [.n (val% «da_verify_loop0» "weights")] [.n (val% «da_verify_loop0» "b0"), .n (val% «da_verify_loop0» "b1")] &&
  isMul A (.n (val% «da_verify_loop0» "slot~0")) (.n (val% «da_verify_loop0» "xi")) (.n (val% «da_verify_loop0» "xi")) && isMul A (.n (val% «da_verify_loop0» "slot")) (.n (val% «da_verify_loop0» "roots")) (.n (val% «da_verify_loop0» "slot~0")) &&
  A.any (isLoadAt (.n (val% «da_verify_loop0» "b0")) (.n (val% «da_verify_loop0» "slot")) 0) && A.any (isLoadAt (.n (val% «da_verify_loop0» "b1")) (.n (val% «da_verify_loop0» "slot")) 1)

/-- `da_pad_loop0`: the padding blob root's cells at `roots·n_blob²·x²`. -/
def padLOk (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn name% «da_pad_loop0» && decide (fn.params.length = 4) &&
  isMul A (.n (val% «da_pad_loop0» "pad~0")) (.n (val% «da_pad_loop0» "n_blob_g")) (.n (val% «da_pad_loop0» "n_blob_g")) && isMul A (.n (val% «da_pad_loop0» "pad~1")) (.n (val% «da_pad_loop0» "roots")) (.n (val% «da_pad_loop0» "pad~0")) && isMul A (.n (val% «da_pad_loop0» "pad~2")) (.n (val% «da_pad_loop0» "xd")) (.n (val% «da_pad_loop0» "xd")) &&
  isMul A (.n (val% «da_pad_loop0» "pad")) (.n (val% «da_pad_loop0» "pad~1")) (.n (val% «da_pad_loop0» "pad~2")) &&
  hasAtom A (.const (.n (val% «da_pad_loop0» "s1#0")) (word 8002054802297438051 4108169256045952147)) &&
  A.any (isLoadAt (.n (val% «da_pad_loop0» "s1#0")) (.n (val% «da_pad_loop0» "pad")) 0) &&
  hasAtom A (.const (.n (val% «da_pad_loop0» "s2#0")) (word 12830724869163462953 1721925254677230945)) &&
  A.any (isLoadAt (.n (val% «da_pad_loop0» "s2#0")) (.n (val% «da_pad_loop0» "pad")) 1)

/-- `da_pad(roots, n_blob, gap)`'s body: the padding loop from `1` while `gap ≠ 1`. -/
def dpadBody : List Stmt :=
  [.atom (.const (.n (val% «da_pad» "s0#0")) (word 1 0)), .atom (.add (.n (val% «da_pad» "s0#1")) (.n (val% «da_pad» "s0#0")) (.n (val% «da_pad» "gap_g"))), .atom (.const (.n (val% «da_pad» "s0#2")) (word 1 0)),
    .callIf (.n (val% «da_pad» "s0#1")) name% «da_pad_loop0» [.n (val% «da_pad» "s0#2"), .n (val% «da_pad» "gap_g"), .n (val% «da_pad» "roots"), .n (val% «da_pad» "n_blob_g")], .ret []]

/-- `da_pad`, checked. -/
def dpadOk (fn : Fn) : Bool := decide (fn.params = [.n (val% «da_pad» "roots"), .n (val% «da_pad» "n_blob_g"), .n (val% «da_pad» "gap_g")]) && stmtsEqb fn.body dpadBody

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
def wsOff (h : ℕ) : V := if h = 0 then .n (val% «da_weights» "offsets") else .n (4 * h + 5)

/-- Column `h`'s leaf of the tree above, as `da_weights` loads it. -/
def wsLeaf (h : ℕ) : V := if h = 0 then .n (val% «da_weights» "s1.u0.s0#1") else .n (4 * h + 3)

/-- `da_weights`' block (its body but the final `ret`). -/
noncomputable def wsP : List Stmt := (Fn.body fn% «da_weights»).dropLast

/-- **`da_weights(top_leaves, cell_factors, zs, offsets)`, checked**: its buffer `weights` (`.n 4`),
then per column `h < 128` the leaf `top_leaves[h]` (`wsLeaf h`), the offsets' pointer
`wsOff h = wsOff (h-1)·g^7`, `da_expand__L6_L7` on them, its result at `weights[h]`. -/
noncomputable def wsOk : Bool :=
  let P := wsP
  let A := atomsIn P
  decide ((fn% «da_weights»).params = [.n (val% «da_weights» "top_leaves"), .n (val% «da_weights» "cell_factors"), .n (val% «da_weights» "zs"), .n (val% «da_weights» "offsets")]) &&
  stmtsEqb (Fn.body fn% «da_weights») (P ⧺ [.ret [.n (val% «da_weights» "s2#0")]]) && P.all Stmt.flat &&
  A.any (isCopyAt (.n (val% «da_weights» "s2#0")) (.n (val% «da_weights» "weights"))) &&
  (List.range 128).all fun h =>
    hasCall P "da_expand__L6_L7" [wsLeaf h, .n (val% «da_weights» "cell_factors"), .n (val% «da_weights» "zs"), wsOff h] [.n (4 * h + 6)] &&
    A.any (isLoadAt (wsLeaf h) (.n (val% «da_weights» "top_leaves")) h) && A.any (isLoadAt (.n (4 * h + 6)) (.n (val% «da_weights» "weights")) h) &&
    (h == 0 || (A.any (isConstAt (.n (4 * h + 4)) 128 0) && isMul A (wsOff h) (wsOff (h - 1)) (.n (4 * h + 4))))

/-! ## The body -/

/-- `da_verify`'s block (its body but the final `ret`). -/
noncomputable def dvP : List Stmt := (Fn.body fn% «da_verify»).dropLast

/-- **`da_verify`'s block, checked.** -/
noncomputable def dvOk : Bool :=
  let P := dvP
  let A := atomsIn P
  decide ((fn% «da_verify»).params = [.n (val% «da_verify» "byte_bits")]) &&
  stmtsEqb (Fn.body fn% «da_verify») (P ⧺ [.ret [.n (val% «da_verify» "s11#0"), .n (val% «da_verify» "s11#0[1]"), .n (val% «da_verify» "s11#0[2]")]]) &&
  P.all Stmt.flat &&
  hasCall P "da_padding" [.n (val% «da_verify» "n_blob_g")] [.n (val% «da_verify» "gap_g")] &&
  hasCall P "da_vector" [.n (val% «da_verify» "z")] [.n (val% «da_verify» "zs"), .n (val% «da_verify» "top_leaves"), .n (val% «da_verify» "cell_factors"), .n (val% «da_verify» "offsets")] &&
  hasCall P "da_weights" [.n (val% «da_verify» "top_leaves"), .n (val% «da_verify» "cell_factors"), .n (val% «da_verify» "zs"), .n (val% «da_verify» "offsets")] [.n (val% «da_verify» "weights")] &&
  guardOk P (.n (val% «da_verify» "s6#1")) name% «da_verify_loop0» (.n (val% «da_verify» "s6#2")) (.n (val% «da_verify» "n_blob_g")) [.n (val% «da_verify» "weights"), .n (val% «da_verify» "roots")] &&
  hasCall P "da_pad" [.n (val% «da_verify» "roots"), .n (val% «da_verify» "n_blob_g"), .n (val% «da_verify» "gap_g")] [] &&
  hasCall P dlTop [.n (val% «da_verify» "roots")] [.n (val% «da_verify» "r0"), .n (val% «da_verify» "r1")] &&
  isMul A (.n (val% «da_verify» "s10#0")) (.n (val% «da_verify» "byte_bits")) (.n (val% «da_verify» "n_blob_g")) && A.any (isLoadAt (.n (val% «da_verify» "s10#1")) (.n (val% «da_verify» "s10#0")) 0) &&
  A.any (isConstAt (.n (val% «da_verify» "s10#2[1]")) 0 0) && pairHashVOk A (.n (val% «da_verify» "r0")) (.n (val% «da_verify» "r1")) (.n (val% «da_verify» "s10#1")) (.n (val% «da_verify» "s10#2[1]")) (.n (val% «da_verify» "commitment[0]")) (.n (val% «da_verify» "commitment[1]")) &&
  A.any (isCopyAt (.n (val% «da_verify» "s11#0")) (.n (val% «da_verify» "commitment[0]"))) && A.any (isCopyAt (.n (val% «da_verify» "s11#0[1]")) (.n (val% «da_verify» "commitment[1]"))) &&
  A.any (isCopyAt (.n (val% «da_verify» "s11#0[2]")) (.n (val% «da_verify» "z")))

end
end LeanVM.Guest.B1.Da
