/-
  LeanVM.Guest.B1.VerifySub.NodeShapes

  Where `verify_sub`, `certify_placement` and `verify_tables` pop: their bodies' witness hints and noisy calls by position, every block between them free of witness hints, its callees passing `noWitness` (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Common.PopsSeg
public import LeanVM.Guest.B1.Common.NoWitMute
public import LeanVM.Guest.B1.Common.Basic
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«certify_placement»
import LeanVM.Guest.Data.ValNames.«verify_sub»
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The bodies' shapes

`segOk j l a n`: the block of `n` statements from position `a` of `l`, a body of function `j`, cannot return and passes `noWitBlock j`. `stmtAt l a s`: statement `a` of `l` is `s`.

* `verify_sub` (`vsShape_ok`): the stream's hint at `8`, the table logs' at `55`, `certify_placement` at `243`, `verify_tables` at `316`, the `open_stacked` dispatch at `1510`;
* `certify_placement` (`cpShape_ok`): the group order's hint at `135`;
* `verify_tables` (`vtShape_ok`): the block group order's hint at `17`, `zc_tau_max`'s at `2590`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1

@[expose] public section

/-- The block of `n` statements from `a` of function `j`'s body `l` cannot return and has no witness hint in its subtree. -/
noncomputable def segOk (j : ℕ) (l : List Stmt) (a n : ℕ) : Bool :=
  Stmt.noRetList ((l.drop a).take n) && noWitBlock j ((l.drop a).take n)

/-- Statement `a` of `l` is `s`. -/
def stmtAt (l : List Stmt) (a : ℕ) (s : Stmt) : Bool := stmtsEqb ((l.drop a).take 1) [s]

theorem stmtAt_sound {l : List Stmt} {a : ℕ} {s : Stmt} (h : stmtAt l a s = true) : l[a]? = some s := by
  have e := congrArg (·[0]?) (stmtsEqb_sound h)
  simpa [List.getElem?_take, List.getElem?_drop] using e

/-- The `open_stacked` arms. -/
def vsOpen : List String :=
  ["open_stacked__L0", "open_stacked__L1", "open_stacked__L2", "open_stacked__L3", "open_stacked__L4",
    "open_stacked__L5", "open_stacked__L6", "open_stacked__L7", "open_stacked__L8", "open_stacked__L9",
    "open_stacked__L10"]

/-- `verify_sub`'s stream hint. -/
def vsStreamA : Atom := .hint (.witness "stream" (.heap (.n (val% «verify_sub» "stream")) 0 8192))

/-- `verify_sub`'s table logs hint. -/
def vsLogsA : Atom := .hint (.witness "table_logs" (.heap (.n (val% «verify_sub» "dims_g")) 1 6))

/-- `verify_sub`'s call of `certify_placement`. -/
def vsCpS : Stmt := .call "certify_placement" [.n (val% «verify_sub» "kappa_base"), .n (val% «verify_sub» "g_squares")] [.n (val% «verify_sub» "g_total"), .n (val% «verify_sub» "col_offsets")]

/-- `verify_sub`'s call of `verify_tables`. -/
def vsVtS : Stmt :=
  .call "verify_tables" ([545, 546, 547, 548, 549, 550, 0, 1, 254, 253, 71, 26, 4, 334, 530, 6, 552, 551, 555, 553, 25].map .n)
    ((List.range 10).map fun k => .n (556 + k))

/-- `verify_sub`'s dispatch to `open_stacked`. -/
def vsOsS : Stmt :=
  .dispatch (.n (val% «verify_sub» "size_sel")) vsOpen ([66, 1337, 1338, 1339, 1340, 1341, 1883, 268, 271, 1885, 1887].map .n)
    ((List.range 5).map fun k => .n ((val% «verify_sub» "sumcheck_target") + k))

/-- `verify_sub`'s shape. -/
noncomputable def vsShapeOk : Bool :=
  let l := (fn% «verify_sub»).body
  let j := idx% «verify_sub»
  segOk j l 0 8 && stmtAt l 8 (.atom vsStreamA) && segOk j l 9 46 && stmtAt l 55 (.atom vsLogsA) &&
    segOk j l 56 187 && stmtAt l 243 vsCpS && segOk j l 244 72 && stmtAt l 316 vsVtS && segOk j l 317 1193 &&
    stmtAt l 1510 vsOsS && noWitBlock j (l.drop 1511)

theorem vsShape_ok : vsShapeOk = true := by decide +kernel

/-- `certify_placement`'s group order hint. -/
def cpOrdA : Atom := .hint (.witness "col_group_order" (.heap (.n (val% «certify_placement» "group_order")) 0 9))

/-- `certify_placement`'s shape. -/
noncomputable def cpShapeOk : Bool :=
  let l := (fn% «certify_placement»).body
  let j := idx% «certify_placement»
  segOk j l 0 135 && stmtAt l 135 (.atom cpOrdA) && noWitBlock j (l.drop 136)

theorem cpShape_ok : cpShapeOk = true := by decide +kernel

/-- `verify_tables`' block group order hint. -/
def vtOrdA : Atom := .hint (.witness "block_group_order" (.heap (.n (val% «verify_tables» "group_order")) 0 24))

/-- `verify_tables`' round count hint. -/
def vtZcA : Atom := .hint (.witness "zc_tau_max" (.stack [.n (val% «verify_tables» "g_zc_n")]))

/-- `verify_tables`' shape. -/
noncomputable def vtShapeOk : Bool :=
  let l := (fn% «verify_tables»).body
  let j := idx% «verify_tables»
  segOk j l 0 17 && stmtAt l 17 (.atom vtOrdA) && segOk j l 18 2572 && stmtAt l 2590 (.atom vtZcA) &&
    noWitBlock j (l.drop 2591)

theorem vtShape_ok : vtShapeOk = true := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
