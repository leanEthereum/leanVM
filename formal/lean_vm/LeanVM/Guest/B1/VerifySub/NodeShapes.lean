/-
  LeanVM.Guest.B1.VerifySub.NodeShapes

  Where `verify_sub`, `certify_placement` and `verify_tables` pop: their bodies' witness hints and noisy calls by position, every block between them mute in `vsMuteSet` (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Common.PopsSeg
public import LeanVM.Guest.B1.VerifySub.MuteChk
public import LeanVM.Guest.B1.Common.Basic

/-!
# The bodies' shapes

`segOk l a n`: the block of `n` statements from position `a` of `l` cannot return and is mute in `vsMuteSet`. `stmtAt l a s`: statement `a` of `l` is `s`.

* `verify_sub` (`vsShape_ok`): the stream's hint at `8`, the table logs' at `55`, `certify_placement` at `243`, `verify_tables` at `333`, the `open_stacked` dispatch at `1544`;
* `certify_placement` (`cpShape_ok`): the group order's hint at `135`;
* `verify_tables` (`vtShape_ok`): the block group order's hint at `17`, `zc_tau_max`'s at `2591`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1

@[expose] public section

/-- The block of `n` statements from `a` cannot return and is mute. -/
def segOk (l : List Stmt) (a n : ℕ) : Bool :=
  Stmt.noRetList ((l.drop a).take n) && Stmt.muteList vsMuteSet.contains ((l.drop a).take n)

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
def vsStreamA : Atom := .hint (.witness "stream" (.heap (.n 25) 0 8192))

/-- `verify_sub`'s table logs hint. -/
def vsLogsA : Atom := .hint (.witness "table_logs" (.heap (.n 71) 1 6))

/-- `verify_sub`'s call of `certify_placement`. -/
def vsCpS : Stmt := .call "certify_placement" [.n 83, .n 4] [.n 274, .n 275]

/-- `verify_sub`'s call of `verify_tables`. -/
def vsVtS : Stmt :=
  .call "verify_tables" ([562, 563, 564, 565, 566, 567, 0, 1, 254, 253, 71, 26, 4, 335, 559, 6, 569, 568, 572, 570].map .n)
    ((List.range 10).map fun k => .n (573 + k))

/-- `verify_sub`'s dispatch to `open_stacked`. -/
def vsOsS : Stmt :=
  .dispatch (.n 278) vsOpen ([66, 1370, 1371, 1372, 1373, 1374, 1917, 268, 271, 1919, 1921].map .n)
    ((List.range 5).map fun k => .n (1922 + k))

/-- `verify_sub`'s shape. -/
noncomputable def vsShapeOk : Bool :=
  let l := (fn% «verify_sub»).body
  segOk l 0 8 && stmtAt l 8 (.atom vsStreamA) && segOk l 9 46 && stmtAt l 55 (.atom vsLogsA) &&
    segOk l 56 187 && stmtAt l 243 vsCpS && segOk l 244 89 && stmtAt l 333 vsVtS && segOk l 334 1210 &&
    stmtAt l 1544 vsOsS && Stmt.muteList vsMuteSet.contains (l.drop 1545)

theorem vsShape_ok : vsShapeOk = true := by decide +kernel

/-- `certify_placement`'s group order hint. -/
def cpOrdA : Atom := .hint (.witness "col_group_order" (.heap (.n 136) 0 9))

/-- `certify_placement`'s shape. -/
noncomputable def cpShapeOk : Bool :=
  let l := (fn% «certify_placement»).body
  segOk l 0 135 && stmtAt l 135 (.atom cpOrdA) && Stmt.muteList vsMuteSet.contains (l.drop 136)

theorem cpShape_ok : cpShapeOk = true := by decide +kernel

/-- `verify_tables`' block group order hint. -/
def vtOrdA : Atom := .hint (.witness "block_group_order" (.heap (.n 36) 0 24))

/-- `verify_tables`' round count hint. -/
def vtZcA : Atom := .hint (.witness "zc_tau_max" (.stack [.n 2544]))

/-- `verify_tables`' shape. -/
noncomputable def vtShapeOk : Bool :=
  let l := (fn% «verify_tables»).body
  segOk l 0 17 && stmtAt l 17 (.atom vtOrdA) && segOk l 18 2573 && stmtAt l 2591 (.atom vtZcA) &&
    Stmt.muteList vsMuteSet.contains (l.drop 2592)

theorem vtShape_ok : vtShapeOk = true := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
