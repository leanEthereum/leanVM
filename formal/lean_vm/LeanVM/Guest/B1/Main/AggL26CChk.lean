/-
  LeanVM.Guest.B1.Main.AggL26CChk

  `aggregate_claims_loop1` (a child's record: the power of `λ` and the running claim) and
  `aggregate_claims_loop2` (a child's weight), evaluated (by kernel evaluation), for their
  completeness.
-/

module

public import LeanVM.Guest.B1.Main.AggCLib
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop1»
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop2»

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-! ## `aggregate_claims_loop1` -/

/-- `aggregate_claims_loop1`'s stores: the next record's power and claim. -/
def l26Stores : List Atom := [.load (.n (val% «aggregate_claims_loop1» "s5#0")) (.n (val% «aggregate_claims_loop1» "row")) 2, .load (.n (val% «aggregate_claims_loop1» "s6#6")) (.n (val% «aggregate_claims_loop1» "row")) 3]

/-- `aggregate_claims_loop1`'s atoms but its stores. -/
noncomputable def l26A : List Atom :=
  (atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop1» default))).filter fun a =>
      decide (a ∉ l26Stores)

theorem mem_l26A {a : Atom} :
    a ∈ l26A ↔ a ∈ atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop1» default)) ∧ a ∉
        l26Stores := by
  simp [l26A]

/-- A load of `aggregate_claims_loop1`: the record's two words, the pointers to the child's claims,
their
values. -/
def isL26Load : Atom → Bool
  | .load _ p o => (decide (p = .n (val% «aggregate_claims_loop1» "row")) && decide (o < 2)) ||
      ((decide (p = .n (val% «aggregate_claims_loop1» "fresh~0")) || decide (p = .n (val% «aggregate_claims_loop1» "carried~0"))) && decide (o = 0)) ||
      ((decide (p = .n (val% «aggregate_claims_loop1» "fresh")) || decide (p = .n (val% «aggregate_claims_loop1» "carried"))) && decide (o = 23))
  | _ => false

set_option maxRecDepth 100000 in
theorem l26_stores : storesOf 7 (coreProgram.getD idx% «aggregate_claims_loop1» default).body =
    l26Stores := by
  decide +kernel

/-- **`aggregate_claims_loop1`, evaluated**: its values defined in order, its atoms but its stores
holding from
its loads, and the facts of its block on them. -/
noncomputable def l26COk : Bool :=
  let fn := coreProgram.getD idx% «aggregate_claims_loop1» default
  let A := l26A
  let P := (atomsIn (loopPre fn)).filter pureB
  (chk 7 fn.body).isSome && (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) &&
  A.all (fun a => !needsSide a || isL26Load a) &&
  isMul P (.n (val% «aggregate_claims_loop1» "row~0")) (.n (val% «aggregate_claims_loop1» "xc")) (.n (val% «aggregate_claims_loop1» "xc")) && isMul P (.n (val% «aggregate_claims_loop1» "row")) (.n (val% «aggregate_claims_loop1» "bc_chain")) (.n (val% «aggregate_claims_loop1» "row~0")) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop1» "lam_pow")) (.n (val% «aggregate_claims_loop1» "row")) 0) &&
  isMul P (.n (val% «aggregate_claims_loop1» "fresh~0")) (.n (val% «aggregate_claims_loop1» "fresh_row")) (.n (val% «aggregate_claims_loop1» "xc")) && A.any (isLoadAt (.n (val% «aggregate_claims_loop1» "fresh")) (.n (val% «aggregate_claims_loop1» "fresh~0")) 0) &&
  isMul P (.n (val% «aggregate_claims_loop1» "carried~0")) (.n (val% «aggregate_claims_loop1» "carried_row")) (.n (val% «aggregate_claims_loop1» "xc")) && A.any (isLoadAt (.n (val% «aggregate_claims_loop1» "carried")) (.n (val% «aggregate_claims_loop1» "carried~0")) 0) &&
  isMul P (.n (val% «aggregate_claims_loop1» "s5#0")) (.n (val% «aggregate_claims_loop1» "lam_pow")) (.n (val% «aggregate_claims_loop1» "lam_sq")) && A.any (isLoadAt (.n (val% «aggregate_claims_loop1» "s6#0")) (.n (val% «aggregate_claims_loop1» "row")) 1) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop1» "s6#1")) (.n (val% «aggregate_claims_loop1» "fresh")) 23) && A.any (isLoadAt (.n (val% «aggregate_claims_loop1» "s6#2")) (.n (val% «aggregate_claims_loop1» "carried")) 23) &&
  isMul P (.n (val% «aggregate_claims_loop1» "s6#3")) (.n (val% «aggregate_claims_loop1» "lam")) (.n (val% «aggregate_claims_loop1» "s6#2")) && P.any (isAddAt (.n (val% «aggregate_claims_loop1» "s6#4")) (.n (val% «aggregate_claims_loop1» "s6#1")) (.n (val% «aggregate_claims_loop1» "s6#3"))) &&
  isMul P (.n (val% «aggregate_claims_loop1» "s6#5")) (.n (val% «aggregate_claims_loop1» "lam_pow")) (.n (val% «aggregate_claims_loop1» "s6#4")) && P.any (isAddAt (.n (val% «aggregate_claims_loop1» "s6#6")) (.n (val% «aggregate_claims_loop1» "s6#0")) (.n (val% «aggregate_claims_loop1» "s6#5")))

set_option maxRecDepth 100000 in
theorem l26_shape : loopShapeF (coreProgram.getD idx% «aggregate_claims_loop1» default)
    name% «aggregate_claims_loop1» = true ∧
    (coreProgram.getD idx% «aggregate_claims_loop1» default).params.length = 7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem l26c_ok : l26COk = true := by decide +kernel

/-! ## `aggregate_claims_loop2` -/

/-- `aggregate_claims_loop2`'s store: the next weight. -/
def l27Stores : List Atom := [.load (.n (val% «aggregate_claims_loop2» "s4#6")) (.n (val% «aggregate_claims_loop2» "s4#7")) 1]

/-- `aggregate_claims_loop2`'s atoms but its store. -/
noncomputable def l27A : List Atom :=
  (atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop2» default))).filter fun a =>
      decide (a ∉ l27Stores)

theorem mem_l27A {a : Atom} :
    a ∈ l27A ↔ a ∈ atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop2» default)) ∧ a ∉
        l27Stores := by
  simp [l27A]

/-- A load of `aggregate_claims_loop2`: the pointers to the child's claims, the record's power, the
weight,
and coordinate `o < 23` of the claims' points and of `bc_point1`. -/
def isL27Load : Atom → Bool
  | .load _ p o => (decide (p = .n (val% «aggregate_claims_loop2» "fresh~0")) && decide (o = 0)) || (decide (p = .n (val% «aggregate_claims_loop2» "carried~0")) && decide (o = 0)) ||
      (decide (p = .n (val% «aggregate_claims_loop2» "row")) && decide (o = 0)) || (decide (p = .n (val% «aggregate_claims_loop2» "s4#0")) && decide (o = 0)) ||
      ((decide (p = .n (val% «aggregate_claims_loop2» "bc_point1")) || decide (p = .n (val% «aggregate_claims_loop2» "fresh")) || decide (p = .n (val% «aggregate_claims_loop2» "carried"))) && decide (o < 23))
  | _ => false

set_option maxRecDepth 100000 in
theorem l27_stores : storesOf 8 (coreProgram.getD idx% «aggregate_claims_loop2» default).body =
    l27Stores := by
  decide +kernel

/-- **`aggregate_claims_loop2`, evaluated**: its values defined in order, its atoms but its store
holding from
its loads, and the facts of its block on them. -/
noncomputable def l27COk : Bool :=
  let fn := coreProgram.getD idx% «aggregate_claims_loop2» default
  let A := l27A
  let P := (atomsIn (loopPre fn)).filter pureB
  (chk 8 fn.body).isSome && (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) &&
  A.all (fun a => !needsSide a || isL27Load a) &&
  isMul P (.n (val% «aggregate_claims_loop2» "fresh~0")) (.n (val% «aggregate_claims_loop2» "fresh_row")) (.n (val% «aggregate_claims_loop2» "xc")) && A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "fresh")) (.n (val% «aggregate_claims_loop2» "fresh~0")) 0) &&
  isMul P (.n (val% «aggregate_claims_loop2» "carried~0")) (.n (val% «aggregate_claims_loop2» "carried_row")) (.n (val% «aggregate_claims_loop2» "xc")) && A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "carried")) (.n (val% «aggregate_claims_loop2» "carried~0")) 0) &&
  eqChainOk A (.n (val% «aggregate_claims_loop2» "fresh")) (.n (val% «aggregate_claims_loop2» "bc_point1")) 23 (.n (val% «aggregate_claims_loop2» "eq_fresh@23")) && eqChainOk A (.n (val% «aggregate_claims_loop2» "carried")) (.n (val% «aggregate_claims_loop2» "bc_point1")) 23 (.n (val% «aggregate_claims_loop2» "eq_carried@23")) &&
  isMul P (.n (val% «aggregate_claims_loop2» "row~0")) (.n (val% «aggregate_claims_loop2» "xc")) (.n (val% «aggregate_claims_loop2» "xc")) && isMul P (.n (val% «aggregate_claims_loop2» "row")) (.n (val% «aggregate_claims_loop2» "bc_chain")) (.n (val% «aggregate_claims_loop2» "row~0")) &&
  isMul P (.n (val% «aggregate_claims_loop2» "s4#0")) (.n (val% «aggregate_claims_loop2» "bc_wsum")) (.n (val% «aggregate_claims_loop2» "xc")) && A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "s4#1")) (.n (val% «aggregate_claims_loop2» "s4#0")) 0) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "s4#2")) (.n (val% «aggregate_claims_loop2» "row")) 0) && isMul P (.n (val% «aggregate_claims_loop2» "s4#3")) (.n (val% «aggregate_claims_loop2» "lam")) (.n (val% «aggregate_claims_loop2» "eq_carried@23")) &&
  P.any (isAddAt (.n (val% «aggregate_claims_loop2» "s4#4")) (.n (val% «aggregate_claims_loop2» "eq_fresh@23")) (.n (val% «aggregate_claims_loop2» "s4#3"))) && isMul P (.n (val% «aggregate_claims_loop2» "s4#5")) (.n (val% «aggregate_claims_loop2» "s4#2")) (.n (val% «aggregate_claims_loop2» "s4#4")) &&
  P.any (isAddAt (.n (val% «aggregate_claims_loop2» "s4#6")) (.n (val% «aggregate_claims_loop2» "s4#1")) (.n (val% «aggregate_claims_loop2» "s4#5"))) && isMul P (.n (val% «aggregate_claims_loop2» "s4#7")) (.n (val% «aggregate_claims_loop2» "bc_wsum")) (.n (val% «aggregate_claims_loop2» "xc"))

set_option maxRecDepth 100000 in
theorem l27_shape : loopShapeF (coreProgram.getD idx% «aggregate_claims_loop2» default)
    name% «aggregate_claims_loop2» = true ∧
    (coreProgram.getD idx% «aggregate_claims_loop2» default).params.length = 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem l27c_ok : l27COk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
