/-
  LeanVM.Guest.B1.Main.AggL26CChk

  `__loop34` (a child's record: the power of `λ` and the running claim) and `__loop35` (a child's
  weight), evaluated (by kernel evaluation), for their completeness.
-/

module

public import LeanVM.Guest.B1.Main.AggCLib

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-! ## `__loop34` -/

/-- `__loop34`'s stores: the next record's power and claim. -/
def l26Stores : List Atom := [.load (.n 14) (.n 8) 2, .load (.n 21) (.n 8) 3]

/-- `__loop34`'s atoms but its stores. -/
noncomputable def l26A : List Atom :=
  (atomsIn (loopPre (coreProgram.getD 432 default))).filter fun a => decide (a ∉ l26Stores)

theorem mem_l26A {a : Atom} :
    a ∈ l26A ↔ a ∈ atomsIn (loopPre (coreProgram.getD 432 default)) ∧ a ∉ l26Stores := by
  simp [l26A]

/-- A load of `__loop34`: the record's two words, the pointers to the child's claims, their
values. -/
def isL26Load : Atom → Bool
  | .load _ p o => (decide (p = .n 8) && decide (o < 2)) ||
      ((decide (p = .n 10) || decide (p = .n 12)) && decide (o = 0)) ||
      ((decide (p = .n 11) || decide (p = .n 13)) && decide (o = 23))
  | _ => false

set_option maxRecDepth 100000 in
theorem l26_stores : storesOf 7 (coreProgram.getD 432 default).body = l26Stores := by
  decide +kernel

/-- **`__loop34`, evaluated**: its values defined in order, its atoms but its stores holding from
its loads, and the facts of its block on them. -/
noncomputable def l26COk : Bool :=
  let fn := coreProgram.getD 432 default
  let A := l26A
  let P := (atomsIn (loopPre fn)).filter pureB
  (chk 7 fn.body).isSome && (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) &&
  A.all (fun a => !needsSide a || isL26Load a) &&
  isMul P (.n 7) (.n 0) (.n 0) && isMul P (.n 8) (.n 2) (.n 7) &&
  A.any (isLoadAt (.n 9) (.n 8) 0) &&
  isMul P (.n 10) (.n 3) (.n 0) && A.any (isLoadAt (.n 11) (.n 10) 0) &&
  isMul P (.n 12) (.n 4) (.n 0) && A.any (isLoadAt (.n 13) (.n 12) 0) &&
  isMul P (.n 14) (.n 9) (.n 5) && A.any (isLoadAt (.n 15) (.n 8) 1) &&
  A.any (isLoadAt (.n 16) (.n 11) 23) && A.any (isLoadAt (.n 17) (.n 13) 23) &&
  isMul P (.n 18) (.n 6) (.n 17) && P.any (isAddAt (.n 19) (.n 16) (.n 18)) &&
  isMul P (.n 20) (.n 9) (.n 19) && P.any (isAddAt (.n 21) (.n 15) (.n 20))

set_option maxRecDepth 100000 in
theorem l26_shape : loopShapeF (coreProgram.getD 432 default) "__loop34" = true ∧
    (coreProgram.getD 432 default).params.length = 7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem l26c_ok : l26COk = true := by decide +kernel

/-! ## `__loop35` -/

/-- `__loop35`'s store: the next weight. -/
def l27Stores : List Atom := [.load (.n 179) (.n 180) 1]

/-- `__loop35`'s atoms but its store. -/
noncomputable def l27A : List Atom :=
  (atomsIn (loopPre (coreProgram.getD 434 default))).filter fun a => decide (a ∉ l27Stores)

theorem mem_l27A {a : Atom} :
    a ∈ l27A ↔ a ∈ atomsIn (loopPre (coreProgram.getD 434 default)) ∧ a ∉ l27Stores := by
  simp [l27A]

/-- A load of `__loop35`: the pointers to the child's claims, the record's power, the weight,
and coordinate `o < 23` of the claims' points and of `bc_point1`. -/
def isL27Load : Atom → Bool
  | .load _ p o => (decide (p = .n 8) && decide (o = 0)) || (decide (p = .n 10) && decide (o = 0)) ||
      (decide (p = .n 172) && decide (o = 0)) || (decide (p = .n 173) && decide (o = 0)) ||
      ((decide (p = .n 4) || decide (p = .n 9) || decide (p = .n 11)) && decide (o < 23))
  | _ => false

set_option maxRecDepth 100000 in
theorem l27_stores : storesOf 8 (coreProgram.getD 434 default).body = l27Stores := by
  decide +kernel

/-- **`__loop35`, evaluated**: its values defined in order, its atoms but its store holding from
its loads, and the facts of its block on them. -/
noncomputable def l27COk : Bool :=
  let fn := coreProgram.getD 434 default
  let A := l27A
  let P := (atomsIn (loopPre fn)).filter pureB
  (chk 8 fn.body).isSome && (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) &&
  A.all (fun a => !needsSide a || isL27Load a) &&
  isMul P (.n 8) (.n 2) (.n 0) && A.any (isLoadAt (.n 9) (.n 8) 0) &&
  isMul P (.n 10) (.n 3) (.n 0) && A.any (isLoadAt (.n 11) (.n 10) 0) &&
  eqChainOk A (.n 9) (.n 4) 23 (.n 167) && eqChainOk A (.n 11) (.n 4) 23 (.n 170) &&
  isMul P (.n 171) (.n 0) (.n 0) && isMul P (.n 172) (.n 5) (.n 171) &&
  isMul P (.n 173) (.n 6) (.n 0) && A.any (isLoadAt (.n 174) (.n 173) 0) &&
  A.any (isLoadAt (.n 175) (.n 172) 0) && isMul P (.n 176) (.n 7) (.n 170) &&
  P.any (isAddAt (.n 177) (.n 167) (.n 176)) && isMul P (.n 178) (.n 175) (.n 177) &&
  P.any (isAddAt (.n 179) (.n 174) (.n 178)) && isMul P (.n 180) (.n 6) (.n 0)

set_option maxRecDepth 100000 in
theorem l27_shape : loopShapeF (coreProgram.getD 434 default) "__loop35" = true ∧
    (coreProgram.getD 434 default).params.length = 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem l27c_ok : l27COk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
