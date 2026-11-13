/-
  LeanVM.Guest.B1.Main.AggL25CChk

  `aggregate_claims_loop0` (a child's absorption), evaluated (by kernel evaluation), for its
  completeness.
-/

module

public import LeanVM.Guest.B1.Main.AggCLib

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- A load of the row's word `o < 13` through `.n 13` into `.n (14 + o)`. -/
def isL25RowLoad : Atom → Bool
  | .load d p o => decide (p = .n 13) && decide (d = .n (14 + o)) && decide (o < 13)
  | _ => false

/-- A load of a child's word: its public input's cells through `.n 59`, `.n 63`, its claims'
words through `.n 50`, `.n 57`. -/
def isL25WordLoad : Atom → Bool
  | .load _ p o => (decide (p = .n 59) && decide (o = 0)) || (decide (p = .n 63) && decide (o = 1)) ||
      (decide (p = .n 50) && decide (o < 24)) || (decide (p = .n 57) && decide (o < 24))
  | _ => false

/-- `aggregate_claims_loop0`'s stores: the pointer tables, then the next row's capacity and rate
cells. -/
def l25Stores : List Atom :=
  [.load (.n 50) (.n 51) 0, .load (.n 57) (.n 58) 0] ++
    (List.range 5).map (fun i => .load (.n (356 + i)) (.n 13) (13 + i)) ++
    (List.range 4).flatMap fun j =>
      [.load (.n (362 + 3 * j)) (.n 13) (18 + 2 * j), .load (.n (363 + 3 * j)) (.n 13) (19 + 2 * j)]

/-- `aggregate_claims_loop0`'s atoms but its stores. -/
noncomputable def l25A : List Atom :=
  (atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop0» default))).filter fun a =>
      decide (a ∉ l25Stores)

/-- `aggregate_claims_loop0`'s chain, on its atoms but its stores. -/
noncomputable def l25S : DupSpec := ⟨keccakBlocks l25A, packsOf l25A⟩

theorem mem_l25A {a : Atom} :
    a ∈ l25A ↔ a ∈ atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop0» default)) ∧ a ∉
        l25Stores := by
  simp [l25A]

set_option maxRecDepth 100000 in
theorem l25_stores : storesOf 8 (coreProgram.getD idx% «aggregate_claims_loop0» default).body =
    l25Stores := by
  decide +kernel

/-- **`aggregate_claims_loop0`, evaluated**: its values defined in order, its atoms but its stores
holding from
its row's and child's loads. -/
noncomputable def l25COk : Bool :=
  let fn := coreProgram.getD idx% «aggregate_claims_loop0» default
  (chk 8 fn.body).isSome && (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) &&
  l25A.all (fun a => !needsSide a || isL25RowLoad a || isL25WordLoad a) &&
  (List.range 13).all (fun o => decide (Atom.load (.n (14 + o)) (.n 13) o ∈ l25A))

/-- **`aggregate_claims_loop0`'s chain, on its atoms but its stores.** -/
noncomputable def l25DOk : Bool :=
  let A := l25A
  let P := (atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop0» default))).filter pureB
  (packsOf A).all (fun p => packIn A p.1 p.2) &&
  l25S.check A && decide (l25S.nb = 13) && rowInOk A (.n 13) (l25S.ins 0) &&
  (List.range 5).all (fun i => decide ((l25S.outs 12).getD (8 + i) default = .n (356 + i))) &&
  (List.range 4).all (fun j => decide (l25S.wB (48 + j) = 362 + 3 * j) &&
    decide (l25S.wB (48 + j) + 1 = 363 + 3 * j)) &&
  (List.range 52).all (fun w => srcOk A (l25S.wV w) (l25Src w)) &&
  monoIs P (.n 13) (.n 2) (.n 0) 13 && monoIs P (.n 59) (.n 7) (.n 0) 2 &&
  monoIs P (.n 63) (.n 7) (.n 0) 2 && monoIs P (.n 50) (.n 3) (.n 0) 24 &&
  monoIs P (.n 57) (.n 5) (.n 0) 24 && isMul P (.n 51) (.n 4) (.n 0) && isMul P (.n 58) (.n 6) (.n 0)

set_option maxRecDepth 100000 in
theorem l25c_ok : l25COk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l25d_ok : l25DOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
