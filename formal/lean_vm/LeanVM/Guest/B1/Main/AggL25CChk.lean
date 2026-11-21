/-
  LeanVM.Guest.B1.Main.AggL25CChk

  `aggregate_claims_loop0` (a child's absorption), evaluated (by kernel evaluation), for its
  completeness.
-/

module

public import LeanVM.Guest.B1.Main.AggCLib
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop0»

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- A load of the row's word `o < 13` through `.n 13` into `.n (14 + o)`. -/
def isL25RowLoad : Atom → Bool
  | .load d p o => decide (p = .n (val% «aggregate_claims_loop0» "row")) && decide (d = .n (14 + o)) && decide (o < 13)
  | _ => false

/-- A load of a child's word: its public input's cells through `.n 59`, `.n 63`, its claims'
words through `.n 50`, `.n 57`. -/
def isL25WordLoad : Atom → Bool
  | .load _ p o => (decide (p = .n (val% «aggregate_claims_loop0» "s9.u0.s1.t.s0#0")) && decide (o = 0)) || (decide (p = .n (val% «aggregate_claims_loop0» "s9.u1.s1.t.s0#0")) && decide (o = 1)) ||
      (decide (p = .n (val% «aggregate_claims_loop0» "fresh")) && decide (o < 24)) || (decide (p = .n (val% «aggregate_claims_loop0» "carried")) && decide (o < 24))
  | _ => false

/-- The `fs_pack` base of the next row's word `j < 4`: two loaded words' copies, then two zeros
bound in place. -/
def l25Last (j : ℕ) : ℕ := [362, 365, 367, 369].getD j 0

/-- `aggregate_claims_loop0`'s stores: the pointer tables, then the next row's capacity and rate
cells. -/
def l25Stores : List Atom :=
  [.load (.n (val% «aggregate_claims_loop0» "fresh")) (.n (val% «aggregate_claims_loop0» "s6#0")) 0, .load (.n (val% «aggregate_claims_loop0» "carried")) (.n (val% «aggregate_claims_loop0» "s8#0")) 0] ++
    (List.range 5).map (fun i => .load (.n ((val% «aggregate_claims_loop0» "nxt[8]@13") + i)) (.n (val% «aggregate_claims_loop0» "row")) (13 + i)) ++
    (List.range 4).flatMap fun j =>
      [.load (.n (l25Last j)) (.n (val% «aggregate_claims_loop0» "row")) (18 + 2 * j), .load (.n (l25Last j + 1)) (.n (val% «aggregate_claims_loop0» "row")) (19 + 2 * j)]

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
  (List.range 13).all (fun o => decide (Atom.load (.n ((val% «aggregate_claims_loop0» "sp[0]") + o)) (.n (val% «aggregate_claims_loop0» "row")) o ∈ l25A))

/-- **`aggregate_claims_loop0`'s chain, on its atoms but its stores.** -/
noncomputable def l25DOk : Bool :=
  let A := l25A
  let P := (atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop0» default))).filter pureB
  (packsOf A).all (fun p => packIn A p.1 p.2) &&
  l25S.check A && decide (l25S.nb = 13) && rowInOk A (.n (val% «aggregate_claims_loop0» "row")) (l25S.ins 0) &&
  (List.range 5).all (fun i => decide ((l25S.outs 12).getD (8 + i) default = .n ((val% «aggregate_claims_loop0» "nxt[8]@13") + i))) &&
  (List.range 4).all (fun j => decide (l25S.wB (48 + j) = l25Last j) &&
    decide (l25S.wB (48 + j) + 1 = l25Last j + 1)) &&
  (List.range 52).all (fun w => srcOk A (l25S.wV w) (l25Src w)) &&
  monoIs P (.n (val% «aggregate_claims_loop0» "row")) (.n (val% «aggregate_claims_loop0» "absorb")) (.n (val% «aggregate_claims_loop0» "xc")) 13 && monoIs P (.n (val% «aggregate_claims_loop0» "s9.u0.s1.t.s0#0")) (.n (val% «aggregate_claims_loop0» "child_pi")) (.n (val% «aggregate_claims_loop0» "xc")) 2 &&
  monoIs P (.n (val% «aggregate_claims_loop0» "s9.u1.s1.t.s0#0")) (.n (val% «aggregate_claims_loop0» "child_pi")) (.n (val% «aggregate_claims_loop0» "xc")) 2 && monoIs P (.n (val% «aggregate_claims_loop0» "fresh")) (.n (val% «aggregate_claims_loop0» "child_fresh")) (.n (val% «aggregate_claims_loop0» "xc")) 24 &&
  monoIs P (.n (val% «aggregate_claims_loop0» "carried")) (.n (val% «aggregate_claims_loop0» "child_carried")) (.n (val% «aggregate_claims_loop0» "xc")) 24 && isMul P (.n (val% «aggregate_claims_loop0» "s6#0")) (.n (val% «aggregate_claims_loop0» "fresh_row")) (.n (val% «aggregate_claims_loop0» "xc")) && isMul P (.n (val% «aggregate_claims_loop0» "s8#0")) (.n (val% «aggregate_claims_loop0» "carried_row")) (.n (val% «aggregate_claims_loop0» "xc"))

set_option maxRecDepth 100000 in
theorem l25c_ok : l25COk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l25d_ok : l25DOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
