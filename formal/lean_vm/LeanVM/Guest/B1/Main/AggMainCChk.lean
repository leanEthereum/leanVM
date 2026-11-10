/-
  LeanVM.Guest.B1.Main.AggMainCChk

  `aggregate_claims`' body, evaluated (by kernel evaluation), for its completeness.
-/

module

public import LeanVM.Guest.B1.Main.AggCMath

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `aggregate_claims`' stores: the first absorbing row (the seed, the packed count and zeros),
the first record of `bc_chain` (the power `1`, the claim `0`), `bc_point1`, the first weight `0`,
the claim at `defer_stmt`. -/
def aggStores : List Atom :=
  (List.range 5).map (fun i => .load (.n (10 + i)) (.n 33) i) ++
    (List.range 4).flatMap (fun j => [.load (.n (15 + 3 * j)) (.n 33) (5 + 2 * j),
      .load (.n (16 + 3 * j)) (.n 33) (6 + 2 * j)]) ++
    [.load (.n 99) (.n 98) 0, .load (.n 100) (.n 98) 1] ++
    (List.range 23).map (fun k => .load (.n (119 + 3 * k)) (.n 116) k) ++ [.load (.n 189) (.n 188) 0] ++
    (List.range 23).map (fun k => .load (.n (196 + k)) (.n 4) k) ++ [.load (.n 7) (.n 4) 23]

/-- `aggregate_claims`' loads: the last absorbing row, the nonce, the last record's claim, the
sumcheck's point (for `bc_point1`), the last weight, the sumcheck's point (for `defer_stmt`). -/
def aggLoads : List Atom :=
  (List.range 13).map (fun k => .load (.n (43 + k)) (.n 42) k) ++ [.load (.n 73) (.n 6) 0] ++
    [.load (.n 106) (.n 105) 1] ++
    (List.range 23).map (fun k => .load (.n (118 + 3 * k)) (.n 107) k) ++
    [.load (.n 194) (.n 193) 0] ++ (List.range 23).map (fun k => .load (.n (196 + k)) (.n 107) k)

/-- `aggregate_claims`' hints: the buffers and `bc_star_hint`. -/
def aggHintsA : List Atom :=
  [.hint (.alloc (.n 6) 47), .hint (.witness "bc_star_hint" (.stack [.n 7])),
    .hint (.allocDyn (.n 8) (.n 0)), .hint (.allocDyn (.n 9) (.n 0)),
    .hint (.allocDyn (.n 33) (.n 32)), .hint (.allocDyn (.n 98) (.n 97)),
    .hint (.alloc (.n 107) 23), .hint (.alloc (.n 116) 23), .hint (.allocDyn (.n 188) (.n 187))]

/-- `aggregate_claims`' packs (`fs_pack` of the count and three zeros). -/
def aggPacks : List (V × ℕ) := [(.n 0, 15), (.n 17, 18), (.n 20, 21), (.n 23, 24)]

/-- `aggregate_claims`' calls. -/
def aggCalls : List Stmt :=
  [.callIf (.n 35) "__loop33" [.n 36, .n 0, .n 33, .n 2, .n 8, .n 3, .n 9, .n 1],
    .call "grind_check__L2" [.n 82, .n 5] [],
    .callIf (.n 102) "__loop34" [.n 103, .n 0, .n 98, .n 8, .n 9, .n 94, .n 81],
    .call "batch_sumcheck__L23" [.n 89, .n 90, .n 91, .n 92, .n 93, .n 109, .n 106, .n 107, .n 5]
      [.n 110, .n 111, .n 112, .n 113, .n 114, .n 115],
    .callIf (.n 191) "__loop35" [.n 192, .n 0, .n 8, .n 9, .n 116, .n 98, .n 188, .n 81]]

/-- `aggregate_claims`' atoms but its stores. -/
noncomputable def aggA : List Atom := (atomsIn aggP).filter fun a => decide (a ∉ aggStores)

theorem mem_aggA {a : Atom} : a ∈ aggA ↔ a ∈ atomsIn aggP ∧ a ∉ aggStores := by
  simp [aggA]

set_option maxRecDepth 100000 in
theorem agg_stores : storesOf 6 (Fn.body Data.core33) = aggStores := by decide +kernel

/-- **`aggregate_claims`' body, evaluated**: its values defined in order, its atoms but its stores
holding from its loads and the final check, its statements atoms or its calls, the sums of
`bc_point1` and the products pure. -/
noncomputable def aggCOk : Bool :=
  let A := atomsIn aggP
  let P := A.filter pureB
  (chk 6 (Fn.body Data.core33)).isSome &&
  aggA.all (fun a => !needsSide a || decide (a ∈ aggLoads) || decide (a = .assertEq (.n 115) (.n 195))) &&
  aggPacks.all (fun p => packIn aggA p.1 p.2) &&
  aggLoads.all (fun a => decide (a ∈ aggA)) && aggHintsA.all (fun a => decide (a ∈ A)) &&
  aggP.all (fun s => match s with | .atom _ => true | _ => aggCalls.any (stmtEqb s)) &&
  aggCalls.all (fun c => aggP.any (stmtEqb · c)) &&
  monoIs P (.n 42) (.n 33) (.n 0) 13 && monoIs P (.n 105) (.n 98) (.n 0) 2 &&
  isMul P (.n 193) (.n 188) (.n 0) && isMul P (.n 195) (.n 7) (.n 194) && genMulOk P (.n 109) (.n 6) &&
  isMul P (.n 94) (.n 81) (.n 81) &&
  (List.range 23).all (fun k => P.any (isAddAt (.n (119 + 3 * k)) (.n (117 + 3 * k)) (.n (118 + 3 * k))))

set_option maxRecDepth 100000 in
theorem aggc_ok : aggCOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
